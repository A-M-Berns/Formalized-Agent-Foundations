# Spike: how hard is *Communication & Trust* (Demski, 2025)?

**Paper.** Abram Demski, *Communication & Trust*, 16 September 2025, 15 pp. Formalizes
Yudkowsky's "decision-determination" fairness criterion and proves two self-trust results
for Wei Dai's UDT, using communication between agent-instances as a release valve for
self-modification pressure. Builds on Critch's boundaries, Cartesian Frames, and Finite
Factored Sets — the last two of which this repo already has complete.

**Verdict, in one line: this is an easy paper to formalize and a hard paper to formalize
*honestly*, and the second is the only thing worth planning around.**

It is 30 numbered nodes, of which **26 are definitions and assumptions and 3 are
results** whose proofs run 5–20 lines each. There is essentially no proof difficulty.
What there is instead: a stack of prose definitions with acknowledged notational "puns",
several concrete defects (below — one of them proved in Lean), and **not a single
constructed model anywhere in the paper**. By this repo's own standard — *"it is only
honest if its hypotheses are satisfiable and its constructed objects are real"* — the
witness construction *is* the project, not the theorems.

Artifacts:

- `CommunicationTrust/Spike.lean` — 164 lines, **compiles, zero `sorry`**, axioms clean.
  Settles the §4 substrate against Mathlib's `Setoid` and proves the Theorem 1 defect.
- `CommunicationTrust/spike-build.sh` — compiles against the parent checkout's oleans.

---

## 1. Defects found

I read the paper for correctness before estimating, because with a 26:3
definition-to-theorem ratio that is where the information is. Six findings; the first
three are substantive.

### 1.1 Theorem 1's printed conclusion is a tautology

Verbatim:

> `m(Π*(ȯö,ö) = aö) > min_{a'ö ∈ Aö} m(Π*(ȯö,ö) = a'ö)`
> `⟹  E[U | Π*(ȯö,ö) = aö] ≤ max_{a'ö ∈ Aö} E[U | Π*(ȯö,ö) = a'ö]`

Since `aö ∈ Aö`, the max on the right ranges over a set containing `aö`. The consequent
therefore holds **with no hypotheses at all**, for any real-valued function whatsoever.
This is `printed_conclusion_is_vacuous` in the spike file — a one-line proof taking none
of the paper's three conditions.

The proof establishes something real and stronger: `ca(aö)` is *minimally modifying* by
Definition 18(1), so the max should range over the minimally modifying actions.
`IntendedConclusion` in the spike file states that version, and a two-element
counter-model shows it is genuinely non-tautological. The English gloss —
"non-minimally-modifying actions can never be strictly preferred" — matches the intended
statement, not the printed one.

### 1.2 Lemma 1 is stated at a strength its own proof does not deliver

Lemma 1 as printed: `E[U | Π*(ȯö,ö) = aö] = E[U | Π*(ȯö,ö) = ca(aö)]`.

Its proof decomposes `E[U | Π*(ȯö,ö) = ca(aö), Π̈ = R]` — *with* the conditioning — and
matches it against the left side via Definition 18(2), which is itself stated with
`Π̈ ≡ R`. So the proof establishes

> `E[U | Π* = aö] = E[U | Π* = ca(aö), Π̈ = R]`

and never removes the conditioning. Theorem 1's proof then reads "By (2) and the lemma,
`E[U|Π* = aö] ≤ E[U|Π* = ca(aö), Π̈ = R]`. **By (3)**, this proves the desired result" —
i.e. it uses the *conditioned* form and spends condition (3), `P(Π̈ = R) = 1`, to discharge
it. The printed Lemma 1 is inconsistent with both its own proof and its only consumer.
Fix: state Lemma 1 with the `Π̈ = R` conditioning.

### 1.3 Theorem 2's proof contains an unsound step, and proves a different statement

Two separate problems.

**The unsound step.** The chain reaches
`arg max_{äö} Σ_k E[U | …, k] · P(k | …)` and then says: "By (2),
`P(rô'−ö | Π*(ȯö,ö) = (ȧö, äö))` is constant in `äö`, so" — and drops the weights.
Weights being *independent of the maximization variable* does not license dropping them:
`arg max_ä Σ_k w_k f_k(ä) ≠ arg max_ä Σ_k f_k(ä)` in general. Take `w = (1, 0)`,
`f₁ = (0, 1)`, `f₂ = (10, 0)`: weighted picks the second action, unweighted the first.

The conclusion probably survives, because the *next* step invokes stability (Definition
19), which gives **pointwise** dominance across the sum — and pointwise dominance
maximizes weighted and unweighted sums alike. So the fix is to delete the weight-dropping
step rather than to repair it. But as printed the inference is invalid.

**Statement/proof mismatch.** Theorem 2 concludes, for a *fixed* internal action `ȧö` on
both sides, that the recommended external action strictly beats every other. The proof
instead works with `max_{ȧö}` and then says "let `ȧö` denote the internal instance action
which is best given the best external instance action" — establishing a claim about one
particular `ȧö`. Since Definition 19 quantifies over all `ȧö`, the stated `∀ȧö` form looks
directly reachable; the `max` detour is what opens the gap.

### 1.4 A symbol collision

Definition 15: "The variable **P** represents the possible forced external policies."
`P` is also the agent's probability distribution, used on nearly every page including
inside Definition 16's own `m(e) = P(dom(qǒ) ≠ ∅ | e)`. Formalizing forces a rename.

### 1.5 Typos

- **Definition 15**: `qǒ(ö) = pö(ôö)` — should be `pö(ǒö)`. `pö : Ǒö ⇀ Ä` takes a
  side-channel value, not a semantic observation. (Compare Definition 14's `rô(ö) = sö(ôö)`,
  from which this was evidently copied.)
- **Definition 14**: `sö : ÔÖ ⇀ Ä` — should be `Ôö`.
- **Definition 20**: writes `rȯ` where Definition 14 defines `rô`.
- **Definition 18**: alternates `ca(aö)` and `caȯö(aö)`; and uses `Π̈ ≡ R` where the rest
  of the paper writes `Π̈ = R`.

### 1.6 A vacuity risk that a formalization must resolve

Footnote 17 stipulates `E(U|S) = −1` when `P(S) = 0`, with `U` bounded in `[0,1]`. So a
probability-zero conditioning event is *strictly worse than any real outcome*. Now note
that Theorem 2 assumes `P(Π̈ = R) = 1`. If deviating from the recommendation is a
probability-zero event under `P`, then `E[U | Π*(ȯö,ö) = (ȧö, äö)] = −1` for every
non-recommended `äö`, and **Theorem 2's strict inequality holds by the convention rather
than by stability** — making it far weaker than it reads.

I have not established that this happens; I am flagging that nothing in the paper rules
it out, and that it is exactly the "oversold statement" pattern this repo's scheduled
adversarial audit exists to catch. Settling it requires a model, which brings us to the
main point.

## 2. The dominant risk is vacuity, not difficulty

The paper constructs **no** decision structure. Theorem 1 carries three hypotheses
(decision-determination, communicative alternatives, `P(Π̈=R)=1`); Theorem 2 carries four
(`P(Π̈=R)=1`, internally-driven recommendations, stability with probability one, plus
recommendation/modification exclusivity for the addendum) on top of a *concrete decision
structure*, which is itself Assumptions 1–4 plus Definitions 12–16. That is a long
conjunction, and nobody has exhibited a point in it.

Examples 1–3 (Coordinated Buttons, Memory, Third Button) are prose scenarios, not models.
Turning Coordinated Buttons into an actual `Ω`, partitions `I, B, E, Ȯ, Ö, Ȧ, Ä, Ô, Ǒ`,
factorizations satisfying Assumptions 1–4, a `P` and a `U`, and then checking
decision-determination and the existence of communicative alternatives — that is the real
work in this project, and it simultaneously validates every definition. It is also the
only thing that can answer §1.6.

**So I would invert the usual order: build the witness first, alongside the definitions,
and state the theorems last.** If the assumptions turn out not to be jointly satisfiable,
that is a more valuable result than a green build, and better to learn in week one.

## 3. The substrate: mostly good news

### What the spike settled

**Order convention (this one matters).** Demski's Definition 1 — `X ≤ Y` iff every part of
`X` sits inside a part of `Y`, i.e. `X` refines `Y` — is **Mathlib's `≤` on `Setoid Ω`**,
and his meet `∧` (coarsest common refinement) is **Mathlib's `⊓`**. Both proved
mechanically (`refines_iff_le`, `classes_inf`).

This is the *opposite* of the FFS situation, where Garrabrant writes `⋁` for the common
refinement and `FiniteFactoredSets/` carries a standing `dd:order-flip` disclosure that
"the paper's order glyphs are inverted relative to Mathlib's". Anyone porting intuitions
from the FFS development to this paper will get it backwards on day one. Worth a
prominent note.

**Definition 5 (partition factorization).** The paper asserts the relationship to the meet
in prose; `factorsAs_iff` proves it:

> `X` factors as `(Y, Z)` **iff** `X = Y ⊓ Z` **and** every `y ∈ Y`, `z ∈ Z` have
> `y ∩ z ≠ ∅`.

That is the clean working form and what a real development should be stated over. The
parenthetical in Definition 5 ("this implies `y ∩ z` is nonempty for all `y, z`") is also
correct, and the reason is that partition parts are nonempty — proved as
`FactorsAs.nonempty_inter`.

**Encoding.** `Setoid Ω` with `Setoid.classes` for parts. Mathlib supplies the complete
lattice, `classes_inj`, `rel_iff_exists_classes`, `empty_notMem_classes`; FFS already
exercises all of it in this repo. No new infrastructure needed for §4.1–4.2.

### What the spike did *not* settle — probe these next

- **Definition 6** (factoring into a *family*, via dependent choice functions
  `c : (i : I) → Xi` with `m(c) = ⋂_i c(i)`). This is the general form everything in
  §6 uses, and it is where I would expect dependent-type friction — it is the analogue of
  the index-family problem in the Factored Space Models paper. Unprobed. **Probe it first.**
- **Definition 7** (function decomposition): `f(x) = ⋂_i fi([[x]]_{Xi})` where the `Xi` are
  subvariables of `X` but need not be factors. The paper does not argue that this
  intersection is a part of `Y`, or that `f` is well-defined. May need a side condition.
- **Definition 4** (restriction map) is used at a type it does not fit: Definition 5's
  `m : Y × Z → X` has a *product* domain, not a partition. Two senses of the term; pick
  one and disclose.

### The puns

The paper is explicit that it "freely puns" between objects and the variables that index
them. Each pun is a formalization obligation:

| Pun | Paper's status | Obligation |
|---|---|---|
| `Π†` as functions vs. subvariable of `DB` | constructible | must construct |
| `Π̈` as functions vs. subvariable of `D_{I,B}` | constructible | must construct |
| `Π*` as functions vs. variable | **assumed** | disclosed hypothesis |
| `R` as variable vs. set of functions | implicit | must construct or assume |
| `P` (forced policies) as variable vs. functions | implicit | must construct or assume |
| `O` vs `Ȯ × Ö`, `A` vs `Ȧ × Ä` | assumed to factor | follows from Definition 5 |
| equations-as-events (`Π†(o) = a`) | notational | a coercion to `Set Ω` |

Discharging the "constructible" ones is not optional: leaving them as assumptions
silently weakens the trust surface in exactly the way this repo's rule 4(c) is about.

### Probability

The paper asks for a σ-algebra containing all parts of every partition of interest, but
every actual computation is a finite sum (`Σ_{π̈ ∈ Π̈}`, sums over messages). **Recommend a
finite `Ω`**: faithful to all usage, matches the `FiniteFactoredSets/Probability.lean`
pattern, and avoids measure theory outright. Disclose as a modeling choice
(`dd:finite-omega`). Also needed: conditional probability under zero-probability
conditioning (Definition 12's identity is between conditional probabilities, and the
paper's `−1` convention covers only conditional *expectations*, not probabilities).

## 4. A practical blocker: provenance

The file is `27_Communication_Trust.pdf` — LaTeX + hyperref, 16 Sep 2025, no title/author
metadata. **No arXiv ID, no DOI, no venue string anywhere in the PDF.** That is a problem
for this repo's machinery specifically: `scripts/papers.py` wants a registered source, and
every existing paper here has a node checker that recomputes printed numbers *from the
committed `.tex`*, fail-closed. Without the source we would be down to a hand-maintained
node table with no mechanical check — a real weakening of the standard the other four
formalizations meet.

Two asks before committing effort, both for Anson:

1. **Get the `.tex` from Demski**, or a stable arXiv posting.
2. **Confirm the paper is settled.** Given §1's findings, several statements will likely
   change. Formalizing against a moving preprint burns the provenance work twice. Sending
   the errata list first is probably worth more to the author than the formalization is,
   and costs a day.

## 5. Estimate

| Tranche | Nodes | Lines | Risk |
|---|---|---|---|
| §4 substrate (Defs 1–7) | 7 | 600–900 | low — partly done |
| §5 agents (Assumptions 1–4, Defs 8–12) | 9 | 500–800 | low, definitional |
| §6 instances & communication (Defs 13–16) | 4 | 300–400 | low, definitional |
| §7–§8 results (Def 17–20, Lemma 1, Thms 1–2) | 7 | 300–500 | low *if* the definitions are right |
| Witness models (Examples 1–3) | 3 | 1000–2000 | **high — this is the project** |
| **Total** | **30** | **2700–4600** | |

Call it **35–50% of the FiniteFactoredSets effort** by volume, with an inverted risk
profile: near-zero proof risk, high definitional risk, and a single dominant unknown
(does a model exist?).

## 6. Recommendation

Worth doing, and a good fit for this repo — it sits directly downstream of two completed
formalizations, and the class of defect I found in a few hours is exactly what this
project is for. But sequence it deliberately:

1. **Send Demski the §1 errata list.** Cheap, high value, and avoids formalizing a moving
   target.
2. **Probe Definition 6** (family factorization via dependent choice functions). It is the
   one unresolved substrate question and it gates §6.
3. **Build Coordinated Buttons as a concrete decision structure** before stating any
   theorem. If that succeeds, the rest is bookkeeping. If it fails, you have the finding.
4. Only then state Lemma 1 and Theorems 1–2 — in their *intended* forms, with the printed
   forms recorded in a `paper-errata.md` alongside `CartesianFrames/notes/paper-errata.md`,
   which is the established precedent here for "the printed proof is the thing that is
   wrong".
