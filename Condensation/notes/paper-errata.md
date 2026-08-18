# Condensation (Eisenstat, July 2025) — paper errata noticed during formalization

Curated during the Lean formalization in `Condensation/`. Each entry cites the committed
source `Condensation/notes/condensation-25-07.txt` (the `pdftotext -layout` extraction of
`Condensation/notes/condensation-25-07.pdf`), by line number where useful.

**What this file is for.** Read it before concluding that a Lean statement or proof
diverges from the printed one: in several places below the printed text is the thing that
is wrong, and a formalizer's first instinct on a mismatch is to assume the Lean is wrong.
Each entry names its **location** (node, and which part of it), what is **printed**, and
what is **meant**. Entries also say whether the defect was re-confirmed against the
committed extraction or is carried forward unverified from the feasibility spike
(`Condensation/SPIKE-REPORT.md`); as of this writing all of them are confirmed.

**Not an erratum: the missing ligatures.** `pdftotext` drops the `fi` and `ff` ligatures,
so the extraction reads `Denition`, `nite`, `dierent`, `sucient`, `signicant`. That is a
*tool* artifact of the extractor, not a defect of the paper — the PDF itself is fine. Do
not log one here. (It is also why the node checker's regex reads `De.?nition`.)

Keep the numbered-entry shape below — `N. **headline naming the node**` followed by the
detail. The trust-surface generator parses Cartesian Frames' errata headlines exactly that
way (`^\s*(\d+)\.\s+\*\*(.+?)\*\*`, pulling node ids out of the headline), and a
Condensation-specific reader will do the same; a headline that does not name its node
cannot be attached to it on the generated page.

---

1. **Lemma 4.5, statement of clause (2), and Corollary 4.6, statement: `P I` printed for
   `P⁺ I`.** Clause (2) of Lemma 4.5 reads "For all `i ∈ I` and `A ∈ PI` such that `i ∈ A`"
   (L637), and Corollary 4.6 reads "whenever we have `i ∈ A ∈ PI`" (L660). In both places
   the intended index set is the **nonempty** power set `P⁺ I` of Definition 2.2, which is
   what the surrounding statements quantify over — clause (1) of the same lemma writes
   `A ∈ P⁺ I`, as does the `(⇐=)` half of its proof. **Confirmed in the committed
   extraction**, and confirmed to be a real omission rather than an extraction artifact:
   the extractor does render this paper's superscript `+` (it lands on its own line,
   e.g. L635 for clause (1) and L649 for the proof), and no such line accompanies L637 or
   L660. Benign in effect — for `i ∈ A` the set `A` is nonempty anyway, so the two readings
   coincide — but the Lean statements use `PPlus I` throughout (`dd:pplus`), and a reader
   comparing them to the printed clause should not read the difference as a divergence.

2. **Lemma 4.5, proof: cites "Corollary 2.5", but 2.5 is a Proposition.** The `(=⇒)` half
   reads "Hence, using Corollary 2.5 `Y_∋i`, and a fortiori `Y_A` for any `A` containing
   `i`, is almost everywhere equal to a function of `X_i`" (L647). The paper prints
   **Proposition** 2.5 (L195), the determinism bridge `H(Y | X) = 0 ⟹ Y = f(X)` a.e.; that
   is the result being used, and there is no Corollary 2.5 in the paper (§2 contains
   Definitions 2.1–2.4 and Proposition 2.5, and nothing else). A pure citation slip; the
   argument is correct. **Confirmed in the committed extraction.** Worth recording because
   the node checker validates the *kind* of a cited node, so `Paper node: Corollary 2.5`
   would fail even though it is what the paper's own prose says.

3. **Corollary 4.6, proof: cites only Proposition 4.2, but the argument also needs
   Lemma 4.5.** The whole proof is "Using Proposition 4.2, this follows immediately."
   (L662). Proposition 4.2 supplies the chain `σ_L(A) ≥ χ_L(A) ≥ H(Y_∩A) ≥ H(X_A)` (4.6),
   which — combined with the hypothesis that `L` perfectly condenses `M`, i.e.
   `χ_L(A) = H(X_A)` — gives `H(Y_∩A) = H(X_A)`. That is exactly clause (1) of Lemma 4.5;
   the conclusion asserted by the corollary, the existence of the functions `f^i_A` with
   `Y_A = f^i_A(X_i)` almost everywhere, is clause (2), and it is Lemma 4.5's `(1) =⇒ (2)`
   that gets from one to the other. Proposition 4.2 alone does not. The corollary is true
   as stated; only the citation is incomplete. **Confirmed in the committed extraction.**

4. **Theorem 4.9, condition (B2): the "almost everywhere" of (A2) is dropped.** (A2) reads
   "the latent variable `Y_A` is a function of `X_i` **almost everywhere**" (L741–742),
   while the parallel (B2) reads "the latent variable `Y_A` is a function of `X_i`."
   (L748–749) with no qualifier. The intended reading is the a.e. one: the whole
   development is a.e.-based (Definition 2.1's fifth convention, Definition 3.2's condition
   on `π^* X_i`), the proof of `(B1) ⟺ (B2)` goes through the same Proposition 2.5 route as
   (A2), and the everywhere reading is not implied by (B1) — a perfect condensation can be
   modified on a null set. **Confirmed in the committed extraction.** A formalization has to
   pick one, and this one picks a.e. (`dd:ae-function`), so the Lean (B2) will read
   `AEFunctionOf` where the printed (B2) reads as if it meant `FunctionOf`. That difference
   is this erratum, not a divergence.

5. **Theorem 4.15, proof: `F_i` is used but never defined, and the induction is asserted
   rather than set up.** The proof says it will "apply Lemma 4.14 repeatedly, using
   induction", states the lemma's hypotheses for two upward-closed `F, G ⊆ P⁺I`, and then
   concludes from the display
   `(4.62)  ⋂_{i∈A} F_i = {B : B ⊇ A}` (L1173)
   that `Y_A` is a function of `Z_{⊇A}` almost everywhere. **`F_i` occurs exactly once in
   the paper, at (4.62), and is never defined** — a grep of the extraction for `Fi ` returns
   that line and no other. It evidently means `F_i = {B ∈ P⁺I : i ∈ B}`, which is
   upward-closed and does satisfy (4.62). What is missing is more than a symbol: the actual
   induction — intersect the `|A|` upward-closed sets `F_i` pairwise, discharging Lemma
   4.14's conditional-independence side condition at each step via Proposition 4.10 — is
   never written down, and (4.62) is the only place the induction is specified.
   **Confirmed in the committed extraction.** This is the most substantive entry in this
   file: formalizing Theorem 4.15 means supplying the induction, not transcribing it, and
   the node should be budgeted well above what its half-page of printed proof suggests.

6. **Theorem 5.8, proof: "(5.14)" printed for "(5.13)".** The proof opens "We will first
   prove (5.14)", establishes (5.15) by induction over the intersection tree, specializes
   it to the root, and then says "Specializing this equation to the root, we establish
   (5.14). Equation (5.14) follows by a term-by-term comparison." (L1465). The second
   occurrence should read **(5.13)** — the *inequality*, which is what the following
   term-by-term comparison (5.17)–(5.20) actually derives from the just-proved exact
   identity (5.14). **Confirmed in the committed extraction.**

7. **Corollary 5.10, equation (5.24): "`n − 1`" printed for "`k − 1`".** (5.24) reads
   `G = {C ⊆ I : C contains at least all but n − 1 elements of A}` (L1520–1522), but the
   corollary has no parameter `n`: its parameter is `k`, and `F` is "the collection of all
   those `C ⊆ A` with cardinality `k`" (L1517). The `n` is left over from the §5.2
   motivating prose, which says the same thing with `n`: "if `F` consists of all
   `n`-element subsets of `A`, then … `G` consists of all sets that contain at least all but
   `n − 1` elements of `A`" (L1371–1372). With `k`, the claim is right: `C` meets every
   `k`-element subset of `A` exactly when `|A \ C| ≤ k − 1`. **Confirmed in the committed
   extraction**, together with its source in the §5.2 prose.

8. **Corollary 5.10, statement: `k` is used one sentence before it is bound.** *(Newly
   found during this pass; not in the spike report.)* The hypothesis reads "Suppose that
   `ϱ_Y(C) ≤ α` for all `C ∈ P⁺I` with cardinality `k`. Now, let `A` be an element of `P⁺I`
   and `k ∈ N`, and define `F` to be the collection of all those `C ⊆ A` with cardinality
   `k`." (L1515–1517). `k` is quantified over in the second sentence but already used in
   the first; the intended statement introduces `A ∈ P⁺I` and `k ∈ N` first and *then*
   imposes the uniform bound `ϱ_Y(C) ≤ α` on all `C` of cardinality `k`. Purely an ordering
   slip, but it has to be resolved to state the corollary in Lean at all. A related
   loose end in the same sentence, recorded here rather than as its own entry: `F` is
   required to be a subset of `P⁺I`, so the degenerate `k = 0` (which would give
   `F = {∅} ⊄ P⁺I`) is excluded, and `k > |A|` gives `F = ∅`. The paper does not say which
   of these it means to exclude. **Confirmed in the committed extraction.** For what
   actually happens at those two corners — the tree hypothesis becomes *unsatisfiable*, so
   (5.25) is vacuous rather than trivially true — see entry 14.

9. **Definition 5.6 versus Theorem 5.8 and Corollaries 5.9, 5.10: the intersection tree's
   label function is renamed from `ℓ` to `I`, colliding with the index set and with the
   mutual-information operator.** *(Newly found during this pass; not in the spike report.)*
   Definition 5.6 introduces an intersection tree as a triple `(V, E, ℓ)` and writes its
   labels `ℓ(u) = ℓ(v) ∩ ℓ(w)` (L1326–1344), and Proposition 5.7 keeps `ℓ` (L1346–1350).
   Theorem 5.8 then writes "let `T = (V, E, I)` be an intersection tree" (L1398) and uses
   `I(v)` for the label throughout — as do the §5.2 prose and Corollaries 5.9 and 5.10
   (`intersections ({L(v), R(v)}, I(v))_{v∈N}`). In those same statements `I` is also the
   index set of the random variable family (`(X_i)_{i∈I}`, `P⁺I`), and inside the displayed
   bounds `I` is also the mutual-information operator: (5.13) contains
   `I(Z_{L(v)} ; Z_{R(v)} | Z_{I(v)})`, in which the outer `I` and the subscripted `I` are
   different things. The intended reading is that `I(·)` in §5.2–§5.3 is Definition 5.6's
   `ℓ`. **Confirmed in the committed extraction** that the *symbol changes in the paper*
   and not in the extractor: the extractor reproduces `ℓ` faithfully wherever the paper
   uses it (L1327, L1333, L1336, L1340, L1347–1349), and renders the §5.2–§5.3 label
   function as `I` (L1398, and every `Z_{I(v)}` in §5.2–§5.3).
   **Not determined:** whether the printed glyph in §5.2–§5.3 is an italic `I` or a
   calligraphic `ℐ` — both extract as `I` — so the collision may be visual-only in the PDF.
   Either way the formalization cannot reuse the letter, and `dd:tree` computes the label
   from the tree structure instead of carrying a named labelling function.

10. **Definition 4.12: nothing ties `π̃₁` to `π̃₂`, yet Theorem 4.15 needs them to agree.**
    *(Found while formalizing §4's amalgamation.)* Definition 4.12 asks for "two latent
    variable models `L̃₁` and `L̃₂`, both of which have underlying probability space `Λ₀`"
    together with morphisms `ρₖ : L̃ₖ → Lₖ` of the forms (4.44)/(4.45). A latent variable
    model carries its *own* map to `Ω` (Definition 3.2), so the definition as printed
    supplies two maps `π̃₁, π̃₂ : Λ₀ → Ω` and says nothing relating them. The commuting
    square (4.43) of Definition 4.11 — which *is* the relation — is stated for an
    amalgamation of a cospan of bare probability spaces, and Definition 4.12 does not
    restate it. In the construction of Lemma 4.13 the two agree on the nose, by (4.51).
    Theorem 4.15's proof needs them to agree at least almost everywhere: the step "`Y_A` is
    a.e. a function of `X_i`, and `X_i` is a.e. a function of `Z_∋i`, hence `Y_A` is a.e. a
    function of `Z_∋i`" composes a dependence witnessed through `π̃₁` with one witnessed
    through `π̃₂`, which is only legal when the two maps agree a.e. The Lean rendering
    therefore carries the a.e. commutation as an explicit field, `LatentAmalgamation.comm`
    (`∀ᵐ l ∂P₀, π₁ l = π₂ l`), and this entry records that the field is *added*, not read
    off the printed clause. It is not a strengthening in substance: the paper's own
    construction satisfies it, and without it Definition 4.12 does not support the theorem
    that consumes it.

    **What clause (3) does *not* supply, corrected 2026-08-17 (R2-F12/F20).** An earlier
    reading of this entry took clause (3) to also relate `Lₖ.π ∘ ρₖ` to `π̃ₖ`, and the Lean
    structure carried two extra fields `ρ₁_π`/`ρ₂_π` saying so. That is not in Definition
    4.12. Clause (3)'s `ρₖ : L̃ₖ → Lₖ` are morphisms in the sense of **Definition 3.5**,
    which is a morphism of the underlying *random variable* models and imposes exactly two
    conditions — `ρₖ` probability preserving, and `fⱼ(X_{ι(j)}) = ρₖ^* Yⱼ` a.e. with
    `fⱼ = id` here. The paper never defines a morphism of *latent* variable models, and so
    never asks for compatibility with the maps to `Ω`. The fields were deleted; what
    survives of clause (3) is `ρₖ_pres` and `ρₖ_Y`, and `comm` (this entry) is the only
    added field. The derived lemma `LatentAmalgamation.comm_ρ`, which said the square
    (4.43) commutes a.e. inside Definition 4.12, went with them: it was provable only from
    the deleted fields, and it is not a consequence of the printed definition.

11. **Example 4.1, equations (4.4) and (4.5): false at `A = ∅`.** *(Found while
    constructing the example.)* Example 4.1's second latent variable model `L₂` puts all of
    `M`'s information into the single top latent `Z_I` and makes every other latent
    constant; (4.4) then reads `σ_{L₂}(A) = H(Z_I) = H(X_I)` and (4.5) reads
    `χ_{L₂}(A) = H(X_I)`. Both are stated "for any `A`", and Proposition 4.2 — which these
    equations are illustrating — does quantify over all `A ⊆ I` including `A = ∅`. At
    `A = ∅` the index family `{B : B ∩ A ≠ ∅}` is empty, so both scores are the empty sum
    `0`, while the right-hand side is `H(X_I)`, which is nonzero for any non-degenerate `M`.
    The intended hypothesis is `A ≠ ∅`, i.e. `A ∈ P⁺I`, which is what the sentence
    introducing `L₂` is about. The Lean statements (`Condensation.Example41.L₂_simpleScore`,
    `.L₂_condScore`) therefore carry an explicit `A.Nonempty` hypothesis. Harmless in the
    paper's own use — every consumer of (4.4)–(4.5) has `A` nonempty — but it cannot be
    transcribed as printed.

12. **Theorem 5.8: the `Z`-side contribution condition is used but not stated as a
    hypothesis.** *(Found while formalizing §5.)* Theorem 5.8 is stated for "an
    amalgamation of two latent variable models" and then, at (5.18), uses that each `X_i`
    is almost everywhere a function of `Z_∋i` — Definition 3.2's contribution condition for
    the *second* model. That is legitimate, because Definition 4.12 makes `L̃₂` a latent
    variable model for `M` and so carries the condition; but the theorem's own statement
    lists no hypothesis about `Z` beyond it being "the" second family, and a reader
    checking (5.13) against the statement will not find where (5.18) is licensed. Recorded
    because the Lean statement drops the hypothesis for exactly this reason: it quantifies
    over `LatentAmalgamation L₁ L₂`, whose field `contributes₂` supplies it. Nothing is
    lost, but the licence comes from Definition 4.12 rather than from Theorem 5.8.

13. **Definition 5.6: the "parents" of a vertex are its children under the usual
    convention.** *(Found while formalizing §5.)* Definition 5.6's intersection tree is a
    directed rooted tree in which edges point *towards* the root, so the vertices it calls
    the parents `v, w` of an internal vertex `u` — the ones whose labels are intersected to
    give `ℓ(u) = ℓ(v) ∩ ℓ(w)` — are what the inductive-tree convention (and most of graph
    theory) calls the *children* of `u`, and the paper's "ancestors of `v`" are the
    vertices of the subtree above `v`. Not an error, and the paper's convention is
    internally consistent, but it inverts the reading a formalizer will bring to it and
    caused one wrong first draft here. `dd:tree` renders the tree as an inductive binary
    tree whose `node l r` has `l`, `r` as its *children*; those are Definition 5.6's
    parents.

14. **Theorem 5.8 and Corollaries 5.9, 5.10: at `F = ∅` (equivalently `k > |A|` in
    Corollary 5.10, and `k = 0` under the reading that admits it) the tree hypothesis is
    unsatisfiable, so the statements are vacuous — in the paper, not only in the Lean.**
    *(Found during the round-2 audit of §5; the Lean already documents it in
    `Condensation/Quantitative.lean`, and this entry records that it is a property of the
    printed statement.)* Theorem 5.8 requires an intersection tree `T` whose label function
    "restricts to a bijection between the leaves of `T` and the set of sets
    `{C ∈ P⁺I : B ∩ C ≠ ∅}` ranging over `B ∈ F`" (L1398–1402). Definition 5.6(1) says
    `(V, E)` is a directed binary tree with a **root** to which every vertex has a unique
    directed path; such a tree is nonempty and therefore has at least one leaf (the root
    itself, if the tree is a single vertex). So when `F = ∅` the right-hand side of the
    required bijection is empty while the left-hand side is not, and no such `T` exists.
    The hypothesis cannot be discharged, and Theorem 5.8, Corollary 5.9 and Corollary
    5.10's (5.25) are all vacuously true there.

    This is worth recording for two reasons. First, it is *not* what entry 8's
    "`k > |A|` gives `F = ∅` and hence `G = P⁺I`" suggests: `G = P⁺I` would make the
    conclusion cheap but the statement still contentful, whereas in fact the *hypothesis*
    fails and the statement says nothing at all. Second, it is why the Lean
    `Condensation.condEntropy_jointAbove_le_choose` (5.25) needs no `1 ≤ k` hypothesis
    (R2-F21): the degenerate `k` is already excluded by the tree hypothesis, so adding
    `hk` would be dead weight rather than a faithfulness fix. `Condensation.polar_kSubsets`
    (5.24) keeps `1 ≤ k`, because there it is load-bearing — (5.24) is an identity of
    index families with no tree in sight.

15. **Lemma 4.14 as printed is false: nothing constrains the ranges of `X`, `Y₁`, `Y₂`, and
    without the paper's own countable-discrete convention on one of them the lemma has a
    counterexample.** *(Found at M2, 2026-08-18, by trying to prove the round-2 statement;
    the ruling of the same date restored one binder that R2-F01/R2-F23 had stripped. The
    *mechanism* below was corrected on 2026-08-18 after a round-3 audit — see "the
    mechanism, corrected".)* Lemma 4.14 hypothesises only that the variables live on a
    countable discrete probability space and that "C has discrete range"; the ranges of
    `X`, `Y₁`, `Y₂` are unconstrained. With the trivial σ-algebra on those ranges, the
    conditional-independence hypothesis becomes vacuous and the two functional-dependence
    hypotheses become trivially satisfiable, while the conclusion still constrains `X`.

    Machine-checked refutation of the literal Lean transcription (`.harness`-archived
    scratch, also recorded in `Condensation/Comparison.lean`'s header): Ω = Bool uniform,
    U = Unit (C constant), S = T₁ = T₂ = a two-point type with the trivial σ-algebra ⊥,
    X = Y₁ = Y₂ = id — every hypothesis holds, the conclusion forces id to be a.e.
    constant.

    **The mechanism, corrected.** An earlier version of this entry attributed the
    counterexample to `X`'s range failing to separate points. That is not what does the
    work, and the difference decides which repairs are available.
    `ProbabilityTheory.CondIndepFun Y₁ Y₂ C μ` **never mentions `S`, the range of `X`, at
    all** — it is a statement about the σ-algebras generated by `Y₁`, `Y₂` and `C` — so the
    vacuity cannot come from `S`. It comes from `T₁` and `T₂`, the ranges of `Y₁` and `Y₂`:
    with the trivial σ-algebra `⊥` on them, `MeasurableSpace.comap Yₖ ⊥ = ⊥` and the
    conditional independence holds trivially, for any variables whatsoever. `S` at `⊥` is a
    separate matter: it is what makes the two `AEFunctionOf` hypotheses satisfiable
    (trivially), since every map into a `⊥`-space is measurable and so `Prod.snd` witnesses
    both dependences. The conclusion `AEFunctionOf C X μ` is a real constraint either way.

    **Two independent minimal repairs, and the printed statement needs exactly one of
    them.**
    (i) Require a `MeasurableSingletonClass` on `S`. Informally, this is what makes the
    argument's step "`X`'s level sets lie a.e. in `σ(C, Y₁) ∩ σ(C, Y₂)`" meaningful.
    (ii) Require `MeasurableSingletonClass` on `T₁` and on `T₂`. This removes the vacuity at
    its source, and it is the repair the *printed proof* implicitly uses.
    Both are licensed by the paper's §2 standing conventions ("our probability spaces are
    countable and discrete", stated just before Definition 2.4), so neither adds anything to
    what the paper means — only to what it prints.

    **The Lean carries (i).** `Condensation.aeFunctionOf_of_condIndepFun` has
    `[MeasurableSingletonClass S]` on `X`'s range and nothing more; `T₁`, `T₂` need only
    measurable-space structure. The binder is free at every call site, since `X` is always a
    model variable and `RVModel` carries `singR`.

    **Strength: separating points, not countability.** What is needed of `X`'s range is that
    it *separate points* — a `MeasurableSingletonClass`. It is **not** needed that the range
    be countable discrete, and there is no `Countable S` binder anywhere in the Lean
    statement. An earlier version of this entry said "X's range must be countable discrete";
    that overstated the repair.

16. **Proposition 4.10, equation (4.39): the right-hand containment is printed as `⊆ I_A`
    where `⊆ I_A ∪ S_A` is meant, which makes the display self-contradictory.** *(Found
    during the round-3 audit of §4.)* In the proof of `(1 ⟹ 2)` the paper fixes, for each
    `A ∈ G − F`, "`I_A ⊆ P⁺I` … the set of all such sets incomparable with `A`, and
    `S_A ⊆ P⁺I` … the set of strict supersets of `A`" (L887–888), and then displays

    > `(4.39)              SA ⊆ F ∪ {B ∈ G − F | B ≺ A} ⊆ IA` (L891)
    > `                    SA ⊆ (F ∩ G) ∪ {B ∈ G − F | B ≺ A} ⊆ IA ,` (L892)

    Both lines chain to `S_A ⊆ I_A`. But `S_A ∩ I_A = ∅` by construction — a strict superset
    of `A` is comparable to `A`, hence not incomparable to it — so each line is
    self-contradictory whenever `S_A ≠ ∅`, i.e. for every `A` other than the top element
    `I` itself. It is also not rescued by the left-hand containment being loose: `S_A` is
    genuinely a subset of the middle set (see below), so the two containments really do
    compose.

    **What is meant: `I_A ∪ S_A` on the right.** The middle set is the conditioning family
    the chain rule (4.38) hands the argument, `W = F ∪ {B ∈ G − F : B ≺ A}`, and what the
    proof needs of it is a *sandwich*, `S_A ⊆ W ⊆ I_A ∪ S_A`, so that conditioning on `Y_W`
    gives the same conditional entropy as conditioning on `Y_{S_A}` alone. Both halves are
    true as meant. Left: if `C ⊋ A` then `C ∈ G` by upward closure of `G`, so either
    `C ∈ F` or `C ∈ G − F` with `C ≺ A` (the order `⪯` of the paragraph before (4.38) puts
    supersets first). Right: `B ∈ F` cannot satisfy `B ⊆ A`, since `A ∉ F` and `F` is upward
    closed; and `B ∈ G − F` with `B ≺ A` cannot satisfy `B ⊊ A`, since that would give
    `A ≺ B`. So every element of `W` is incomparable to `A` or a strict superset of it.

    That the intended reading is `I_A ∪ S_A` is settled by the paper itself: at the parallel
    step (4.35) it states the very same sandwich, correctly, in prose — "the set
    `{C | C ≺ B}` contains all sets `C ∈ P⁺I` which are strict supersets of `B`. Further,
    all its elements that are not strict supersets of `B` are inclusion-incomparable to `B`"
    (L847–849), which is `S_B ⊆ {C | C ≺ B} ⊆ I_B ∪ S_B` word for word. The `∪ S_A` is
    dropped only when the same fact is put into symbols at (4.39).

    **What the Lean does.** `Condensation.RVModel.condEntropy_jointOn_eq_of_condIndepFun`
    (`Condensation/ChainRule.lean`) carries the intended, correct version: it takes
    `hind : CondIndepFun X (N.jointOn S₁) (N.jointOn S₂) N.P` together with `h₂ : S₂ ⊆ W`
    and `hW : W ⊆ S₁ ∪ S₂`, and concludes
    `H[X | N.jointOn W] = H[X | N.jointOn S₂]` — instantiated at
    `S₁ = Condensation.incomparable A` and `S₂ = Condensation.strictAbove A.toFinset`, so
    the sandwich is literally `S_A ⊆ W ⊆ I_A ∪ S_A`. The
    right-hand inclusion is discharged by
    `Condensation.pred_subset_incomparable_union_strictAbove`, whose own docstring cites
    (4.35) and "the right-hand inclusion of (4.39)". So the Lean was written against the
    intended reading from the start; this entry records that the printed one cannot be
    transcribed. **Confirmed in the committed extraction** (L887–892).

17. **Definition 5.6: the intersection tree is never required to be finite or
    well-founded, though Theorem 5.8 sums over its vertices.** *(Found by the final blind
    audits, 2026-08-18; R4-F02.)* Definition 5.6(1) asks that "`(V, E)` is a directed binary
    tree ; every vertex either has no parents (and so is a *leaf* ) or exactly two parents
    (and so is *internal* ), and there is one vertex, the *root*, to which every vertex has
    a unique directed path" (L1330–1332), and nothing else in the paper constrains the tree:
    a grep of the extraction for `tree` returns L1324, L1326, L1330, L1346, L1349, L1398,
    L1420, L1496, L1518, and the word "finite" modifies it at none of them. Unique paths
    *to* the root bound each vertex's descent, not the tree's height, so the full infinite
    binary tree — every vertex internal, no leaves — satisfies (1) as printed. But
    Theorem 5.8's conclusions are finite sums over the tree: `Σ_{v∈L}` and `Σ_{v∈N}` in
    `(5.14)  H(Y_⊇A | Z_G) = [Σ_{v∈L} H(Y_⊇A | Z_{I(v)})] − [Σ_{v∈N} H(Y_⊇A |
    Z_{L(v)∪R(v)})] + [Σ_{v∈N} I(Z_{L(v)} ; Z_{R(v)} ; Y_⊇A | Z_{I(v)})]` (L1408–1415), and
    `Σ_{v∈N}` in (5.13) (L1403–1406). **Confirmed in the committed extraction.**

    **The leaf-bijection hypothesis does not supply it.** Theorem 5.8 requires `I` to
    restrict to a bijection between the leaves and `{C ∈ P⁺I : B ∩ C ≠ ∅}` over `B ∈ F`
    (L1398–1402), and `I` is finite, so the *leaf* set is finite. That does not bound the
    internal vertices: a root with one leaf parent and one leafless infinite full binary
    parent has exactly one leaf and infinitely many internal vertices, so `Σ_{v∈N}` is still
    an infinite sum. That the paper means well-founded is clear from Proposition 5.7, whose
    conclusion — `ℓ` "assigns to each internal vertex the meet of all the labels of the
    leaves which are its ancestors" (L1349–1350) — is ill-defined at an internal vertex with
    no leaf ancestors, and whose proof is the single word "Induction." (L1351).

    **Interaction with entry 14.** Entry 14 argues that at `F = ∅` no admissible tree exists
    because "such a tree is nonempty and therefore has at least one leaf". That step is
    licensed only by the finiteness this entry says is not printed — a leafless infinite
    tree satisfies Definition 5.6(1) and satisfies the `F = ∅` bijection vacuously. Entry
    14's conclusion stands under the intended reading; this entry records that the reading
    has to be supplied.

    **What the Lean does.** It supplies the reading structurally, and now discloses it as a
    reading rather than as a neutral encoding. `Condensation.ITree`
    (`Condensation/Quantitative.lean`) is an inductive binary tree (`leaf` / `node l r`),
    hence finite, so `T.leaves` and `T.intersections` are `List`s and both sums are literally
    finite (`dd:tree`). The disclosure is written in `Quantitative.lean` (module docstring
    and the `ITree` docstring), `Condensation.lean`'s glossary, `README.md`'s `dd:tree` row
    and `notes/roadmap.md`'s; the four must stay in agreement.

18. **Proposition 2.5, proof: the conditional measure `P(· | X = x)` is called a Dirac
    measure in `G(Ω)`; it is its pushforward under `Y` that is Dirac.** The proof reads
    "Everywhere on the preimage `X⁻¹A`, we can dene the conditional probability
    distribution `P (· | X = x)`. From the denition of conditional entropy, each such
    probability distribution is a Dirac measure in `G (Ω)` for almost every `x ∈ R_X`"
    (L202–204). `G(Ω)` is Definition 2.4's space of probability measures **on `Ω`**
    (L189–193), so as printed the claim is that `P(· | X = x)` is a point mass on `Ω`. That
    is false in general and is not what `H(Y | X) = 0` gives: the hypothesis determines `Y`
    from `X`, not `ω` from `X` — with `X` and `Y` both constant, `P(· | X = x) = P`, which is
    Dirac only if `Ω` is a point. What the definition of conditional entropy actually yields,
    from `0 = H(Y | X) = Σ_x P(X = x)·H(Y | X ← x)`, is that `H(Y | X ← x) = 0` for a.e. `x`,
    i.e. that the pushforward `Y_* P(· | X = x)` is a Dirac measure in `G(R_Y)`. That is
    exactly what (2.5), `Y = f̃(X)` a.e., needs. **Confirmed in the committed extraction.**
    Worth recording because `Condensation/Probability.lean`'s Definition 2.4 docstring quotes
    this sentence when justifying the `ProbabilityMeasure Ω` carrier: the quotation is
    faithful, but the sentence it quotes is wrong about *which* space the Dirac lives in, and
    the docstring now says so. The Lean endpoints
    (`Condensation.aeFunctionOf_of_condEntropy_eq_zero` and its converse) are stated in terms
    of `AEFunctionOf` and conditional entropy and never form the Dirac measure at all, so
    nothing in the formalization inherits the slip.

19. **Lemma 4.5, proof of `(⇐=)`: "picking any `i ∈ A`" — a single `i` cannot witness all of
    `Y_∩A`.** The half reads "For any `A ∈ P⁺I`, we have `H (Y_∩A ) ≥ H (X_A )` by
    Proposition 4.2. Further, picking any `i ∈ A`, the random variable `Y_∩A` is almost
    everywhere equal to a measurable function of `X_i`, and therefore to a measurable
    function of `X_A`" (L650–652). `Y_∩A` is the family `(Y_B : B ∈ P⁺I, B ∩ A ≠ ∅)` (L308),
    and clause (2) supplies `Y_B = f^i_B(X_i)` only when `i ∈ B`. So each `B ∈ contrib A`
    needs its **own** witness `i ∈ A ∩ B`, and no single `i` serves them all: at `A = {1,2}`
    and `B = {2}` the latent `Y_{2}` belongs to `Y_∩A` but is constrained only through `X_2`,
    so `i = 1` fails. The conclusion is unaffected — every `B ∈ contrib A` meets `A`, so each
    `Y_B` is a.e. a function of some `X_i` with `i ∈ A`, hence of `X_A`, which is all (4.14)
    and (4.15) use. **Confirmed in the committed extraction.** The Lean proof of
    `Condensation.LatentModel.perfect_entropy_iff_aeFunctionOf` therefore routes through
    `X_A` directly rather than through any one `X_i`, and a reader comparing it to the
    printed step should read the difference as this erratum rather than as a divergence.

20. **Lemma 4.13, proof: the sentence introducing (4.53) writes `P₂(· | π₁ = ω)` for
    `P₂(· | π₂ = ω)`.** The sentence reads "we can dene the conditional probabilities
    `ω ↦ P₁ (· | π₁ = ω)` and `ω ↦ P₂ (· | π₁ = ω)`, taking values in the spaces of measures
    `G (Λ₁)` and `G (Λ₂)`, for almost all `ω ∈ Ω`" (L1022–1023). The second must be
    `P₂(· | π₂ = ω)`: `π₁` is a map out of `Λ₁` and is not defined on `Λ₂`, and the same
    sentence says the conditional takes values in `G(Λ₂)`. The slip is confined to the prose
    — the displays get it right at (4.53) itself, `∫_Ω [P₁ (· | π₁ = ω)] × [P₂ (· | π₂ = ω)]
    (E) dP_Ω` (L1026–1027), and again at (4.54) (L1032), (4.55) (L1043, L1047) and L1059.
    **Confirmed in the committed extraction**, and confirmed not to be an extraction
    artifact: the extractor renders the subscripts of `π₁`/`π₂` correctly on every
    surrounding line. Benign for the formalization —
    `Condensation.Amalgamation.canonical` is built from the displays, not the prose.

21. **The discussion preceding Theorem 5.8: `Y_∩B` printed where `Y_⊇A` is meant, in the
    reading of (5.13)'s first family of terms.** *(Soft finding — see the caveat below.)*
    The passage reads "Starting on the right-hand side, we will have two kinds of terms. The
    terms of the form `H (Y_⊇A | X_B )` being small is an approximate form of `Y_∩B` being a
    function of `X_B` almost everywhere, assuming that `A ∩ B ≠ ∅`, and that would be a
    consequence of perfect condensation." (L1358–1361). The term displayed is
    `H(Y_⊇A | X_B)`, so its smallness is an approximate form of **`Y_⊇A`** being a function
    of `X_B`, not of `Y_∩B`. The two are not interchangeable: when `A ∩ B ≠ ∅` we have
    `{C : C ⊇ A} ⊆ {C : C ∩ B ≠ ∅}`, so `Y_∩B` is the strictly *larger* family and "`Y_∩B` is
    a function of `X_B`" is strictly stronger — a small `H(Y_⊇A | X_B)` does not approximate
    it. The tell that `Y_⊇A` is meant is the clause "assuming that `A ∩ B ≠ ∅`": under
    perfect condensation "`Y_∩B` is a function of `X_B`" holds by Corollary 4.6 with **no**
    hypothesis on `A`, and the hypothesis is needed only to get from that to the `Y_⊇A`
    statement. **Confirmed in the committed extraction** (L1358–1361).

    **Caveat, stated adversarially.** A charitable reader can take the author to be
    deliberately naming the *stronger sufficient condition* that perfect condensation
    supplies, in which case the defect is not the subscript but the phrase "is an approximate
    form of", which then states the implication backwards. Either way something in the
    sentence is not right, but this entry is softer than the others in the file and is
    recorded with that qualification rather than as a flat misprint. Note also that the
    passage belongs to the discussion *preceding* Theorem 5.8, not to Definition 5.6.
    Nothing in the Lean depends on it: it is motivating prose, and the corresponding formal
    step is `Condensation.condEntropy_jointContrib_le_pullbackJoint`.

22. **Corollary 5.9, proof: (5.22) is attributed to "the denition of the ordered Markov
    condition" (Definition 4.8), but it needs Proposition 4.10's upward-closed
    characterization.** The proof's last line is "The second form follows from the denition
    of the ordered Markov condition." (L1509), where the second form is
    `(5.22)  H (Y_⊇A | Z_G ) ≤ Σ_{B∈F} ϱ_Y (B)` (L1504) — (5.21) with every
    `I(Z_{L(v)} ; Z_{R(v)} | Z_{I(v)})` dropped. Those terms vanish exactly when `Z_{L(v)}`
    and `Z_{R(v)}` are conditionally independent given `Z_{I(v)}`, for the **upward-closed**
    label sets of Theorem 5.8's tree, which "is an intersection tree on the lattice of
    upward-closed subsets of `P⁺I`" (L1398) with `I(v) = L(v) ∩ R(v)`. That is clause (2) of
    Proposition 4.10 — "For any two upward-closed sets `F, G ⊆ P⁺I`, the random variables
    `Y_F` and `Y_G` are independent conditional on `Y_{F∩G}`" (L872–873) — whereas
    Definition 4.8, which is clause (1), constrains a single `A` against its incomparables
    conditional on `Y_⊋A` (L729–732). Getting from (1) to (2) is the chain-rule argument
    (4.38)–(4.40), the one entry 16 is about; it is not a reading-off of the definition. The
    paper states the same step correctly elsewhere: the §5.2 discussion says the term "being
    small is an approximate form of the statement that `Z_{L(v)}` and `Z_{R(v)}` are
    independent given `Z_{I(v)}`, **which follows from Proposition 4.10**" (L1363–1365).
    **Confirmed in the committed extraction.** The Lean matches the intended route:
    `Condensation.condEntropy_jointAbove_le_reconScore_of_orderedMarkov`
    (`Condensation/Quantitative.lean`) kills the internal terms with
    `(Am.rv₂.orderedMarkov_iff).mp hmarkov q₁ q₂ hq₁ hq₂` — Proposition 4.10, `(1) ⟹ (2)` —
    and carries the tree's `hupper : T.LabelsIn {s | IsUpperSet s}` for exactly this step,
    which (5.14) does not need. This is why (5.22) was the last §5 endpoint to become
    axiom-clean: it waited on Proposition 4.10's proof, not on Definition 4.8.

---

**One candidate was investigated and REFUTED, and is recorded here so that it is not
re-raised.** A blind auditor reported that "the prose after Proposition 4.7 reverses the
perfect / simply-perfect implication". It does not. The sentence is "Corollary 4.6 tells us
something about perfect, and hence simply-perfect, condensations." (L717–718), and the claim
it makes is about the *scope of Corollary 4.6* — the corollary is stated for perfect
condensations and therefore also applies to simply-perfect ones, an inference licensed by
the true direction simply-perfect ⇒ perfect
(`Condensation.LatentModel.PerfectlyCondenses.of_simply`). The reading "perfect
condensations, which are hence simply-perfect" is grammatically available and would be
false, but it is also vacuous as a remark, so it is not what the sentence is doing.
Ambiguous English, not a reversed implication. Nothing else in §4 states an implication in
the wrong direction: L740–751 keep (A1) ⇒ (A3) straight, and L626's "so L simply-perfectly
condenses M" is correct, since (4.11) computes the *simple* score.
