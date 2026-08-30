# Lean traps met in this development

Traps that cost real time here, kept because they recur and because none of them is
discoverable from an error message. This is the single home for them: `KNOWLEDGE.md` carries
the settled design decisions and the correspondence table, and points here for pitfalls.

## Tooling and toolchain

- **`lake env lean` on a just-edited module silently uses the stale olean.** It also
  auto-binds implicits, so a signature error can elaborate cleanly. It is not a gate:
  rebuild the specific module target with `lake build` before trusting a scratch check
  against it.
- **`.git/info/exclude` swallows `Scratch*.lean`.** A spike file named `Scratch_Foo.lean`
  is neither tracked nor shown by `git status`, so `git add -A` of "the spike plus its
  writeup" commits the writeup alone, citing a file that is not in the repository. Run
  `git check-ignore -v` before citing a new file as evidence.
- **A witness-file edit blocks everyone downstream of it in a shared worktree.** Parallel
  sessions in one tree see each other's syntax errors; poll and do unaffected work rather
  than assuming your own edit broke the build.

## Parsing and elaboration

- **`stacks` is a reserved token, not an identifier.** Mathlib's `@[stacks]` attribute
  (`Mathlib/Tactic/CrossRefAttribute.lean`) declares `"stacks"` as a syntax atom, so a
  field or definition of that name fails to parse with `unexpected token 'stacks'`,
  reported at the *following* line. Recognize the class: a parse error naming a token you
  took for an ordinary identifier, in a file that parses fine without Mathlib imported.
- **`#assert_fields` compares field *names* only**, despite its wording. A boundary
  structure's field *type* can change under a green freeze. Read it as a rename guard, not
  a premise-smuggling guard.
- **`Nat.sqrt` whnf-loops in deep `Primrec` / `PolyFueled` work.** Fix is a scoped
  `attribute [local irreducible] Nat.sqrt`.
- **`Nat.Partrec.Code.evaln` does not reduce under `decide`** (the `Decidable` instance
  gets stuck); use `simp [evaln]` for concrete evaluations. Likewise `native_decide`
  misreports on goals with free variables in the token-decode area, and
  `simp [strategyOfTokens, …]` sticks on the dependent `match hdecode :` — use bare `rfl`.

## Proof shapes

- **Mirror-and-push beats `split_ifs` for automaton agreement.** Word-level mirrors of a
  scalar branch cascade prove agreement in one `simp only [apply_ite List.length, …]`:
  pushing `.length` through the cascade makes both sides syntactically identical. Copying
  the ℕ-level `split_ifs <;> omega` shape (which needs `maxHeartbeats 2000000` there) times
  out at the word level. Shorter *and* cheaper.
- **`Function.update`-shaped phase lemmas at a concrete bundled machine block `rw`/`simp`
  but not `exact`/`refine`.** The `DecidableEq` instances agree; what diverges is the type
  argument — the goal's unreduced projection versus the literal in a hand-written update
  nest. Defeq but not syntactically equal, so rewriting does not fire while term-mode
  application does. Do not rewrite working update-shaped proofs to "fix" this.

## Statements that look stronger than they are

- **Check how a per-step bound compounds, not only that it holds.** A multiplicative
  per-step state bound compounds to `k^L` over a fold and is not polynomial. This caught
  three would-be-wrong lemmas in one session: an emitter copying its incoming flag rather
  than re-emitting a literal; a nested-pair state bounded projection-by-projection instead
  of jointly; and a fold hypothesis quantified over all token words rather than the slot
  shape.
- **Try to instantiate an interface hypothesis before publishing it.** Every interface
  correction in the freeze-transport work came from a client failing to discharge a
  hypothesis that looked reasonable in the abstract.
- **`Complexity.FP` has `selectHead` but no `tail`.** A digit handed over as a flat
  three-bit word can be branched on once and no further; hand it over as three separately
  headable one-bit slots.
- **Degenerate instantiations prove nothing.** `MachinePolyEC` over `Fin 0` holds for every
  `f`, and an empty freeze table (`S = ∅`) inhabits any freeze certificate while forcing
  `P = P'`. Neither is evidence that a machine statement has content.

## Definitional shapes that fight `simp`

- **Prefer `match j with | none => a | some _ => b` to `fun j => if j = none then a else b`.**
  The `ite` form defeats `simp` on the projections — `(if none = none then [] else …) = []`
  is left open as a split — while the match form makes both projections `rfl`.
- **`Option.none_bind` does not exist** in the installed Mathlib; `none.bind f = none` is
  definitional, so close it with `rfl` after rewriting.
- **Doc comments on `example` are legal** in this toolchain. Do not refactor away from them
  on the assumption that they error.

## Auditing names

- **`rg -r` is the *replace* flag, not recursive.** `rg -rn "foo"` rewrites every match to
  `n` in the displayed output, which once made `EfficientPrefixPatch.preserves_ec` display
  as a dangling name. Use `rg -n --fixed-strings` when auditing declaration names.
- **`lint_paper_labels.py` requires every `theorem` to carry a paper label.** A supporting
  result promoted from `lemma` to `theorem` for emphasis breaks the gate.
- **`lakefile.lean` sets `autoImplicit := false` package-wide, but `lake env lean` does not
  apply package `leanOptions`.** Auto-implicit over-generalization is therefore a per-file
  scratch-checking hazard that a real `lake build` would have caught — one more reason the
  entry above says `lake env lean` is not a gate.

## Traps recorded in the 2026-08-28 write-out / source-encoding round

- **A failed elaboration makes `#print axioms` report `sorryAx` on *downstream* declarations
  in the same file.** Check the error list and `grep -rn sorry` before treating a build-log
  `sorryAx` as genuine.
- **`unRpn`/`unRpnTokens` case analysis:** `simp only [unRpn, List.length_cons] at h` *first*,
  then `rw [unRpnTokens] at h`; never `simp only [..., unRpnTokens]` (unfolds the recursive
  tail; `split_ifs` explodes). Match `[] / [t] / t :: c' :: r`.
- **`have h : PolyFueled _ f := …` fails with "don't know how to synthesize placeholder for
  c"** — the have-type elaborates before its proof. Write `∃ c : Code, PolyFueled c f` and
  `refine ⟨_, proof⟩`, or `obtain ⟨c, h⟩ : ∃ c, PolyFueled c f := by refine ⟨_, (…).of_eq (fun z => ?_)⟩`.
- **Inside `namespace Nat.Partrec.Code`, bare `Primrec.const/pair/comp` resolve to
  `Nat.Primrec.*`.** Write `_root_.Primrec`, `_root_.Primrec2`, `_root_.PrimrecPred`,
  `_root_.Computable`; `open _root_.Primrec` collides with `Code`'s constructors.
- **Foundation name traps:** `Semantics.Not.models_not` (a class field, `@[simp]`);
  `Entailment.by_axm h` takes only the membership proof; `WeakerThan.trans` needs explicit
  `(S := …) (T := …)`; `ISigma1.Delta1` needs
  `import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1` explicitly, and the
  failure is a bare "failed to synthesize Theory.Delta1 ISigma1".
- **Don't `rw [thyName]` to unfold a theory built as `insert σ 𝗜𝚺₁`**; use
  `inferInstanceAs (Theory.Delta1 (insert σ 𝗜𝚺₁))` and state provability lemmas at the
  unfolded sentence. `[ℕ ⊧* T] → T.SoundOn F` (`Arithmetic/Basic/Model.lean:99`) gives
  `SoundOnHierarchy 𝚺 1` *and* `Consistent` for free once every axiom is true in ℕ.
- **`split_ifs <;> omega` is unsafe when a guard is decidably false on literals** — it leaves
  `h : False ⊢ 5 = 1`. Discharge guards explicitly: `rw [if_neg (by omega), …, if_pos (by decide)]`.
  `simp_all` loops on `1 = 2*(n+1)`.
- **`pow_mul : a ^ (m * n) = (a ^ m) ^ n`** — to turn `4 ^ (k * 2)` into `16 ^ k`, `rw [mul_comm, pow_mul]`.
- **Mathlib `Nat.Partrec.Code.eval` halting proofs:** `(Code.eval Code.zero x).Dom` is `trivial`,
  not `simp [Code.eval]`; divergence of `rfind' succ`: `rw [CodeHalts, Part.dom_iff_mem] at h;
  obtain ⟨v, hv⟩ := h; simp only [Code.eval, Nat.unpaired, Part.mem_map_iff, Nat.mem_rfind] at hv;
  obtain ⟨a, ⟨h1, -⟩, -⟩ := hv; simp at h1`.
- **`Nat.ofDigits_lt_base_pow_length` / `Nat.ofDigits_div_pow_eq_ofDigits_drop`** are not
  reachable through `Framework/DigitArith` — `import Mathlib.Data.Nat.Digits.Defs` explicitly.
- **The `models_haltingSchema_iff` transport** is exactly
  `simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using (codeOfREPred_spec hp (x := z))`;
  that triple is required. Reuse it for other `codeOfREPred` schemas.
- **Shell/monitoring:** `grep --include=*.lean` fails under this zsh unless quoted (a false
  "no references" negative); `safe-lake.sh … | grep | tail` emits nothing until exit — tee
  to a log; `pgrep -f safe-lake` in an `until` loop matches its own wrapper. A full
  `LogicalInduction` build from a stale-Framework state is ~35 min (2945 jobs).
- **Glyphs:** never retype `𝗜𝚺₁` (U+1D5DC U+1D6BA) in generated prose edits; copy it. A
  mistyped glyph passes every gate.
- **Foundation `Semiterm.Operator` arithmetic:** `(Add.add.comp ![a,b]).const` whnf-reduces
  to `Semiterm.func … ![a.const, b.const]`, so an encoder lemma can be bridged with `show … = _`.
  A well-founded-recursive `def` (e.g. `binNumeral`) does NOT unfold by `rfl` at a literal —
  `rw [binNumeral]; rfl`. `Matrix.fun_eq_vec_two` loops inside `simp only` (fine in full `simp`).
  In a strong-induction step `simp` normalizes `(w+2)/2` to `w/2+1` in the goal but not the IH —
  rewrite the IH first. `(List.range (n+1)).flatMap (fun _ => c)` induction: route through
  `(List.replicate n c).flatten`, since `rw [ih]` rewrites both sides.
- **Extracting `IsPolyBounded` from a `PolySegStream`:** `rintro ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩;
  obtain ⟨b, hrun, hpb, hbb⟩ := hl`; `hlen n` comes back beta-unreduced — restate it with an
  explicit type ascription before `rw`. `PolySegStream.constList` is declared late in
  `StructuredPaperRpn.lean` (Frontend section); term-level sections must use
  `PolySegStream.ofTokenStream (PolyTokenStream.const t)`.
- **`check-paper-nodes.sh` matches inventory members by SHORT name** (everything after the last
  dot), so `PaperLUV.toLUV` is satisfied by any annotated `toLUV` anywhere — a check that can
  pass for the wrong reason.
- **`safe-lake.sh build X 2>&1 | tee log | tail -40` reports `tail`'s exit status**, so a failed
  build looks like exit 0 (and a background-task notice says so too). Redirect
  (`> log 2>&1; echo EXIT=$?`) and grep the log for `^error`.
- **`LUV.RpnThresholdCodes`/`RpnThresholdCodeSeq` are `def`s**, so `h.comp` dot-notation fails;
  ascribe to the unfolded `RpnSentenceCodes _` first. The index shift Seq→single is reindexing
  along `m ↦ Nat.pair 0 m` (`(PolyFueled.const 0).pair PolyFueled.id`); `RpnThresholdCodes.constSeq`
  goes the OPPOSITE way. In `StructuredPaperRpn.lean`, `dyadicPaperLUV`/`unitFracPaperLUV` live
  near the END of the file — client examples at concrete LUVs must be placed after them.
- **Adding a tag to `parseStructuredArithmeticFormula` (Framework/Criterion.lean) has FOUR obligatory
  downstream repairs:** `parseStructuredArithmeticFormula_consumed_lt` and `_suffix`
  (Framework/RpnSentence.lean; both end in a `simp at h` closing the no-branch case),
  `structuredFormulaGCore` + `_spec` (Framework/RpnComputation.lean, the memoized mirror), and
  `structuredFormulaG_prim` (Construction/LIACompiler.lean). Criterion.lean is upstream of the
  whole library: `lake env lean` downstream fails with "object file … does not exist" until a
  full ~35–45 min build replaces the oleans.
- **`simp only [..., parseStructuredArithmeticFormula]` does not reduce the parser's literal tag
  if-chain**; a `rw` between that simp and the closing `rfl` fires inside an unreduced dead branch
  and corrupts the goal (symptom: huge `rfl failed` dump with `if True then …`). State per-tag
  equation lemmas `parse_tagNN … := rfl` and `rw` those first (`ArithSource.parse_tag20/21/22`).
- **Foundation has no `Semiformula.Evalm`.** Use `Semiformula.Eval b f φ` / `Evalf`/`Evalb`;
  `eval_all`/`eval_ex` are `of_eq rfl`, so finish with `forall_congr'`/`exists_congr`, not simp.
- **Foundation tokens:** biconditional `🡘`, implication `🡒`, universal `∀⁰`; `⭤`/`➝`/`∀'` do not parse.
  External ∀-instantiation is `LO.FirstOrder.Theory.Proof.specialize … ⨀`; there is NO external
  ∃-introduction for `T ⊢` (`Bootstrapping…ex_intro!` is the internal predicate). `T ⊢ n̄ ≠ m̄` is
  `weakening h (Entailment.by_axm (R0.Ω₃ n m hnm))`. Nested substitution normalizes with
  `simp only [Semiformula.subst, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst]` + `congrArg`
  (`congr`/`ext` dead-end).
- **`Semiformula.Evalbm` does not exist** (it appears once in Foundation source and misleads); use
  `Semiformula.Evalb (M := M) ![x] φ`. `paperPrimeDecompose (.all φ)` is not rfl-reducible —
  `simp only [paperPrimeDecompose]` then `rfl`. `↑(Semiformula.rel R v)` under `Rew.emb` does not
  compute by rfl (vector becomes `fun i => Rew.emb (v i)`); evaluate encoders with
  `simp [<def>, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols, encodeStructuredNat, Matrix.fun_eq_vec_two]`.
- **In `parseStructuredPaperPrime` contraction proofs the `simp only [List.cons_append]` after
  `rw [parseStructuredPaperPrime.eq_def]` is load-bearing** even though the linter says unused;
  deleting it breaks the following `rw [if_pos hbool]`.
- **`mulc_polyFueled W` multiplies on the RIGHT** (`fun n => n * W`); build `2n+1` as
  `hm.succ_comp.of_eq (by ring_nf)`. Repeated fixed blocks: `PolySegStream.blocks hb W (fun _ => rfl) (by omega) hcnt`
  producing `(List.range (cnt n)).flatMap (fun j => blk ⟨n,j⟩)` — state the token identity in that form.
- **NEVER `git commit --amend` in a checkout shared with a concurrently committing agent**; HEAD can
  move between commit and amend and the amend rewrites the OTHER agent's commit. New commit, always.
- **Foundation `Struc L` has no `Structure.Eq`**: `T ⊢ ↑y = ↑y` is not semantically valid and
  `Theory.Proof.complete` cannot prove it; use the equality axiom
  `weakening h (Entailment.by_axm (R0.equal _ Theory.eqAxiom.refl))` + `specialize`
  (`numeral_eq_refl_prov`). `Theory.Proof.complete` needs explicit universes `.{0, 0}`.
- **`∀⁰ φ` vs `Semiformula.all φ`** are defeq but not syntactically equal — state equation lemmas
  at `Semiformula.all/exs`; `Rewriting.emb X` vs `Rewriting.app Rew.emb X` likewise (trailing `rfl`).
- **After editing an upstream module, `lake env lean` downstream reports spurious "unknown
  identifier"** for the new declarations — rebuild just that module first
  (`safe-lake.sh build LogicalInduction.Framework.RepresentsComputations`).
- **Vacuous-quantifier introduction is not in Foundation's `Theory.Proof` API** (`specialize` only
  eliminates). Route: `Theory.Proof.complete_iff : T ⊨ φ ↔ T ⊢ φ` (Completeness/CounterModel.lean:253)
  → `provable_iff_of_realize_iff`; write the model lambda as `fun M _ _ => by …` so `[Nonempty M]` is
  introduced. In `∀ n, T ⊢ ∼(σ/[↑n])` the binder infers as a closed TERM, not ℕ — spell `∀ n : ℕ`.
  `ArithmeticTerm` takes a type argument; closed terms are `(‘↑n’ : ArithmeticSemiterm Empty 0)`.
- **`paperPrimeDecompose` contracts to one prime only at an `.exs` head** (and its `.all` negation);
  `∼` on `Formula` is `imp _ falsum`, so commutation with ⋏/⋎ is false syntactically —
  `PCWorld.holds_paperPrimeDecompose_neg` is semantic for that reason.
- **`binNumeral` is base-4 uniform Horner** (`digitTerm d = (1+1)*bit(d/2)+bit(d%2)`), two constant-width
  runs driven by `len4`/`dig4` (`dig4_succ` IS the Horner step) — base-2 Horner branches on parity and
  `PolySegStream.blocks` needs a constant block width. `binNumeralEnc_length_le` is `8·log₂v+7`.
- **`provable_subst_iff_of_val T φ t v hval : T ⊢ φ/[t.const] ↔ T ⊢ φ/[↑v]`** (RepresentsComputations.lean):
  completeness out, `Theory.Proof.sound` back; needs only `𝗣𝗔⁻ ⪯ T` (Foundation derives it from
  `[𝗜𝚺₁ ⪯ T]`, Schemata.lean:404); state `hval` over `M : Type` to match `Arithmetic.complete.{0}`.
  `Structure.numeral_eq_numeral` lands on `ORingStructure.numeral`; bridge with `numeral_eq_natCast`.
- **`𝗣𝗔⁻`/`⊧*` are PARSE errors ("expected token") without `import …PeanoMinus.Basic`/`.Schemata`.**
- **Atom-equality → formula-equality chain:** `paperPrimeSentence_injective` (explicit `(a₁ := (true, φ))`),
  `Semiformula.exs.injEq`, `Rewriting.emb_injective`; strip `∼` first with `simpa using congrArg (∼·)`.
- **Probing a goal by a scratch file that imports the file being edited sees the stale olean**; insert
  `trace_state; sorry` in the real file and run `safe-lake.sh env lean` on it instead.
- **`Nat.pow_le_iff_le_log` does not exist** — `Nat.le_log_iff_pow_le`. `omega` treats `2^2` as an atom.
  `simp` with `Matrix.fun_eq_vec_two` loops on nested `Operator.comp ![…]` defs — prove operator-value
  steps on opaque `s t : Semiterm.Const` and use `simp only`.
- **Collapsing a def into an instance of a general one is defeq-safe but simp-unsafe** (downstream
  `simp [thatDef]` halts at the new intermediate); keep the direct body + a `rfl` bridge.
- **The emission certificate for a substituted term must be arity-quantified**
  (`henc : ∀ l, PolySegStream (fun n => encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))`)
  because the ∀/∃ cases re-enter at depth l+1 under `Rew.q`. `‘↑n’` is definitionally
  `(Operator.numeral ℒₒᵣ n).const`, so numeral instantiation needs no transport.
- **Gate calibration under contention:** a warm `safe-lake.sh build LogicalInduction` ran ~2h with three
  agents sharing the 24 GB machine (swap 95%); `safe-lake.sh env lean` is 3–5 s.
- **`Semiformula.subst φ ![t]` vs the `φ/[t]` notation are not interchangeable for `rw`** (the
  notation expands to `Rewriting.subst`); state transport lemmas in the consumer's spelling.
  `𝗣𝗔⁻ ⪯ 𝗜𝚺₁` is an inferable Foundation instance (`WeakerThan.trans (𝓣 := 𝗜𝚺₁)`).
- **`scripts/check_trust_surface.py` is a gate**: `gen-trust-surface.py`'s editorial notes are a SECOND
  copy of the per-node commentary — retiring a claim only in `coverage-classification.md` leaves stale
  assertions on the published page. Regenerate last (`latex2mathml` is installed).
- **Census splitter:** elaborated `#check` output prints some declarations as `@Name : …` and dotted
  names by last component — the naive `^Name : ` regex loses ~1/3 of blocks and mis-attributes them;
  match `^@?ident : ` and re-anchor by suffix. Never grep the word "Consistent" (matches
  `PCWorld.ConsistentWith*`; 14 → ~60).
- **`safe-lake.sh` has two give-up paths that look like hangs and are neither a red build**: lock
  timeout after 1800s, and `resource-guard wait 900` exiting "STILL LOADED" (disk floor 15GB free —
  disk does not recover on its own). `lake env lean` takes the same lock. `gen-trust-surface.py`
  writes its output only at the end — never run two concurrently.
- **The session scratchpad can be shared with a concurrent agent in the same worktree** — prefix
  scratch outputs uniquely; generic names (`census.out`, `build.log`) get clobbered.
