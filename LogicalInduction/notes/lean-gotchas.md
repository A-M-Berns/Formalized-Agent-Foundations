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
