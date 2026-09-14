import LogicalInduction.Construction.Primcodable
import LogicalInduction.Properties.Support.SettlementDecision
import Mathlib.Computability.Halting
import Foundation.Vorspiel.Computability

/-!
# Dovetailing a semi-decider into a computable deductive process

Every constructed deductive process in `Construction/` is built the same way: an r.e.
*event* predicate on `ℕ`, a sentence named by each event, and a dovetail that publishes at
stage `k` the sentences of the events whose semi-decider halts within `k` interpreter
steps.  This module is that construction, written once.

## The interface

* `exists_semiDecider` turns an `REPred` into a `Nat.Partrec.Code` whose domain is exactly
  the predicate — the `∃ code, ∀ e, (code.eval e).Dom ↔ P e` shape every lane opens with.
* `dovetailStage atom code k` is the stage: the `atom`-images of the events `e ≤ k` on
  which `code` halts within fuel `k`.  `mem_dovetailStage` is its membership law, stated in
  the shape `simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]` produces, so
  `obtain ⟨e, ⟨-, hsome⟩, rfl⟩` reads off a membership hypothesis directly.
* `dovetailProcess atom code` bundles it as a `DeductiveProcess` (monotone by
  `evaln`-monotonicity), with `dovetailProcess_D` unfolding its stage and
  `dovetailProcess_covers` saying that every halting event's sentence eventually appears.
* `dovetailProcess_computable` discharges `ComputableDeductiveProcess` from `Primrec atom`
  alone.

## The stage-list layer

The computability half factors through two facts that are useful on their own, for
processes that are *not* dovetails:

* `encode_stage_prim_of_list` — a stage family presented as the `toFinset` of a primitive
  recursive list family has a primitive recursive encoder.  `encode_toFinset_eq` is what
  makes this work: a `Finset Sentence` given as `l.toFinset` has the code of the canonical
  deduplicated, `sentenceCodeLE`-sorted list.
* `ComputableDeductiveProcess.ofEncodePrim` — a primitive recursive stage encoder is a
  `ComputableDeductiveProcess`.

## The prefix layer

A lane whose clause family is decidable needs no dovetailing clock: it publishes the clauses
of every job code `e ≤ n` at stage `n`.  `prefixProcess` is that process, written once, with
`mem_prefixProcess` for its membership law, `self_mem_prefixProcess` for the one-sided form
every `hv` application uses, and `prefixProcess_computable` / `prefixProcess_encode_prim`
discharging `def:dedproc` from `Computable ψ` / `Primrec ψ` alone.  Five lanes instantiate it
(the quotation closure, the two product closures, the source interpreter and the registry),
and so does the conditioning lane's prefix presentation.
-/

namespace LogicalInduction

open Nat.Partrec (Code)

/-! ## The stage-list layer -/

/-- A stage's Gödel code is exactly the code of its sorted sentence list. -/
lemma encode_eq_encode_stageSort (stage : Finset Sentence) :
    Encodable.encode stage = Encodable.encode (stageSort stage) := rfl

/-- A finite sentence set given as a list's `toFinset` has the code of the canonical
sorted, duplicate-free list.  Every stage-encoding computability proof in the
`Construction/` lanes reduces its stage encoder to this shape. -/
lemma encode_toFinset_eq (l : List Sentence) :
    Encodable.encode l.toFinset =
      Encodable.encode ((List.dedup l).insertionSort sentenceCodeLE) := by
  classical
  let canonical := (List.dedup l).insertionSort sentenceCodeLE
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort sentenceCodeLE _).nodup_iff.mpr (List.nodup_dedup l)
  have hsorted : canonical.Pairwise sentenceCodeLE :=
    List.pairwise_insertionSort sentenceCodeLE _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext φ; simp [canonical, List.mem_dedup]
  have hsort : l.toFinset.sort sentenceCodeLE = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := sentenceCodeLE) hnodup).mpr hsorted
  rw [encode_eq_encode_stageSort l.toFinset]
  exact congrArg Encodable.encode hsort

/-- **The stage-list criterion.**  A stage family presented as the `toFinset` of a
primitive recursive list family has a primitive recursive Gödel-code function. -/
lemma encode_stage_prim_of_list {D : ℕ → Finset Sentence} {l : ℕ → List Sentence}
    (hl : Primrec l) (hD : ∀ k, D k = (l k).toFinset) :
    Primrec fun k => Encodable.encode (D k) := by
  have hkey : (fun k => Encodable.encode (D k))
      = fun k => Encodable.encode ((List.dedup (l k)).insertionSort sentenceCodeLE) := by
    funext k
    rw [hD k, encode_toFinset_eq]
  rw [hkey]
  exact Primrec.encode.comp (sentenceInsertionSort_prim.comp (dedup_prim.comp hl))

/-- A deductive process whose stage encoder is primitive recursive is computable: a
primitive recursive function is a total partial recursive one, and `exists_code` names the
program `def:dedproc` asks for. -/
lemma ComputableDeductiveProcess.ofEncodePrim {DP : DeductiveProcess}
    (h : Primrec fun k => Encodable.encode (DP.D k)) : ComputableDeductiveProcess DP := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp h))
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## Prefix enumerations -/

/-- The prefix deductive process of a sentence sequence: stage `n` is the finite set
`{ψ₀, …, ψₙ}`.  Every lane whose clause family is decidable — no dovetailing clock needed —
publishes its stages this way, indexing the clauses by a packed job code.  Its condition, in
the conditioning lane, is the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ`
(`Construction/Conditioning/Presentation.lean`).
Paper node: `thm:scon` -/
def prefixProcess (ψ : ℕ → Sentence) : DeductiveProcess where
  D n := ((List.range (n + 1)).map ψ).toFinset
  mono n := by
    intro φ hφ
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hφ ⊢
    obtain ⟨i, hi, rfl⟩ := hφ
    exact ⟨i, by omega, rfl⟩

/-- Membership in a prefix stage: the clauses of stage `n` are exactly the `ψ e` for `e ≤ n`.
It is the one membership law for every lane built on `prefixProcess`. -/
lemma mem_prefixProcess {ψ : ℕ → Sentence} {n : ℕ} {φ : Sentence} :
    φ ∈ (prefixProcess ψ).D n ↔ ∃ e ≤ n, ψ e = φ := by
  change φ ∈ ((List.range (n + 1)).map ψ).toFinset ↔ _
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

/-- Each clause is published by its own job code's stage. -/
lemma self_mem_prefixProcess (ψ : ℕ → Sentence) {e n : ℕ} (h : e ≤ n) :
    ψ e ∈ (prefixProcess ψ).D n :=
  mem_prefixProcess.mpr ⟨e, h, rfl⟩

/-- A prefix process with a primitive recursive clause family has a primitive recursive
stage encoder. -/
lemma prefixProcess_encode_prim {ψ : ℕ → Sentence} (hψ : Primrec ψ) :
    Primrec fun n => Encodable.encode ((prefixProcess ψ).D n) :=
  encode_stage_prim_of_list
    (Primrec.list_map (Primrec.list_range.comp Primrec.succ) (hψ.comp Primrec.snd).to₂)
    (fun _ => rfl)

/-- The clauses of stage `n`, newest first.  Mathlib has `Primrec.list_map` but no
`Computable.list_map`, so the merely computable case is certified through this `nat_rec`
recursion and `prefixListRev_eq`. -/
private def prefixListRev (ψ : ℕ → Sentence) : ℕ → List Sentence
  | 0 => [ψ 0]
  | k + 1 => ψ (k + 1) :: prefixListRev ψ k

private lemma prefixListRev_eq (ψ : ℕ → Sentence) (n : ℕ) :
    prefixListRev ψ n = ((List.range (n + 1)).map ψ).reverse := by
  induction n with
  | zero => rfl
  | succ k ih => rw [prefixListRev, ih]; simp [List.range_succ]

/-- **A prefix process with a computable clause family is a `ComputableDeductiveProcess`.**
`def:dedproc` asks for a program printing each stage code, and the code of a stage given as a
list's `toFinset` is the code of its deduplicated, `sentenceCodeLE`-sorted list
(`encode_toFinset_eq`). -/
lemma prefixProcess_computable {ψ : ℕ → Sentence} (hψ : Computable ψ) :
    ComputableDeductiveProcess (prefixProcess ψ) := by
  have hrev : Computable (prefixListRev ψ) := by
    have hstep : Computable fun p : ℕ × List Sentence => ψ (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (hψ.comp (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id (Computable.const [ψ 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [prefixListRev] using ih
  have hlist : Computable fun n : ℕ => (List.range (n + 1)).map ψ :=
    (Computable.list_reverse.comp hrev).of_eq fun n => by
      rw [prefixListRev_eq, List.reverse_reverse]
  have hkey : Computable fun n => Encodable.encode
      ((List.dedup ((List.range (n + 1)).map ψ)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp dedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq ((List.range (n + 1)).map ψ))

/-! ## The dovetail -/

open Classical in
/-- Fuel-`k` dovetailer: the sentences named by every event `e ≤ k` whose semi-decider
halts within `k` interpreter steps. -/
noncomputable def dovetailStage (atom : ℕ → Sentence) (code : Code) (k : ℕ) :
    Finset Sentence :=
  ((Finset.range (k + 1)).filter
    (fun e => (Nat.Partrec.Code.evaln k code e).isSome = true)).image atom

lemma mem_dovetailStage {atom : ℕ → Sentence} {code : Code} {k : ℕ} {φ : Sentence} :
    φ ∈ dovetailStage atom code k ↔
      ∃ e, (e < k + 1 ∧ (Nat.Partrec.Code.evaln k code e).isSome = true) ∧ atom e = φ := by
  classical
  simp only [dovetailStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range]

/-- Monotone in the fuel, by `evaln`-monotonicity. -/
lemma dovetailStage_mono (atom : ℕ → Sentence) (code : Code) (k : ℕ) :
    dovetailStage atom code k ⊆ dovetailStage atom code (k + 1) := by
  intro φ hφ
  rw [mem_dovetailStage] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

/-- The deductive process a semi-decider and a naming map generate. -/
noncomputable def dovetailProcess (atom : ℕ → Sentence) (code : Code) : DeductiveProcess where
  D := dovetailStage atom code
  mono := dovetailStage_mono atom code

@[simp] lemma dovetailProcess_D (atom : ℕ → Sentence) (code : Code) :
    (dovetailProcess atom code).D = dovetailStage atom code := rfl

/-- Coverage: the sentence of every event the semi-decider accepts eventually appears. -/
lemma dovetailProcess_covers {atom : ℕ → Sentence} {code : Code} {e : ℕ}
    (he : (code.eval e).Dom) : ∃ k, atom e ∈ (dovetailProcess atom code).D k := by
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp he
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
  refine ⟨max e fuel, ?_⟩
  rw [dovetailProcess_D, mem_dovetailStage]
  exact ⟨e, ⟨by omega, evaln_isSome_mono (le_max_right e fuel)
    (Option.isSome_iff_exists.mpr ⟨out, hfuel⟩)⟩, rfl⟩

/-- The stage as a deduplicated list, the shape the primitive-recursive encoder works on. -/
lemma dovetailStage_eq_toFinset (atom : ℕ → Sentence) (code : Code) (k : ℕ) :
    dovetailStage atom code k =
      ((List.range (k + 1)).filterMap
        (fun e => if (Nat.Partrec.Code.evaln k code e).isSome = true then some (atom e)
          else none)).toFinset := by
  classical
  ext φ
  rw [mem_dovetailStage]
  simp only [List.mem_toFinset, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨e, ⟨he, hsome⟩, rfl⟩
    exact ⟨e, he, by rw [if_pos hsome]⟩
  · rintro ⟨e, he, hcond⟩
    by_cases hs : (Nat.Partrec.Code.evaln k code e).isSome = true
    · rw [if_pos hs] at hcond
      exact ⟨e, ⟨he, hs⟩, Option.some_inj.mp hcond⟩
    · rw [if_neg hs] at hcond
      exact absurd hcond (by simp)

/-- The dovetailed stage encoder is primitive recursive whenever the naming map is. -/
lemma dovetailStage_encode_prim {atom : ℕ → Sentence} (hatom : Primrec atom) (code : Code) :
    Primrec fun k => Encodable.encode (dovetailStage atom code k) := by
  have hevaln : Primrec (fun p : ℕ × ℕ =>
      (Nat.Partrec.Code.evaln p.1 code p.2).isSome) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const code)).pair Primrec.snd))
  have hguncur : Primrec (fun p : ℕ × ℕ =>
      if (Nat.Partrec.Code.evaln p.1 code p.2).isSome = true then some (atom p.2)
        else (none : Option Sentence)) := by
    have hb : Primrec (fun p : ℕ × ℕ =>
        bif (Nat.Partrec.Code.evaln p.1 code p.2).isSome then some (atom p.2)
          else (none : Option Sentence)) :=
      Primrec.cond hevaln (Primrec.option_some.comp (hatom.comp Primrec.snd))
        (Primrec.const (none : Option Sentence))
    exact hb.of_eq fun p => by
      cases (Nat.Partrec.Code.evaln p.1 code p.2).isSome <;> simp
  exact encode_stage_prim_of_list
    (Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hguncur.to₂)
    (dovetailStage_eq_toFinset atom code)

/-- **The dovetailed process is computable**, from `Primrec atom` alone. -/
lemma dovetailProcess_computable {atom : ℕ → Sentence} (hatom : Primrec atom) (code : Code) :
    ComputableDeductiveProcess (dovetailProcess atom code) :=
  ComputableDeductiveProcess.ofEncodePrim (dovetailStage_encode_prim hatom code)

/-! ## Semi-deciders -/

/-- An r.e. predicate on `ℕ` has a partial-recursive semi-decider: a code whose domain is
exactly the predicate. -/
lemma exists_semiDecider {P : ℕ → Prop} (h : REPred P) :
    ∃ code : Code, ∀ e, (code.eval e).Dom ↔ P e := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp h
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun e => ?_⟩
  rw [hcode]
  exact (hfP e).symm

end LogicalInduction
