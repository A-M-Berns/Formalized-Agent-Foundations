import LogicalInduction.Construction.Freeze.StructuredPatterns
import LogicalInduction.Construction.Freeze.CounterAutomaton

/-!
# Splitting `SegMatch` into a regular part and a counter part

Renders `app:ifp` (tex:6018): `StructPat.SegMatch` is exact, but it is not what a
finite-state device decides, because a structured segment's unary length field `1^L` must
equal its payload's own token count, and that is an `aⁿbⁿ` constraint.  This module performs
the split, exactly:

    SegMatch p b  ↔  SegMatchRelaxed p b  ∧  (segCtr p).Accepts b

* `StructBlockRelaxed` drops the length identification (carrying instead the payload's
  `19`-freedom, which the payload grammar supplies anyway) and `SegMatchRelaxed` is the
  resulting segment-match relation — the half a finite automaton checks.
* `segCtr` is the one-counter `CtrAuto.CtrProgram` that checks the length identification
  alone, one structured segment at a time.
* State encoding: `stQ p m k = (p.length + 1) * m + k` with kinds `0`–`5` (segment start,
  opening `1`, polarity, unary field, payload, absorbing reject), `rejSt` the reject state
  and program bound.
* Both zero tests in the payload state are load-bearing: at the terminator the counter must
  be exactly spent, and a payload token arriving with the counter spent means the payload is
  longer than the field.
* `segMatch_iff_relaxed_and_ctr` proves the split exact; `h19` (a complete payload contains
  no `19`) is a hypothesis so that `PayAuto.nineteen_not_mem_of_parse` is not duplicated.

Consumed by `SegmentRecognizer.lean`; `segMatch_iff_relaxed_and_ctr` is in
`AxiomAudit.lean`.
-/

namespace LogicalInduction

namespace SegCtr

open CtrAuto StructPat

/-! ## The relaxed part of the split -/

/-- Dropping the length identification: an exact segment match is a relaxed one. -/
lemma matchesRelaxed_of_matchesSeg
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q)
    {σ : StructPat.PatSeg} {b : List ℕ} (h : StructPat.PatSeg.MatchesSeg σ b) :
    PatSeg.MatchesRelaxed σ b := by
  cases σ with
  | lit t => exact h
  | hole χ => exact h
  | struct pol fc =>
      obtain ⟨q, rfl, hpol, hparse⟩ := h
      exact ⟨q.length, q, rfl, hpol, hparse, h19 hparse⟩

lemma segMatch_relaxed_of_segMatch
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q)
    {p : List StructPat.PatSeg} {b : List ℕ} (h : StructPat.SegMatch p b) :
    SegMatchRelaxed p b := by
  obtain ⟨bs, hf, rfl⟩ := h
  exact ⟨bs, hf.imp (fun _ _ hh => matchesRelaxed_of_matchesSeg h19 hh), rfl⟩

/-! ## The counter program

`K := p.length + 1` control slots per kind; a state is `K * m + k` with kind `m` and
segment index `k`:

* `m = 0` — about to start segment `k` (`k = p.length` is the accepting state);
* `m = 1` — read the block's leading `1`, expecting the `0`;
* `m = 2` — expecting the polarity token;
* `m = 3` — inside the unary length field (each `1` increments the counter);
* `m = 4` — inside the payload (each token decrements it);
* `m = 5`, `k = 0` — the absorbing reject state.

Both zero tests in the payload state are load-bearing: at the terminator the counter must
be exactly spent, and a payload token arriving with the counter already spent means the
payload is longer than the field. -/

/-- Control state `K * m + k`. -/
def stQ (p : List StructPat.PatSeg) (m k : ℕ) : ℕ := (p.length + 1) * m + k

/-- The absorbing reject state, and the program's state bound. -/
def rejSt (p : List StructPat.PatSeg) : ℕ := (p.length + 1) * 5

/-- Is this segment a structured block? -/
def isStructO : Option StructPat.PatSeg → Bool
  | some (.struct _ _) => true
  | _ => false

/-- The transition table, on a decoded state. -/
def ctrlF (p : List StructPat.PatSeg) (m k t : ℕ) (z : Bool) : ℕ :=
  if m = 0 then
    (if p[k]?.isSome then
      (if isStructO p[k]? then (if t = 1 then stQ p 1 k else rejSt p) else k + 1)
     else rejSt p)
  else if m = 1 then (if t = 0 then stQ p 2 k else rejSt p)
  else if m = 2 then stQ p 3 k
  else if m = 3 then (if t = 1 then stQ p 3 k else if t = 0 then stQ p 4 k else rejSt p)
  else if m = 4 then
    (if t = 19 then (if z then k + 1 else rejSt p)
     else (if z then rejSt p else stQ p 4 k))
  else rejSt p

/-- The counter action, on a decoded state kind. -/
def actF (m t : ℕ) : CAct :=
  if m = 3 then (if t = 1 then CAct.inc else CAct.keep)
  else if m = 4 then (if t = 19 then CAct.keep else CAct.dec)
  else CAct.keep

lemma ctrlF_le (p : List StructPat.PatSeg) (m k t : ℕ) (z : Bool) (hk : k < p.length + 1) :
    ctrlF p m k t z ≤ rejSt p := by
  simp only [ctrlF, stQ, rejSt]
  split_ifs <;> omega

/-- **The counter program that checks every structured segment's length field.** -/
def segCtr (p : List StructPat.PatSeg) : CtrProgram where
  Q := rejSt p
  A := 19
  ctrl := fun i t z => ctrlF p (i / (p.length + 1)) (i % (p.length + 1)) t z
  act := fun i t _ => actF (i / (p.length + 1)) t
  accept := fun i => decide (i = p.length)
  init := 0
  init_le := Nat.zero_le _
  ctrl_le := fun _i t z =>
    ctrlF_le p _ _ t z (Nat.mod_lt _ (Nat.succ_pos _))

/-! ## Decoding the state -/

variable {p : List StructPat.PatSeg}

lemma stQ_div {m k : ℕ} (hk : k < p.length + 1) : stQ p m k / (p.length + 1) = m := by
  rw [stQ, Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt hk, Nat.add_zero]

lemma stQ_mod {m k : ℕ} (hk : k < p.length + 1) : stQ p m k % (p.length + 1) = k := by
  rw [stQ, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

lemma rejSt_eq : rejSt p = stQ p 5 0 := by simp [stQ, rejSt]

lemma step_stQ (m k n t : ℕ) (hk : k < p.length + 1) :
    (segCtr p).step (stQ p m k, n) t
      = (ctrlF p m k (min t 20) (decide (n = 0)), (actF m (min t 20)).apply n) := by
  show (ctrlF p (stQ p m k / (p.length + 1)) (stQ p m k % (p.length + 1)) (min t 20)
          (decide (n = 0)),
        (actF (stQ p m k / (p.length + 1)) (min t 20)).apply n) = _
  rw [stQ_div hk, stQ_mod hk]

lemma step_pos (k n t : ℕ) (hk : k < p.length + 1) :
    (segCtr p).step (k, n) t
      = (ctrlF p 0 k (min t 20) (decide (n = 0)), (actF 0 (min t 20)).apply n) := by
  have h := step_stQ (p := p) 0 k n t hk
  rwa [show stQ p 0 k = k from by rw [stQ]; omega] at h

/-! ## The individual steps -/

lemma step_rej (n t : ℕ) : (segCtr p).step (rejSt p, n) t = (rejSt p, n) := by
  rw [rejSt_eq, step_stQ 5 0 n t (Nat.succ_pos _)]
  simp [ctrlF, actF, CAct.apply, ← rejSt_eq]

lemma foldl_rej : ∀ (ts : List ℕ) (n : ℕ),
    List.foldl (segCtr p).step (rejSt p, n) ts = (rejSt p, n)
  | [], n => rfl
  | t :: ts, n => by rw [List.foldl_cons, step_rej, foldl_rej ts n]

lemma step_pos_other {σ : StructPat.PatSeg} {k : ℕ} (hσ : p[k]? = some σ)
    (hns : isStructO (some σ) = false) (n t : ℕ) :
    (segCtr p).step (k, n) t = (k + 1, n) := by
  have hk : k < p.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hσ
    exact h
  rw [step_pos k n t (by omega)]
  simp [ctrlF, actF, CAct.apply, hσ, hns]

lemma step_pos_struct {pol fc : ℕ} {k : ℕ}
    (hσ : p[k]? = some (StructPat.PatSeg.struct pol fc)) (n : ℕ) :
    (segCtr p).step (k, n) 1 = (stQ p 1 k, n) := by
  have hk : k < p.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hσ
    exact h
  rw [step_pos k n 1 (by omega)]
  simp [ctrlF, actF, CAct.apply, hσ, isStructO]

lemma step_s1 {k : ℕ} (hk : k < p.length + 1) (n : ℕ) :
    (segCtr p).step (stQ p 1 k, n) 0 = (stQ p 2 k, n) := by
  rw [step_stQ 1 k n 0 hk]
  simp [ctrlF, actF, CAct.apply]

lemma step_s2 {k : ℕ} (hk : k < p.length + 1) (n t : ℕ) :
    (segCtr p).step (stQ p 2 k, n) t = (stQ p 3 k, n) := by
  rw [step_stQ 2 k n t hk]
  simp [ctrlF, actF, CAct.apply]

lemma step_slen_one {k : ℕ} (hk : k < p.length + 1) (n : ℕ) :
    (segCtr p).step (stQ p 3 k, n) 1 = (stQ p 3 k, n + 1) := by
  rw [step_stQ 3 k n 1 hk]
  simp [ctrlF, actF, CAct.apply]

lemma step_slen_zero {k : ℕ} (hk : k < p.length + 1) (n : ℕ) :
    (segCtr p).step (stQ p 3 k, n) 0 = (stQ p 4 k, n) := by
  rw [step_stQ 3 k n 0 hk]
  simp [ctrlF, actF, CAct.apply]

lemma step_spay_tok {k : ℕ} (hk : k < p.length + 1) {n t : ℕ} (ht : t ≠ 19) (hn : n ≠ 0) :
    (segCtr p).step (stQ p 4 k, n) t = (stQ p 4 k, n - 1) := by
  have ht' : min t 20 ≠ 19 := by omega
  rw [step_stQ 4 k n t hk]
  simp [ctrlF, actF, CAct.apply, ht', hn]

lemma step_spay_tok_zero {k : ℕ} (hk : k < p.length + 1) {t : ℕ} (ht : t ≠ 19) :
    (segCtr p).step (stQ p 4 k, 0) t = (rejSt p, 0) := by
  have ht' : min t 20 ≠ 19 := by omega
  rw [step_stQ 4 k 0 t hk]
  simp [ctrlF, actF, CAct.apply, ht']

lemma step_spay_term_zero {k : ℕ} (hk : k < p.length + 1) :
    (segCtr p).step (stQ p 4 k, 0) 19 = (k + 1, 0) := by
  rw [step_stQ 4 k 0 19 hk]
  simp [ctrlF, actF, CAct.apply]

lemma step_spay_term_pos {k : ℕ} (hk : k < p.length + 1) {n : ℕ} (hn : n ≠ 0) :
    (segCtr p).step (stQ p 4 k, n) 19 = (rejSt p, n) := by
  rw [step_stQ 4 k n 19 hk]
  simp [ctrlF, actF, CAct.apply, hn]

/-! ## Running a structured block -/

lemma foldl_slen {k : ℕ} (hk : k < p.length + 1) : ∀ (L n : ℕ),
    List.foldl (segCtr p).step (stQ p 3 k, n) (List.replicate L 1) = (stQ p 3 k, n + L)
  | 0, n => by simp
  | L + 1, n => by
      rw [List.replicate_succ, List.foldl_cons, step_slen_one hk, foldl_slen hk L (n + 1)]
      congr 1
      omega

lemma foldl_spay_ok {k : ℕ} (hk : k < p.length + 1) : ∀ (pay : List ℕ), 19 ∉ pay →
    ∀ n : ℕ, pay.length ≤ n →
      List.foldl (segCtr p).step (stQ p 4 k, n) pay = (stQ p 4 k, n - pay.length)
  | [], _, n, _ => by simp
  | t :: pay, hpay, n, hn => by
      have ht : t ≠ 19 := fun h => hpay (by rw [h]; exact List.mem_cons_self ..)
      have hlen : pay.length + 1 ≤ n := by simpa using hn
      have hn0 : n ≠ 0 := by omega
      rw [List.foldl_cons, step_spay_tok hk ht hn0,
        foldl_spay_ok hk pay (fun h => hpay (List.mem_cons_of_mem _ h)) (n - 1) (by omega)]
      congr 1
      simp only [List.length_cons]
      omega

lemma foldl_spay_bad {k : ℕ} (hk : k < p.length + 1) : ∀ (pay : List ℕ), 19 ∉ pay →
    ∀ n : ℕ, n < pay.length →
      ∃ m, List.foldl (segCtr p).step (stQ p 4 k, n) pay = (rejSt p, m)
  | [], _, n, hn => absurd hn (by simp)
  | t :: pay, hpay, n, hn => by
      have ht : t ≠ 19 := fun h => hpay (by rw [h]; exact List.mem_cons_self ..)
      have hpay' : 19 ∉ pay := fun h => hpay (List.mem_cons_of_mem _ h)
      by_cases hn0 : n = 0
      · subst hn0
        rw [List.foldl_cons, step_spay_tok_zero hk ht, foldl_rej]
        exact ⟨0, rfl⟩
      · rw [List.foldl_cons, step_spay_tok hk ht hn0]
        have hlt : n - 1 < pay.length := by
          simp only [List.length_cons] at hn
          omega
        exact foldl_spay_bad hk pay hpay' (n - 1) hlt

/-- The block's prefix — the dispatch tokens, the polarity, the unary field, and its
closing `0` — drives the control to the payload state with the counter at `L`. -/
lemma foldl_struct_prefix {pol fc : ℕ} {k : ℕ}
    (hσ : p[k]? = some (StructPat.PatSeg.struct pol fc)) (L : ℕ) (pay : List ℕ) :
    List.foldl (segCtr p).step (k, 0)
        ([1, 0, pol] ++ List.replicate L 1 ++ 0 :: pay ++ [19])
      = List.foldl (segCtr p).step (stQ p 4 k, L) (pay ++ [19]) := by
  have hk : k < p.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hσ
    exact h
  have hk' : k < p.length + 1 := by omega
  have hb : ([1, 0, pol] ++ List.replicate L 1 ++ 0 :: pay ++ [19] : List ℕ)
      = 1 :: 0 :: pol :: (List.replicate L 1 ++ 0 :: (pay ++ [19])) := by simp
  rw [hb, List.foldl_cons, step_pos_struct hσ, List.foldl_cons, step_s1 hk',
    List.foldl_cons, step_s2 hk', List.foldl_append, foldl_slen hk' L 0,
    List.foldl_cons, Nat.zero_add, step_slen_zero hk']

lemma foldl_struct_ok {pol fc : ℕ} {k : ℕ}
    (hσ : p[k]? = some (StructPat.PatSeg.struct pol fc)) (pay : List ℕ) (hpay : 19 ∉ pay) :
    List.foldl (segCtr p).step (k, 0)
        ([1, 0, pol] ++ List.replicate pay.length 1 ++ 0 :: pay ++ [19]) = (k + 1, 0) := by
  have hk : k < p.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hσ
    exact h
  have hk' : k < p.length + 1 := by omega
  rw [foldl_struct_prefix hσ pay.length pay, List.foldl_append,
    foldl_spay_ok hk' pay hpay pay.length le_rfl, Nat.sub_self, List.foldl_cons,
    step_spay_term_zero hk']
  rfl

lemma foldl_struct_bad {pol fc : ℕ} {k : ℕ}
    (hσ : p[k]? = some (StructPat.PatSeg.struct pol fc)) (L : ℕ) (pay : List ℕ)
    (hpay : 19 ∉ pay) (hL : L ≠ pay.length) :
    ∃ m, List.foldl (segCtr p).step (k, 0)
        ([1, 0, pol] ++ List.replicate L 1 ++ 0 :: pay ++ [19]) = (rejSt p, m) := by
  have hk : k < p.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hσ
    exact h
  have hk' : k < p.length + 1 := by omega
  rw [foldl_struct_prefix hσ L pay]
  rcases lt_or_ge L pay.length with hlt | hge
  · obtain ⟨m, hm⟩ := foldl_spay_bad hk' pay hpay L hlt
    rw [List.foldl_append, hm, foldl_rej]
    exact ⟨m, rfl⟩
  · rw [List.foldl_append, foldl_spay_ok hk' pay hpay L hge, List.foldl_cons,
      step_spay_term_pos hk' (by omega)]
    exact ⟨L - pay.length, rfl⟩

/-! ## Running one segment -/

lemma run_seg_exact
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q)
    {σ : StructPat.PatSeg} {b : List ℕ} {k : ℕ} (hσ : p[k]? = some σ)
    (hm : StructPat.PatSeg.MatchesSeg σ b) :
    List.foldl (segCtr p).step (k, 0) b = (k + 1, 0) := by
  cases σ with
  | lit t =>
      obtain rfl : b = [t] := hm
      rw [List.foldl_cons, step_pos_other hσ rfl 0 t]
      rfl
  | hole χ =>
      obtain ⟨c, rfl, -⟩ := hm
      rw [List.foldl_cons, step_pos_other hσ rfl 0 c]
      rfl
  | struct pol fc =>
      obtain ⟨q, rfl, -, hparse⟩ := hm
      exact foldl_struct_ok hσ q (h19 hparse)

lemma run_seg_rej {σ : StructPat.PatSeg} {b : List ℕ} {k : ℕ} (hσ : p[k]? = some σ)
    (hrel : PatSeg.MatchesRelaxed σ b) (hnot : ¬ StructPat.PatSeg.MatchesSeg σ b) :
    ∃ m, List.foldl (segCtr p).step (k, 0) b = (rejSt p, m) := by
  cases σ with
  | lit t => exact absurd hrel hnot
  | hole χ => exact absurd hrel hnot
  | struct pol fc =>
      obtain ⟨L, q, rfl, hpol, hparse, hq19⟩ := hrel
      have hL : L ≠ q.length := by
        intro h
        subst h
        exact hnot ⟨q, rfl, hpol, hparse⟩
      exact foldl_struct_bad hσ L q hq19 hL

/-! ## Running a whole pattern -/

private lemma drop_cons_aux {σ : StructPat.PatSeg} {segs : List StructPat.PatSeg} {k : ℕ}
    (hd : p.drop k = σ :: segs) : p[k]? = some σ ∧ p.drop (k + 1) = segs := by
  constructor
  · have h : (p.drop k)[0]? = some σ := by rw [hd]; rfl
    rwa [List.getElem?_drop, Nat.add_zero] at h
  · rw [← List.tail_drop, hd]
    rfl

lemma run_exact
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q) :
    ∀ {segs : List StructPat.PatSeg} {bs : List (List ℕ)},
      List.Forall₂ StructPat.PatSeg.MatchesSeg segs bs →
      ∀ k : ℕ, p.drop k = segs →
        List.foldl (segCtr p).step (k, 0) bs.flatten = (k + segs.length, 0) := by
  intro segs bs h
  induction h with
  | nil => intro k _; simp
  | @cons σ b segs' bs' hhead htail ih =>
      intro k hd
      obtain ⟨hσ, hdrop⟩ := drop_cons_aux hd
      rw [List.flatten_cons, List.foldl_append, run_seg_exact h19 hσ hhead,
        ih (k + 1) hdrop]
      congr 1
      simp only [List.length_cons]
      omega

lemma run_rej
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q) :
    ∀ {segs : List StructPat.PatSeg} {bs : List (List ℕ)},
      List.Forall₂ PatSeg.MatchesRelaxed segs bs →
      ¬ List.Forall₂ StructPat.PatSeg.MatchesSeg segs bs →
      ∀ k : ℕ, p.drop k = segs →
        ∃ m, List.foldl (segCtr p).step (k, 0) bs.flatten = (rejSt p, m) := by
  intro segs bs h
  induction h with
  | nil => intro hno; exact absurd List.Forall₂.nil hno
  | @cons σ b segs' bs' hhead htail ih =>
      intro hno k hd
      obtain ⟨hσ, hdrop⟩ := drop_cons_aux hd
      rw [List.flatten_cons, List.foldl_append]
      by_cases hs : StructPat.PatSeg.MatchesSeg σ b
      · rw [run_seg_exact h19 hσ hs]
        exact ih (fun hc => hno (List.Forall₂.cons hs hc)) (k + 1) hdrop
      · obtain ⟨m, hm⟩ := run_seg_rej hσ hhead hs
        rw [hm, foldl_rej]
        exact ⟨m, rfl⟩

/-! ## The split is exact -/

/-- **The split of `StructPat.SegMatch` into a relaxed part and a counter part is
exact.**

`h19` is supplied by the payload grammar (`PayAuto.nineteen_not_mem_of_parse`); it is a
hypothesis here so that the fact is not duplicated.

Proof kind: `P` proved.  Provenance: (a) `run_exact`, `run_rej`,
`matchesRelaxed_of_matchesSeg`; (b) `CtrAuto.CtrProgram.Accepts`.
Paper node: `app:ifp` -/
lemma segMatch_iff_relaxed_and_ctr
    (h19 : ∀ {q : List ℕ} {c : ℕ},
      parseStructuredArithmeticFormula q.length 0 q = some (c, []) → 19 ∉ q)
    (p : List StructPat.PatSeg) (b : List ℕ) :
    StructPat.SegMatch p b ↔ SegMatchRelaxed p b ∧ (segCtr p).Accepts b = true := by
  have hrun : ∀ bs : List (List ℕ),
      (segCtr p).run bs.flatten = List.foldl (segCtr p).step (0, 0) bs.flatten :=
    fun _ => rfl
  constructor
  · intro hsm
    refine ⟨segMatch_relaxed_of_segMatch h19 hsm, ?_⟩
    obtain ⟨bs, hf, rfl⟩ := hsm
    have h := run_exact (p := p) h19 hf 0 (by simp)
    rw [CtrProgram.Accepts, hrun bs, h]
    simp [segCtr]
  · rintro ⟨⟨bs, hf, rfl⟩, hacc⟩
    by_contra hno
    have hnf : ¬ List.Forall₂ StructPat.PatSeg.MatchesSeg p bs := fun hc =>
      hno ⟨bs, hc, rfl⟩
    obtain ⟨m, hm⟩ := run_rej (p := p) h19 hf hnf 0 (by simp)
    rw [CtrProgram.Accepts, hrun bs, hm] at hacc
    simp only [segCtr, Bool.and_eq_true, decide_eq_true_eq, rejSt] at hacc
    omega

end SegCtr

end LogicalInduction
