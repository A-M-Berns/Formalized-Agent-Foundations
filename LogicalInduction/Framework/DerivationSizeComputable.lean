import LogicalInduction.Framework.DerivationSize
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

/-!
# The §4.10 symbol measures are primitive recursive

`DerivationSize.lean` defines the symbol measures by well-founded recursion at `ℕ`, which
says nothing about their effectivity. This module supplies the missing half of
`dd:symbolcount`: `tSize`, `tvSize`, `fSize`, `sSize`, `dSize` and `G` are all primitive
recursive, hence computable. Without it the §4.10 bounded proof search is a classical
existence statement rather than an algorithm.

Each well-founded measure recurses only on values strictly below its argument, so each is
obtained from Mathlib's course-of-values recursor `Primrec.nat_strong_rec`: the step
function reads its recursive values out of `(List.range n).map f`, whose `i`-th entry is
`f i` and whose length is `n`. The entries are read with `List.getD`, because `l[i]` cannot
be written where Foundation's binder notation registers `)[` as a token.

`tSize` and `tvSize` share one recursion (`tvAux`), so they are packed into a single
function of `2 * n + mode` before the recursor is applied; every recursive `tvAux` call
strictly decreases that packed value.

`Nat.size` — which `idxLen` counts with — has no primitive-recursiveness lemma in Mathlib,
so it is obtained here by the same recursor from `size n = size (n / 2) + 1`.

`G` recurses structurally over the private squaring function `P`. Privacy restricts name
resolution, not unfolding, so the six-fold iterate is definitionally the explicit tower
`Gstep`, and `G_succ_eq` is `rfl`.

The module closes with the `Computable` forms the §4.10 decider consumes, and with
`computable_boundedSearchValue`: a bounded existential over a computable predicate with a
computable bound is computable. Mathlib offers only the `Primrec` list combinators here, so
the scan is an explicit `Nat.rec` fed to `Computable.nat_rec`. All of it is spent in
`Framework/BoundedConsistency.lean`, to make `bprovValue` total and computable.
-/

namespace LogicalInduction

/-! ## Reading a course-of-values list

`Primrec.nat_strong_rec` hands the step function the list `(List.range n).map f`.  Its
length is `n`, and its `i`-th entry — read with `List.getD`, since `l[i]` cannot be written
in a module that imports Foundation's binder notation, which registers `)[` as a token — is
`f i` for every `i < n`. -/

private lemma getD_range_map (f : ℕ → ℕ) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

/-! ## Primitive-recursion plumbing

Small combinators over `α → ℕ`, so the step functions below can be assembled without
point-free contortions. -/

section Plumbing

variable {α : Type*} [Primcodable α] {c f g : α → ℕ}

private lemma prim_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

private lemma pAdd (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  Primrec₂.comp Primrec.nat_add hf hg

private lemma pMul (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a * g a :=
  Primrec₂.comp Primrec.nat_mul hf hg

private lemma pSub (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a - g a :=
  Primrec₂.comp Primrec.nat_sub hf hg

private lemma pDiv (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a / g a :=
  Primrec₂.comp Primrec.nat_div hf hg

private lemma pMod (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a % g a :=
  Primrec₂.comp Primrec.nat_mod hf hg

private lemma pPow (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a ^ g a :=
  Primrec₂.comp prim_natPow hf hg

private lemma prim_pl : Primrec pl := Primrec.fst.comp Primrec.unpair

private lemma prim_pr : Primrec pr := Primrec.snd.comp Primrec.unpair

private lemma pPl (hf : Primrec f) : Primrec fun a => pl (f a) := prim_pl.comp hf

private lemma pPr (hf : Primrec f) : Primrec fun a => pr (f a) := prim_pr.comp hf

private lemma pIte (k : ℕ) (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = k then f a else g a :=
  Primrec.ite (PrimrecRel.comp Primrec.eq hc (Primrec.const k)) hf hg

private lemma pIte₂ (k k' : ℕ) (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = k ∨ c a = k' then f a else g a :=
  Primrec.ite (PrimrecPred.or (PrimrecRel.comp Primrec.eq hc (Primrec.const k))
    (PrimrecRel.comp Primrec.eq hc (Primrec.const k'))) hf hg

private lemma pGetD {ℓ : α → List ℕ} (hℓ : Primrec ℓ) (hf : Primrec f) :
    Primrec fun a => List.getD (ℓ a) (f a) 0 :=
  Primrec₂.comp (f := fun (l : List ℕ) (n : ℕ) => List.getD l n 0) (Primrec.list_getD 0) hℓ hf

end Plumbing

/-- `Primrec.nat_strong_rec` produces a `Primrec₂` over a dummy parameter; discharge it.
Spelled with `f` supplied explicitly, because leaving it to unification makes Lean unfold
the *goal's* function (`Nat.size` into `Nat.binaryRec`, `tSize` into `tvAux`) instead. -/
private lemma ofDummy {F : ℕ → ℕ} (h : Primrec₂ fun (_ : ℕ) (n : ℕ) => F n) : Primrec F :=
  Primrec₂.comp (f := fun (_ : ℕ) (n : ℕ) => F n) h (Primrec.const 0) Primrec.id

/-! ## `Nat.size`

Mathlib has no `Primrec Nat.size`.  The halving recursion `size n = size (n / 2) + 1` is
course-of-values, so the same recursor that carries the measures carries this too. -/

private lemma size_eq_succ {n : ℕ} (h : n ≠ 0) : Nat.size n = Nat.size (n / 2) + 1 := by
  conv_lhs => rw [← Nat.bit_testBit_zero_shiftRight_one n]
  rw [Nat.size_bit (by rw [Nat.bit_testBit_zero_shiftRight_one]; exact h)]
  simp [Nat.shiftRight_eq_div_pow]

private def gsize (L : List ℕ) : ℕ :=
  if L.length = 0 then 0 else L.getD (L.length / 2) 0 + 1

private lemma prim_gsize : Primrec gsize := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have h : Primrec fun L : List ℕ =>
      if L.length = 0 then 0 else L.getD (L.length / 2) 0 + 1 :=
    pIte 0 hlen (Primrec.const 0)
      (pAdd (pGetD Primrec.id (pDiv hlen (Primrec.const 2))) (Primrec.const 1))
  exact h.of_eq fun _ => rfl

private lemma gsize_correct (n : ℕ) : gsize ((List.range n).map Nat.size) = Nat.size n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gsize]
  · have hlen : ((List.range n).map Nat.size).length = n := by simp
    rw [gsize, hlen, if_neg (by omega), getD_range_map Nat.size (by omega)]
    exact (size_eq_succ (by omega)).symm

private lemma prim_natSize : Primrec Nat.size := by
  have h : Primrec₂ fun (_ : ℕ) (n : ℕ) => Nat.size n :=
    Primrec.nat_strong_rec (fun _ n => Nat.size n)
      (g := fun (_ : ℕ) (L : List ℕ) => some (gsize L))
      (Primrec.option_some.comp (prim_gsize.comp Primrec.snd))
      (fun _ n => congrArg some (gsize_correct n))
  exact ofDummy h

private lemma pIdxLen {α : Type*} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec fun a => idxLen (f a) :=
  pAdd (prim_natSize.comp hf) (Primrec.const 1)

/-! ## Terms and term vectors

`tvAux` is one recursion on two modes.  Packing the mode into the argument as `2 * n + mode`
turns every recursive call into a strict decrease of the packed value, which is what
`Primrec.nat_strong_rec` needs. -/

private def tvPacked (z : ℕ) : ℕ := tvAux (z % 2) (z / 2)

private lemma tvAux_zero (mode : ℕ) : tvAux mode 0 = 0 := by rw [tvAux]

private lemma tvPacked_two_mul (n : ℕ) : tvPacked (2 * n) = tSize n := by
  have h1 : 2 * n % 2 = 0 := by omega
  have h2 : 2 * n / 2 = n := by omega
  rw [tvPacked, h1, h2, tvAux_zero_eq]

private lemma tvPacked_two_mul_succ (n : ℕ) : tvPacked (2 * n + 1) = tvSize n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [tvPacked, h1, h2, tvAux_one_eq]

private def tvBody (m mode : ℕ) (L : List ℕ) : ℕ :=
  if mode = 0 then
    (if arg 0 m = 0 then 1 + idxLen (tail 1 m)
     else if arg 0 m = 1 then 1 + idxLen (tail 1 m)
     else if arg 0 m = 2 then
       1 + idxLen (arg 1 m) + idxLen (arg 2 m) + L.getD (2 * tail 3 m + 1) 0
     else m + 1)
  else 1 + L.getD (2 * arg 0 m) 0 + L.getD (2 * tail 1 m + 1) 0

private def gtv (L : List ℕ) : ℕ :=
  if L.length / 2 = 0 then 0 else tvBody (L.length / 2 - 1) (L.length % 2) L

private lemma prim_tvBody : Primrec fun p : ℕ × ℕ × List ℕ => tvBody p.1 p.2.1 p.2.2 := by
  have hm : Primrec fun p : ℕ × ℕ × List ℕ => p.1 := Primrec.fst
  have hmode : Primrec fun p : ℕ × ℕ × List ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hL : Primrec fun p : ℕ × ℕ × List ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  have h : Primrec fun p : ℕ × ℕ × List ℕ =>
      if p.2.1 = 0 then
        (if pl p.1 = 0 then 1 + idxLen (pr p.1)
         else if pl p.1 = 1 then 1 + idxLen (pr p.1)
         else if pl p.1 = 2 then
           1 + idxLen (pl (pr p.1)) + idxLen (pl (pr (pr p.1)))
             + p.2.2.getD (2 * pr (pr (pr p.1)) + 1) 0
         else p.1 + 1)
      else 1 + p.2.2.getD (2 * pl p.1) 0 + p.2.2.getD (2 * pr p.1 + 1) 0 := by
    refine pIte 0 hmode ?_ ?_
    · refine pIte 0 (pPl hm) (pAdd (Primrec.const 1) (pIdxLen (pPr hm))) ?_
      refine pIte 1 (pPl hm) (pAdd (Primrec.const 1) (pIdxLen (pPr hm))) ?_
      refine pIte 2 (pPl hm) ?_ (pAdd hm (Primrec.const 1))
      exact pAdd (pAdd (pAdd (Primrec.const 1) (pIdxLen (pPl (pPr hm))))
          (pIdxLen (pPl (pPr (pPr hm)))))
        (pGetD hL (pAdd (pMul (Primrec.const 2) (pPr (pPr (pPr hm)))) (Primrec.const 1)))
    · exact pAdd (pAdd (Primrec.const 1) (pGetD hL (pMul (Primrec.const 2) (pPl hm))))
        (pGetD hL (pAdd (pMul (Primrec.const 2) (pPr hm)) (Primrec.const 1)))
  exact h.of_eq fun _ => rfl

private lemma prim_gtv : Primrec gtv := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have hn : Primrec (fun L : List ℕ => L.length / 2) := pDiv hlen (Primrec.const 2)
  have hmode : Primrec (fun L : List ℕ => L.length % 2) := pMod hlen (Primrec.const 2)
  have hm : Primrec (fun L : List ℕ => L.length / 2 - 1) := pSub hn (Primrec.const 1)
  have h : Primrec fun L : List ℕ =>
      if L.length / 2 = 0 then 0 else tvBody (L.length / 2 - 1) (L.length % 2) L :=
    pIte 0 hn (Primrec.const 0)
      (prim_tvBody.comp (Primrec.pair hm (Primrec.pair hmode Primrec.id)))
  exact h.of_eq fun _ => rfl

private lemma gtv_correct (z : ℕ) : gtv ((List.range z).map tvPacked) = tvPacked z := by
  have hlen : ((List.range z).map tvPacked).length = z := by simp
  have hget : ∀ i, i < z → ((List.range z).map tvPacked).getD i 0 = tvPacked i :=
    fun i hi => getD_range_map tvPacked hi
  rw [gtv, hlen]
  by_cases hz : z / 2 = 0
  · rw [if_pos hz, tvPacked, hz, tvAux_zero]
  · rw [if_neg hz]
    obtain ⟨m, hm⟩ : ∃ m, z / 2 = m + 1 := ⟨z / 2 - 1, by omega⟩
    have hz2 : z = 2 * (m + 1) + z % 2 := by omega
    have hmod : z % 2 = 0 ∨ z % 2 = 1 := by omega
    rw [hm, Nat.add_sub_cancel, tvBody, tvPacked, hm]
    rcases hmod with h | h
    · rw [h, if_pos rfl, tvAux_zero_eq, tSize_succ,
        hget (2 * tail 3 m + 1) (by have := tail_le 3 m; omega), tvPacked_two_mul_succ]
    · rw [h, if_neg one_ne_zero, tvAux_succ_of_ne one_ne_zero,
        hget (2 * arg 0 m) (by have := arg_le 0 m; omega),
        hget (2 * tail 1 m + 1) (by have := tail_le 1 m; omega),
        tvPacked_two_mul, tvPacked_two_mul_succ]

private lemma prim_tvPacked : Primrec tvPacked := by
  have h : Primrec₂ fun (_ : ℕ) (z : ℕ) => tvPacked z :=
    Primrec.nat_strong_rec (fun _ z => tvPacked z)
      (g := fun (_ : ℕ) (L : List ℕ) => some (gtv L))
      (Primrec.option_some.comp (prim_gtv.comp Primrec.snd))
      (fun _ z => congrArg some (gtv_correct z))
  exact ofDummy h

/-- The symbol count of a term code is primitive recursive. -/
lemma tSize_primrec : Primrec tSize :=
  (prim_tvPacked.comp (pMul (Primrec.const 2) Primrec.id)).of_eq tvPacked_two_mul

/-- The symbol count of a term-vector code is primitive recursive. -/
lemma tvSize_primrec : Primrec tvSize :=
  (prim_tvPacked.comp (pAdd (pMul (Primrec.const 2) Primrec.id) (Primrec.const 1))).of_eq
    tvPacked_two_mul_succ

/-! ## Formulas -/

private def fBody (m : ℕ) (L : List ℕ) : ℕ :=
  if arg 0 m = 0 ∨ arg 0 m = 1 then
    1 + idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)
  else if arg 0 m = 2 ∨ arg 0 m = 3 then
    (if tail 1 m = 0 then 1 else m + 1)
  else if arg 0 m = 4 ∨ arg 0 m = 5 then
    1 + L.getD (arg 1 m) 0 + L.getD (tail 2 m) 0
  else if arg 0 m = 6 ∨ arg 0 m = 7 then
    1 + L.getD (tail 1 m) 0
  else m + 1

private def gf (L : List ℕ) : ℕ :=
  if L.length = 0 then 0 else fBody (L.length - 1) L

private lemma prim_fBody : Primrec fun p : ℕ × List ℕ => fBody p.1 p.2 := by
  have hm : Primrec fun p : ℕ × List ℕ => p.1 := Primrec.fst
  have hL : Primrec fun p : ℕ × List ℕ => p.2 := Primrec.snd
  have h : Primrec fun p : ℕ × List ℕ =>
      if pl p.1 = 0 ∨ pl p.1 = 1 then
        1 + idxLen (pl (pr p.1)) + idxLen (pl (pr (pr p.1))) + tvSize (pr (pr (pr p.1)))
      else if pl p.1 = 2 ∨ pl p.1 = 3 then (if pr p.1 = 0 then 1 else p.1 + 1)
      else if pl p.1 = 4 ∨ pl p.1 = 5 then
        1 + p.2.getD (pl (pr p.1)) 0 + p.2.getD (pr (pr p.1)) 0
      else if pl p.1 = 6 ∨ pl p.1 = 7 then 1 + p.2.getD (pr p.1) 0
      else p.1 + 1 := by
    refine pIte₂ 0 1 (pPl hm) ?_ ?_
    · exact pAdd (pAdd (pAdd (Primrec.const 1) (pIdxLen (pPl (pPr hm))))
        (pIdxLen (pPl (pPr (pPr hm))))) (tvSize_primrec.comp (pPr (pPr (pPr hm))))
    refine pIte₂ 2 3 (pPl hm) (pIte 0 (pPr hm) (Primrec.const 1) (pAdd hm (Primrec.const 1))) ?_
    refine pIte₂ 4 5 (pPl hm) ?_ ?_
    · exact pAdd (pAdd (Primrec.const 1) (pGetD hL (pPl (pPr hm)))) (pGetD hL (pPr (pPr hm)))
    refine pIte₂ 6 7 (pPl hm) ?_ (pAdd hm (Primrec.const 1))
    exact pAdd (Primrec.const 1) (pGetD hL (pPr hm))
  exact h.of_eq fun _ => rfl

private lemma prim_gf : Primrec gf := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have h : Primrec fun L : List ℕ => if L.length = 0 then 0 else fBody (L.length - 1) L :=
    pIte 0 hlen (Primrec.const 0)
      (prim_fBody.comp (Primrec.pair (pSub hlen (Primrec.const 1)) Primrec.id))
  exact h.of_eq fun _ => rfl

private lemma gf_correct (n : ℕ) : gf ((List.range n).map fSize) = fSize n := by
  match n with
  | 0 => simp [gf, fSize]
  | (m + 1) =>
    have hlen : ((List.range (m + 1)).map fSize).length = m + 1 := by simp
    have hget : ∀ i, i < m + 1 → ((List.range (m + 1)).map fSize).getD i 0 = fSize i :=
      fun i hi => getD_range_map fSize hi
    rw [gf, hlen, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, fBody, fSize,
      hget (arg 1 m) (arg_lt_succ 1 m), hget (tail 2 m) (tail_lt_succ 2 m),
      hget (tail 1 m) (tail_lt_succ 1 m)]

/-- The symbol count of a formula code is primitive recursive. -/
lemma fSize_primrec : Primrec fSize := by
  have h : Primrec₂ fun (_ : ℕ) (n : ℕ) => fSize n :=
    Primrec.nat_strong_rec (fun _ n => fSize n)
      (g := fun (_ : ℕ) (L : List ℕ) => some (gf L))
      (Primrec.option_some.comp (prim_gf.comp Primrec.snd))
      (fun _ n => congrArg some (gf_correct n))
  exact ofDummy h

/-! ## Sequents

`sSize` is not recursive: it is a bounded sum over the already-computable `fSize`.  A
`List.foldl` over `List.range` is the shape `Primrec.list_foldl` wants, and it is the shape
`Finset.sum_range_succ` matches, since `List.range (t + 1) = List.range t ++ [t]`. -/

private lemma sSize_eq_foldl (s : ℕ) :
    sSize s =
      (List.range s).foldl (fun acc i => acc + if s / 2 ^ i % 2 = 1 then fSize i else 0) 0 := by
  suffices h : ∀ t : ℕ, (∑ i ∈ Finset.range t, if s.testBit i then fSize i else 0) =
      (List.range t).foldl (fun acc i => acc + if s / 2 ^ i % 2 = 1 then fSize i else 0) 0 by
    rw [sSize]; exact h s
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_append]
      simp [Nat.testBit_eq_decide_div_mod_eq]

/-- The symbol count of a sequent code is primitive recursive. -/
lemma sSize_primrec : Primrec sSize := by
  have hstep : Primrec fun q : ℕ × ℕ × ℕ =>
      q.2.1 + if q.1 / 2 ^ q.2.2 % 2 = 1 then fSize q.2.2 else 0 := by
    have hs : Primrec fun q : ℕ × ℕ × ℕ => q.1 := Primrec.fst
    have hacc : Primrec fun q : ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
    have hi : Primrec fun q : ℕ × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
    exact pAdd hacc
      (pIte 1 (pMod (pDiv hs (pPow (Primrec.const 2) hi)) (Primrec.const 2))
        (fSize_primrec.comp hi) (Primrec.const 0))
  have h : Primrec fun s : ℕ =>
      (List.range s).foldl (fun acc i => acc + if s / 2 ^ i % 2 = 1 then fSize i else 0) 0 :=
    Primrec.list_foldl (h := fun (s : ℕ) (q : ℕ × ℕ) =>
        q.1 + if s / 2 ^ q.2 % 2 = 1 then fSize q.2 else 0)
      Primrec.list_range (Primrec.const 0) hstep
  exact h.of_eq fun s => (sSize_eq_foldl s).symm

/-! ## Derivations -/

private def dBody (m : ℕ) (L : List ℕ) : ℕ :=
  if arg 1 m = 0 then 1 + sSize (arg 0 m) + fSize (tail 2 m)
  else if arg 1 m = 1 then
    (if tail 2 m = 0 then 1 + sSize (arg 0 m) else m + 1)
  else if arg 1 m = 2 then
    1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
      + L.getD (arg 4 m) 0 + L.getD (tail 5 m) 0
  else if arg 1 m = 3 then
    1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m) + L.getD (tail 4 m) 0
  else if arg 1 m = 4 then
    1 + sSize (arg 0 m) + fSize (arg 2 m) + L.getD (tail 3 m) 0
  else if arg 1 m = 5 then
    1 + sSize (arg 0 m) + fSize (arg 2 m) + tSize (arg 3 m) + L.getD (tail 4 m) 0
  else if arg 1 m = 6 ∨ arg 1 m = 7 then
    1 + sSize (arg 0 m) + L.getD (tail 2 m) 0
  else if arg 1 m = 8 then
    1 + sSize (arg 0 m) + fSize (arg 2 m) + L.getD (arg 3 m) 0 + L.getD (tail 4 m) 0
  else if arg 1 m = 9 then 1 + sSize (arg 0 m) + fSize (tail 2 m)
  else m + 1

private def gd (L : List ℕ) : ℕ :=
  if L.length = 0 then 0 else dBody (L.length - 1) L

private lemma prim_dBody : Primrec fun p : ℕ × List ℕ => dBody p.1 p.2 := by
  have hm : Primrec fun p : ℕ × List ℕ => p.1 := Primrec.fst
  have hL : Primrec fun p : ℕ × List ℕ => p.2 := Primrec.snd
  have hs : Primrec fun p : ℕ × List ℕ => sSize (pl p.1) := sSize_primrec.comp (pPl hm)
  have htag : Primrec fun p : ℕ × List ℕ => pl (pr p.1) := pPl (pPr hm)
  have h : Primrec fun p : ℕ × List ℕ =>
      if pl (pr p.1) = 0 then 1 + sSize (pl p.1) + fSize (pr (pr p.1))
      else if pl (pr p.1) = 1 then
        (if pr (pr p.1) = 0 then 1 + sSize (pl p.1) else p.1 + 1)
      else if pl (pr p.1) = 2 then
        1 + sSize (pl p.1) + fSize (pl (pr (pr p.1))) + fSize (pl (pr (pr (pr p.1))))
          + p.2.getD (pl (pr (pr (pr (pr p.1))))) 0 + p.2.getD (pr (pr (pr (pr (pr p.1))))) 0
      else if pl (pr p.1) = 3 then
        1 + sSize (pl p.1) + fSize (pl (pr (pr p.1))) + fSize (pl (pr (pr (pr p.1))))
          + p.2.getD (pr (pr (pr (pr p.1)))) 0
      else if pl (pr p.1) = 4 then
        1 + sSize (pl p.1) + fSize (pl (pr (pr p.1))) + p.2.getD (pr (pr (pr p.1))) 0
      else if pl (pr p.1) = 5 then
        1 + sSize (pl p.1) + fSize (pl (pr (pr p.1))) + tSize (pl (pr (pr (pr p.1))))
          + p.2.getD (pr (pr (pr (pr p.1)))) 0
      else if pl (pr p.1) = 6 ∨ pl (pr p.1) = 7 then
        1 + sSize (pl p.1) + p.2.getD (pr (pr p.1)) 0
      else if pl (pr p.1) = 8 then
        1 + sSize (pl p.1) + fSize (pl (pr (pr p.1))) + p.2.getD (pl (pr (pr (pr p.1)))) 0
          + p.2.getD (pr (pr (pr (pr p.1)))) 0
      else if pl (pr p.1) = 9 then 1 + sSize (pl p.1) + fSize (pr (pr p.1))
      else p.1 + 1 := by
    refine pIte 0 htag
      (pAdd (pAdd (Primrec.const 1) hs) (fSize_primrec.comp (pPr (pPr hm)))) ?_
    refine pIte 1 htag
      (pIte 0 (pPr (pPr hm)) (pAdd (Primrec.const 1) hs) (pAdd hm (Primrec.const 1))) ?_
    refine pIte 2 htag ?_ ?_
    · exact pAdd (pAdd (pAdd (pAdd (pAdd (Primrec.const 1) hs)
        (fSize_primrec.comp (pPl (pPr (pPr hm)))))
        (fSize_primrec.comp (pPl (pPr (pPr (pPr hm))))))
        (pGetD hL (pPl (pPr (pPr (pPr (pPr hm))))))) (pGetD hL (pPr (pPr (pPr (pPr (pPr hm))))))
    refine pIte 3 htag ?_ ?_
    · exact pAdd (pAdd (pAdd (pAdd (Primrec.const 1) hs)
        (fSize_primrec.comp (pPl (pPr (pPr hm)))))
        (fSize_primrec.comp (pPl (pPr (pPr (pPr hm))))))
        (pGetD hL (pPr (pPr (pPr (pPr hm)))))
    refine pIte 4 htag ?_ ?_
    · exact pAdd (pAdd (pAdd (Primrec.const 1) hs)
        (fSize_primrec.comp (pPl (pPr (pPr hm))))) (pGetD hL (pPr (pPr (pPr hm))))
    refine pIte 5 htag ?_ ?_
    · exact pAdd (pAdd (pAdd (pAdd (Primrec.const 1) hs)
        (fSize_primrec.comp (pPl (pPr (pPr hm)))))
        (tSize_primrec.comp (pPl (pPr (pPr (pPr hm))))))
        (pGetD hL (pPr (pPr (pPr (pPr hm)))))
    refine pIte₂ 6 7 htag
      (pAdd (pAdd (Primrec.const 1) hs) (pGetD hL (pPr (pPr hm)))) ?_
    refine pIte 8 htag ?_ ?_
    · exact pAdd (pAdd (pAdd (pAdd (Primrec.const 1) hs)
        (fSize_primrec.comp (pPl (pPr (pPr hm)))))
        (pGetD hL (pPl (pPr (pPr (pPr hm)))))) (pGetD hL (pPr (pPr (pPr (pPr hm)))))
    exact pIte 9 htag
      (pAdd (pAdd (Primrec.const 1) hs) (fSize_primrec.comp (pPr (pPr hm))))
      (pAdd hm (Primrec.const 1))
  exact h.of_eq fun _ => rfl

-- `dBody` is a ten-branch case split; the defeq check against `gd` is large but finite.
set_option maxHeartbeats 1000000 in
private lemma prim_gd : Primrec gd := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have h : Primrec fun L : List ℕ => if L.length = 0 then 0 else dBody (L.length - 1) L :=
    pIte 0 hlen (Primrec.const 0)
      (prim_dBody.comp (Primrec.pair (pSub hlen (Primrec.const 1)) Primrec.id))
  exact h.of_eq fun _ => rfl

private lemma gd_correct (n : ℕ) : gd ((List.range n).map dSize) = dSize n := by
  match n with
  | 0 => simp [gd, dSize]
  | (m + 1) =>
    have hlen : ((List.range (m + 1)).map dSize).length = m + 1 := by simp
    have hget : ∀ i, i < m + 1 → ((List.range (m + 1)).map dSize).getD i 0 = dSize i :=
      fun i hi => getD_range_map dSize hi
    rw [gd, hlen, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, dBody, dSize,
      hget (arg 4 m) (arg_lt_succ 4 m), hget (tail 5 m) (tail_lt_succ 5 m),
      hget (tail 4 m) (tail_lt_succ 4 m), hget (tail 3 m) (tail_lt_succ 3 m),
      hget (tail 2 m) (tail_lt_succ 2 m), hget (arg 3 m) (arg_lt_succ 3 m)]

/-- The symbol count of a derivation code is primitive recursive: the §4.10 bounded search
is a genuine algorithm. -/
lemma dSize_primrec : Primrec dSize := by
  have h : Primrec₂ fun (_ : ℕ) (n : ℕ) => dSize n :=
    Primrec.nat_strong_rec (fun _ n => dSize n)
      (g := fun (_ : ℕ) (L : List ℕ) => some (gd L))
      (Primrec.option_some.comp (prim_gd.comp Primrec.snd))
      (fun _ n => congrArg some (gd_correct n))
  exact ofDummy h

/-! ## The bounding function

`G` recurses structurally, but its step is written with the `private` squaring `P`, whose
name is not available outside `DerivationSize.lean`.  Privacy restricts name resolution,
not unfolding, so the six-fold iterate is still *definitionally* the explicit tower below
and `G_succ_eq` holds by `rfl`. -/

private def Gstep (x : ℕ) : ℕ :=
  ((((((2 ^ (x + 1) + 9 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2

private lemma G_succ_eq (N : ℕ) : G (N + 1) = Gstep (G N) := rfl

/-- The bounding function of the converse bound `d ≤ G (dSize d)` is primitive recursive,
which is what makes the bounded search `d ≤ G k` decidable in both polarities. -/
lemma G_primrec : Primrec G := by
  have hstep : Primrec Gstep := by
    have e0 : Primrec fun x : ℕ => 2 ^ (x + 1) + 9 + 1 :=
      pAdd (pAdd (pPow (Primrec.const 2) (pAdd Primrec.id (Primrec.const 1)))
        (Primrec.const 9)) (Primrec.const 1)
    have e1 := pPow e0 (Primrec.const 2)
    have e2 := pPow (pAdd e1 (Primrec.const 1)) (Primrec.const 2)
    have e3 := pPow (pAdd e2 (Primrec.const 1)) (Primrec.const 2)
    have e4 := pPow (pAdd e3 (Primrec.const 1)) (Primrec.const 2)
    have e5 := pPow (pAdd e4 (Primrec.const 1)) (Primrec.const 2)
    have e6 := pPow (pAdd e5 (Primrec.const 1)) (Primrec.const 2)
    exact e6.of_eq fun _ => rfl
  have h := Primrec.nat_rec₁ (f := fun (_ : ℕ) (x : ℕ) => Gstep x) 1
    (hstep.comp Primrec.snd)
  refine h.of_eq fun N => ?_
  induction N with
  | zero => rfl
  | succ N ih => rw [G_succ_eq, ← ih]

/-! ## Computability

The `Computable` forms are what the §4.10 decider consumes. -/

/-- **`G` is computable.** -/
lemma G_computable : Computable G := G_primrec.to_comp

/-- **The symbol count of a term code is computable.** -/
lemma tSize_computable : Computable tSize := tSize_primrec.to_comp

/-- **The symbol count of a term-vector code is computable.** -/
lemma tvSize_computable : Computable tvSize := tvSize_primrec.to_comp

/-- **The symbol count of a formula code is computable.** -/
lemma fSize_computable : Computable fSize := fSize_primrec.to_comp

/-- **The symbol count of a sequent code is computable.** -/
lemma sSize_computable : Computable sSize := sSize_primrec.to_comp

/-- **The symbol count of a derivation code is computable.** -/
lemma dSize_computable : Computable dSize := dSize_primrec.to_comp

/-! ## Bounded search over a computable predicate

The shape §4.10 needs: a bounded existential over a computable binary predicate, with a
computable bound, is computable.  Mathlib has no `Computable.list_map` or
`Computable.list_foldr` — only the `Primrec` versions — so the scan is written as an
explicit `Nat.rec` over the bound and fed to `Computable.nat_rec`. -/

section BoundedSearch

variable {p : ℕ → ℕ → Prop} [∀ a d : ℕ, Decidable (p a d)]

/-- Scanning `d = 0, …, n - 1` for a witness returns `1` exactly when one exists below `n`.
Stated over the raw `Nat.rec` that `Computable.nat_rec` produces. -/
private lemma scan_eq (a : ℕ) : ∀ n : ℕ,
    Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => if p a y then 1 else IH) n =
      if ∃ d < n, p a d then 1 else 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      show (if p a n then 1 else
        Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => if p a y then 1 else IH) n) = _
      rw [ih]
      by_cases hn : p a n
      · rw [if_pos hn, if_pos ⟨n, Nat.lt_succ_self n, hn⟩]
      · have hnex : (∃ d < n, p a d) ↔ ∃ d < n + 1, p a d := by
          constructor
          · rintro ⟨d, hd, hpd⟩; exact ⟨d, by omega, hpd⟩
          · rintro ⟨d, hd, hpd⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h | rfl
            · exact ⟨d, h, hpd⟩
            · exact absurd hpd hn
        rw [if_neg hn]
        exact if_congr hnex rfl rfl

set_option maxHeartbeats 1000000 in
/-- **A bounded existential over a computable predicate is computable.**  With a computable
bound `b`, deciding "some `d ≤ b a` satisfies `p a d`" is a genuine algorithm. -/
lemma computable_boundedSearchValue
    (hp : Computable fun x : ℕ × ℕ => decide (p x.1 x.2))
    {b : ℕ → ℕ} (hb : Computable b) :
    Computable fun a => if ∃ d ≤ b a, p a d then 1 else 0 := by
  have hstep : Computable₂ fun (a : ℕ) (r : ℕ × ℕ) => if p a r.1 then 1 else r.2 := by
    have hfst : Computable fun z : ℕ × ℕ × ℕ => z.1 := Computable.fst
    have hy : Computable fun z : ℕ × ℕ × ℕ => z.2.1 := Computable.fst.comp Computable.snd
    have hIH : Computable fun z : ℕ × ℕ × ℕ => z.2.2 := Computable.snd.comp Computable.snd
    have hpair : Computable fun z : ℕ × ℕ × ℕ => ((z.1, z.2.1) : ℕ × ℕ) :=
      Computable.pair hfst hy
    have hc : Computable fun z : ℕ × ℕ × ℕ => decide (p z.1 z.2.1) := hp.comp hpair
    have hone : Computable fun _ : ℕ × ℕ × ℕ => (1 : ℕ) := Computable.const 1
    have hcond : Computable fun z : ℕ × ℕ × ℕ =>
        cond (decide (p z.1 z.2.1)) 1 z.2.2 := Computable.cond hc hone hIH
    exact hcond.of_eq fun _ => Bool.cond_decide _ _ _
  have hzero : Computable fun _ : ℕ => (0 : ℕ) := Computable.const 0
  have hsucc : Computable fun a : ℕ => Nat.succ (b a) := Computable.succ.comp hb
  have hscan := Computable.nat_rec (σ := ℕ) hsucc hzero hstep
  refine hscan.of_eq fun a => ?_
  rw [scan_eq a (b a + 1)]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨d, hd, hpd⟩; exact ⟨d, by omega, hpd⟩
  · rintro ⟨d, hd, hpd⟩; exact ⟨d, by omega, hpd⟩

end BoundedSearch

end LogicalInduction
