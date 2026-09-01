import LogicalInduction.Construction.Witnesses.ArithmeticSource
import LogicalInduction.Construction.LIACompiler

/-!
# Reading a written formula back from its name

`ArithSource.sourceNat` names a written formula by its own emitted token run
(`tokenListNat`, `Framework/CodeSource.lean`) — the number `def:ec` charges a trader for
writing.  This module inverts that naming and composes the inverse with the structured
grammar of `Framework/Criterion.lean`, giving

* `tokensOfNat`, the token run named by a number, with `tokensOfNat_tokenListNat` the
  round trip and `tokensOfNat_primrec` its computability;
* `negSourceFormulaCode`, which sends the *name of a source* to the Godel code of the
  **negation of the formula that source compiles to**, together with
  `negSourceFormulaCode_computable`.

The negation is taken on the compiled Foundation formula, not on the source — the source
language's `not` constructor is never used here — so that the refutation the `thm:incons`
checker needs (`provable_neg_listConj_of_not_consistent`, `Framework/BoundedConsistency.lean`)
applies at the compiled formula unchanged.

**Why this exists.**  A predicate of *source names* that is r.e. can be represented in
arithmetic by `codeOfREPred`.  `thm:incons` uses this to check a day-theory's finite axiom
window without ever handling a Godel code on the emission side: the machine emits the
*writings* of its axioms, those writings splice into one writing
(`Construction/Witnesses/SourceWindow.lean`), and the code of the formula that writing
denotes is recovered here, inside the represented predicate, where the paper asks only for
recursive enumerability and the code's size is free.  Handing a code to the schema instead
would be fatal: a formula code's digit count is exponential in the parse depth.

Nothing here is efficient and nothing here needs to be: the decoder runs *inside* the
represented predicate, where the paper asks only for recursive enumerability.  The
efficiency claim lives entirely on the emission side, at
`PolyArithmeticSourceSeq.bigDigits_sourceNat`.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Inverting the naming map -/

/-- **The token run named by `v`**: read `v`'s base-`64` digits from the bottom and stop at
the sentinel `63`.  The search range `v + 1` is long enough by `length_lt_tokenListNat`,
and the `foldr` is `List.takeWhile (· ≠ 63)` written in a shape `Primrec.list_foldr`
accepts. -/
def tokensOfNat (v : ℕ) : List ℕ :=
  List.foldr (fun a acc => if a = 63 then [] else a :: acc) []
    ((List.range (v + 1)).map fun i => v / 64 ^ i % 64)

/-- The base-`64` digit window `tokensOfNat` scans. -/
private def digitRun (v : ℕ) : List ℕ :=
  (List.range (v + 1)).map fun i => v / 64 ^ i % 64

private lemma tokensOfNat_eq (v : ℕ) :
    tokensOfNat v =
      List.foldr (fun a acc => if a = 63 then [] else a :: acc) [] (digitRun v) :=
  rfl

private lemma digitRun_length (v : ℕ) : (digitRun v).length = v + 1 := by
  simp [digitRun]

private lemma digitRun_getElem (v n : ℕ) (h : n < (digitRun v).length) :
    getElem (digitRun v) n h = v / 64 ^ n % 64 := by
  simp [digitRun]

/-- The scan stops at the first sentinel, returning the sentinel-free prefix. -/
private lemma foldr_sentinel_append (r : List ℕ) :
    ∀ l : List ℕ, (∀ a ∈ l, a ≠ 63) →
      List.foldr (fun a acc => if a = 63 then [] else a :: acc) [] (l ++ 63 :: r) = l := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      have ha : a ≠ 63 := h a (by simp)
      have hl : ∀ b ∈ l, b ≠ 63 := fun b hb => h b (by simp [hb])
      simp [ha, ih hl]

/-- **The round trip**: the name of a token run decodes back to that run. -/
lemma tokensOfNat_tokenListNat {ts : List ℕ} (hts : ∀ t ∈ ts, t < 63) :
    tokensOfNat (tokenListNat ts) = ts := by
  have hlt : ts.length < tokenListNat ts := length_lt_tokenListNat ts
  have hlen : (digitRun (tokenListNat ts)).length = tokenListNat ts + 1 :=
    digitRun_length _
  have htake : (digitRun (tokenListNat ts)).take (ts.length + 1) = ts ++ [63] := by
    have hlen1 :
        ((digitRun (tokenListNat ts)).take (ts.length + 1)).length = ts.length + 1 := by
      rw [List.length_take, hlen]; omega
    refine List.ext_getElem (by rw [hlen1]; simp) fun n h1 h2 => ?_
    have hnM : n < (digitRun (tokenListNat ts)).length := by
      rw [hlen1] at h1; rw [hlen]; omega
    have hd := tokenListNat_digit hts n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at hd
    rw [List.getElem_take, digitRun_getElem _ _ hnM]
    exact hd
  rw [tokensOfNat_eq]
  conv_lhs => rw [← List.take_append_drop (ts.length + 1) (digitRun (tokenListNat ts))]
  rw [htake, List.append_assoc]
  exact foldr_sentinel_append _ ts fun a ha => Nat.ne_of_lt (hts a ha)

/-- The decoder is primitive recursive. -/
lemma tokensOfNat_primrec : Primrec tokensOfNat := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hdig : Primrec₂ fun v i : ℕ => v / 64 ^ i % 64 :=
    show Primrec fun p : ℕ × ℕ => p.1 / 64 ^ p.2 % 64 from
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp Primrec.fst
          (hpow.comp (Primrec.const 64) Primrec.snd))
        (Primrec.const 64)
  have hrun : Primrec fun v : ℕ => (List.range (v + 1)).map fun i => v / 64 ^ i % 64 :=
    Primrec.list_map (Primrec.list_range.comp Primrec.succ) hdig
  have hstep : Primrec₂ fun (_ : ℕ) (p : ℕ × List ℕ) =>
      if p.1 = 63 then ([] : List ℕ) else p.1 :: p.2 :=
    show Primrec fun x : ℕ × (ℕ × List ℕ) =>
        if x.2.1 = 63 then ([] : List ℕ) else x.2.1 :: x.2.2 from
      Primrec.ite
        (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (Primrec.const 63))
        (Primrec.const [])
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr hrun (Primrec.const []) hstep).of_eq fun _ => rfl

/-! ## From a source name to a formula code -/

/-- **The Godel code of the negation of the formula written down by `v`.**

`v` is read as a token run, the run is parsed by the structured arithmetic grammar — which
performs all normal-form expansion of `¬`, `⟹` and `⟺` off the written stream — and the
resulting formula code is negated by `negFormulaCode`.  A name that is not a complete
well-formed run gets the code `0`, which is provable in no theory — internal derivations
carry the well-formedness of their sequents and internal formulas are positive numbers, so
`not_provableCode_zero` (`Framework/BoundedConsistency.lean`) rules it out.

That fallback is a totality convention, not a soundness guarantee, and **nothing in
`thm:incons` relies on it**: the day-window gate (`AdmissibleName`,
`Construction/Witnesses/SourceWindow.lean`) admits only runs that
`SourceRecognizer.sourceRun` certifies to be the emitted run of a genuine sentence-valued
`ArithSource`, so the spliced run reaching this decoder always parses completely. -/
def negSourceFormulaCode (v : ℕ) : ℕ :=
  match parseStructuredArithmeticFormula (tokensOfNat v).length 0 (tokensOfNat v) with
  | some (c, []) => negFormulaCode c
  | _ => 0

/-- Decoding a written formula is computable — all that `codeOfREPred` consumes. -/
lemma negSourceFormulaCode_computable : Computable negSourceFormulaCode := by
  have hts : Primrec tokensOfNat := tokensOfNat_primrec
  have hparse : Primrec fun v : ℕ =>
      parseStructuredArithmeticFormula (tokensOfNat v).length 0 (tokensOfNat v) :=
    parseStructuredArithmeticFormula_prim.comp (Primrec.list_length.comp hts) hts
  have hinner : Primrec₂ fun (_ : ℕ) (p : ℕ × List ℕ) =>
      if p.2 = ([] : List ℕ) then negFormulaCode p.1 else 0 :=
    show Primrec fun x : ℕ × (ℕ × List ℕ) =>
        if x.2.2 = ([] : List ℕ) then negFormulaCode x.2.1 else 0 from
      Primrec.ite
        (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.snd) (Primrec.const []))
        (negFormulaCode_prim.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 0)
  refine ((Primrec.option_casesOn hparse (Primrec.const 0) hinner).of_eq
    fun v => ?_).to_comp
  rw [negSourceFormulaCode]
  cases hpv :
      parseStructuredArithmeticFormula (tokensOfNat v).length 0 (tokensOfNat v) with
  | none => rfl
  | some p =>
      obtain ⟨c, rest⟩ := p
      cases rest <;> simp

/-- **The specification**: at the name of a source, the decoder returns the code of the
negation of the formula that source compiles to. -/
lemma negSourceFormulaCode_sourceNat {k : ℕ} (s : ArithSource k) :
    negSourceFormulaCode s.sourceNat =
      Encodable.encode (∼ArithSource.compile s) := by
  rw [ArithSource.sourceNat, negSourceFormulaCode,
    tokensOfNat_tokenListNat (ArithSource.sourceTokens_lt_63 s)]
  have hp : parseStructuredArithmeticFormula (ArithSource.sourceTokens s).length 0
      (ArithSource.sourceTokens s) =
      some (Encodable.encode (ArithSource.compile s), []) := by
    have := ArithSource.parseStructuredArithmeticFormula_sourceTokens s []
      (fuel := (ArithSource.sourceTokens s).length) (depth := 0) (le_refl _)
    simpa using this
  rw [hp]
  exact negFormulaCode_spec _

end LogicalInduction

#print axioms LogicalInduction.tokensOfNat_tokenListNat
#print axioms LogicalInduction.tokensOfNat_primrec
#print axioms LogicalInduction.negSourceFormulaCode_computable
#print axioms LogicalInduction.negSourceFormulaCode_sourceNat
