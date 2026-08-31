import LogicalInduction.Construction.Witnesses.SourceNumbering
import LogicalInduction.Construction.Witnesses.SourceRecognizer

/-!
# Splicing a day's written axioms into one written conjunction

A day-theory is presented by a machine that *writes down* its axioms: it emits, on each
input it halts on, the `ArithSource.sourceNat` name of one written formula.  To speak
about the whole day at once — and in particular about the *inconsistency* of the day's
axioms — those separate written runs must be joined into a single written formula, and
the join must be visible on the emitted stream rather than reconstructed from what the
runs denote.

That is all this module does.  `combineTokens` splices a list of source *names* into one
token run by prefixing the `.and` tag `15` and concatenating the decoded runs; the splice
is pure list surgery, so `combineTokens_map_sourceNat` identifies it with the emitted run
of the right-nested conjunction `conjSource`, and `compile_conjSource` says what that
conjunction denotes.  `axiomWindow` then packages the finite window a day actually sees —
machine `z`, budget and input list packed into `w` — with a diverging input contributing
the inert `⊤`, and `negWindowCode` names the Godel code of the negation of the window's
conjunction, which is the argument the represented predicate of `thm:incons` is
instantiated at.

**The per-entry gate, and why the splice needs one.**  Splicing is list surgery, so it is
blind to what the pieces are: nothing in `combineTokens` stops two *incomplete* runs from
concatenating into one complete run, and nothing in `tokensOfNat` — which stops at the
first sentinel — stops a number that is no name at all from decoding like a short one.
Ungated, both make a machine whose theory is *empty* satisfy the represented predicate.
So `axiomWindow` admits an output only if it passes `AdmissibleName`: the number is
literally the name of its own decoded run, and that run is the complete emitted run of one
`ArithSource 0` whose compiled form is a *sentence* (`SourceRecognizer.sourceRun`).  An
output failing either test contributes the inert `⊤` instead of itself.  The gate is what
makes `exists_sources_axiomWindow` true — *every* window, at every argument, is literally
`ss.map ArithSource.sourceNat` for genuine sentence-valued sources `ss`, each either
emitted by the machine or the inert filler — and that in turn is what makes the represented
predicate say exactly what the `dd:machinetheory` convention claims it says.

Everything here is primitive recursive save the last step, which inherits
`negSourceFormulaCode`'s `Computable`.  As in `SourceNumbering.lean`, none of it is
efficient and none of it needs to be: it runs *inside* a represented predicate, where the
paper asks only for recursive enumerability.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Splicing written sources -/

/-- The written form of `⊤`, the inert filler for a diverging machine. -/
def verumSourceNat : ℕ := (ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0)).sourceNat

/-- **Splice a list of written sources into the written form of their conjunction.**
`15` is `ArithSource.sourceTokens`' `.and` tag, so this is pure list surgery on the
emitted runs; the empty list splices to the run of `⊤`.  Written as a `foldr` because
that is the shape `Primrec.list_foldr` accepts — see `combineTokens_nil` and
`combineTokens_cons` for the defining equations. -/
def combineTokens (vs : List ℕ) : List ℕ :=
  vs.foldr (fun v acc => 15 :: (tokensOfNat v ++ acc))
    (encodeArithmeticFormulaSymbols (⊤ : ArithmeticSemiformula ℕ 0))

@[simp] lemma combineTokens_nil :
    combineTokens [] = encodeArithmeticFormulaSymbols (⊤ : ArithmeticSemiformula ℕ 0) :=
  rfl

@[simp] lemma combineTokens_cons (v : ℕ) (vs : List ℕ) :
    combineTokens (v :: vs) = 15 :: (tokensOfNat v ++ combineTokens vs) :=
  rfl

/-- **The name of the spliced run**, read as a numeral by the same map that names any
written formula. -/
def combineSourceNats (vs : List ℕ) : ℕ := tokenListNat (combineTokens vs)

/-- **The conjunction of a list of sources**, right-nested onto `⊤`.  This is a source,
not a Foundation formula: the `.and` nodes are the paper's own connective, and the
normal-form expansion happens later, in `ArithSource.compile`. -/
def conjSource : List (ArithSource 0) → ArithSource 0
  | [] => .leaf (⊤ : ArithmeticSemiformula ℕ 0)
  | s :: ss => .and s (conjSource ss)

/-- **Splicing written sources writes their conjunction**: the spliced token run is
literally the run `conjSource` emits.  The cons step is the round trip
`tokensOfNat_tokenListNat` at the source alphabet. -/
lemma combineTokens_map_sourceNat (ss : List (ArithSource 0)) :
    combineTokens (ss.map ArithSource.sourceNat)
      = ArithSource.sourceTokens (conjSource ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      have hs : tokensOfNat (ArithSource.sourceNat s) = ArithSource.sourceTokens s := by
        rw [ArithSource.sourceNat]
        exact tokensOfNat_tokenListNat (ArithSource.sourceTokens_lt_63 s)
      simp only [List.map_cons, combineTokens_cons, hs, ih]
      rfl

/-- …and hence **names** it: the spliced name is the name of the conjunction. -/
lemma combineSourceNats_map_sourceNat (ss : List (ArithSource 0)) :
    combineSourceNats (ss.map ArithSource.sourceNat) = (conjSource ss).sourceNat := by
  rw [combineSourceNats, combineTokens_map_sourceNat, ArithSource.sourceNat]

/-- **What the conjunction of sources denotes**: the right-nested Foundation conjunction
of what the pieces denote, closed by `⊤`. -/
lemma compile_conjSource (ss : List (ArithSource 0)) :
    ArithSource.compile (conjSource ss)
      = ss.foldr (fun s acc => ArithSource.compile s ⋏ acc)
          (⊤ : ArithmeticSemiformula ℕ 0) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [conjSource, ArithSource.compile, List.foldr_cons, ih]

/-! ## The per-entry gate -/

/-- **A number is an *admissible name* when it names a written sentence.**  Two decidable
tests, both required:

* the **exact-name** test `tokenListNat (tokensOfNat v) = v`.  `tokensOfNat` reads `v`'s
  base-`64` digits up to the first sentinel, so a number carrying digits at or above the
  sentinel decodes like a shorter number; requiring the decoded run to name `v` back admits
  only numbers that *are* the name of their own run.
* the **complete-source** test `sourceRun (tokensOfNat v).length 0 (tokensOfNat v) = some []`.
  The run is the entire emitted run of one `ArithSource 0` — no remainder — and that source's
  compiled form is a sentence: `sourceRun` tracks binder depth and rejects free variables,
  which is exactly what `parseStructuredArithmeticFormula` does not do.

*Proof kind:* `Def`. -/
def AdmissibleName (v : ℕ) : Prop :=
  tokenListNat (tokensOfNat v) = v ∧
    sourceRun (tokensOfNat v).length 0 (tokensOfNat v) = some []

instance : DecidablePred AdmissibleName := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- **The gate itself**: an admissible name passes through, anything else contributes the
inert `⊤`. -/
def gateName (v : ℕ) : ℕ := if AdmissibleName v then v else verumSourceNat

/-- **What the gate certifies.**  An admissible name is the name of a written source whose
compiled form is a sentence — the property the whole `thm:incons` window rests on.

Kind `C` (composition).  Provenance: (a) `exists_source_of_sourceRun`
(`Construction/Witnesses/SourceRecognizer.lean`) derived in-project. -/
lemma exists_source_of_admissibleName {v : ℕ} (h : AdmissibleName v) :
    ∃ (s : ArithSource 0) (σ : ArithmeticSentence),
      ArithSource.sourceNat s = v ∧
        ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0) := by
  obtain ⟨hname, hrun⟩ := h
  obtain ⟨s, τ, hts, hc⟩ := exists_source_of_sourceRun hrun
  refine ⟨s, τ, ?_, hc⟩
  rw [ArithSource.sourceNat, ← hname]
  congr 1
  simpa using hts.symm

/-- **The gate accepts every genuine written sentence.**  Nothing the convention means to
admit is turned away, so the truth direction of `thm:incons` is untouched by the gate.

Kind `C` (composition).  Provenance: (a) `tokensOfNat_tokenListNat`,
`sourceRun_sourceTokens` derived in-project. -/
lemma admissibleName_sourceNat {s : ArithSource 0} {σ : ArithmeticSentence}
    (hc : ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0)) :
    AdmissibleName (ArithSource.sourceNat s) := by
  have hts : tokensOfNat (ArithSource.sourceNat s) = ArithSource.sourceTokens s := by
    rw [ArithSource.sourceNat]
    exact tokensOfNat_tokenListNat (ArithSource.sourceTokens_lt_63 s)
  refine ⟨by rw [hts, ArithSource.sourceNat], ?_⟩
  rw [hts]
  simpa using sourceRun_sourceTokens s hc [] le_rfl

/-- A genuine written sentence passes the gate unchanged. -/
lemma gateName_sourceNat {s : ArithSource 0} {σ : ArithmeticSentence}
    (hc : ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0)) :
    gateName (ArithSource.sourceNat s) = ArithSource.sourceNat s :=
  if_pos (admissibleName_sourceNat hc)

@[simp] lemma compile_leaf_verum :
    ArithSource.compile (ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0))
      = (↑(⊤ : ArithmeticSentence) : ArithmeticSemiformula ℕ 0) := by
  simp [ArithSource.compile]

@[simp] lemma gateName_verumSourceNat : gateName verumSourceNat = verumSourceNat :=
  gateName_sourceNat (σ := (⊤ : ArithmeticSentence)) compile_leaf_verum

/-- Every gated value is the name of a written sentence — the filler included. -/
lemma exists_source_gateName (v : ℕ) :
    ∃ (s : ArithSource 0) (σ : ArithmeticSentence),
      ArithSource.sourceNat s = gateName v ∧
        ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0) := by
  by_cases h : AdmissibleName v
  · rw [gateName, if_pos h]; exact exists_source_of_admissibleName h
  · exact ⟨ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0), ⊤,
      by rw [gateName, if_neg h]; rfl, compile_leaf_verum⟩

/-! ## The day's axiom window -/

/-- **The day's axiom window**: the machine named by `z` run for `w.unpair.1` steps on
each input in the list named by `w.unpair.2`, a diverging *or inadmissible* output
contributing the inert `verumSourceNat`.  The result is the list of *names of written
sentences* the day has actually seen, which is the finite object `combineSourceNats`
splices. -/
def axiomWindow (z w : ℕ) : List ℕ :=
  (Denumerable.ofNat (List ℕ) w.unpair.2).map fun i =>
    gateName (((Nat.Partrec.Code.ofSource z).evaln w.unpair.1 i).getD verumSourceNat)

/-- The inert filler names only `⊤`: a written source named `verumSourceNat` compiles to
`⊤`, because sources with the same emitted run compile to the same formula. -/
private lemma eq_verum_of_sourceNat_eq_verum {s : ArithSource 0} {σ : ArithmeticSentence}
    (hc : ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0))
    (h : ArithSource.sourceNat s = verumSourceNat) : σ = ⊤ := by
  have htok : ArithSource.sourceTokens s
      = ArithSource.sourceTokens (ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0)) := by
    by_contra hne
    exact ArithSource.sourceNat_ne_of_sourceTokens_ne hne h
  have h2 := ArithSource.compile_eq_of_sourceTokens_eq htok
  rw [hc, compile_leaf_verum] at h2
  exact Rewriting.emb_injective h2

/-- **Every window is a list of written sentences**, and every entry is either one the
machine actually emitted or the inert `⊤`.  This is the gate's whole payload: it holds at
*every* argument `z`, `w`, with no hypothesis on the machine, which is what turns the
represented predicate into a statement about the presented theory rather than about the
emitted stream.

Kind `P` (proved).  Provenance: (a) derived in-project from `exists_source_gateName` and
`ArithSource.compile_eq_of_sourceTokens_eq`. -/
lemma exists_sources_axiomWindow (z w : ℕ) :
    ∃ ss : List (ArithSource 0),
      axiomWindow z w = ss.map ArithSource.sourceNat ∧
        ∀ s ∈ ss, ∃ σ : ArithmeticSentence,
          ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0) ∧
            (σ = ⊤ ∨ ∃ i, (Nat.Partrec.Code.ofSource z).evaln w.unpair.1 i
              = some (ArithSource.sourceNat s)) := by
  rw [axiomWindow]
  induction Denumerable.ofNat (List ℕ) w.unpair.2 with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons i is ih =>
      obtain ⟨ss, hmap, hall⟩ := ih
      obtain ⟨s, σ, hname, hc⟩ := exists_source_gateName
        (((Nat.Partrec.Code.ofSource z).evaln w.unpair.1 i).getD verumSourceNat)
      refine ⟨s :: ss, by simp [hmap, hname], ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with heq | ht'
      · subst heq
        refine ⟨σ, hc, ?_⟩
        by_cases hadm : AdmissibleName
            (((Nat.Partrec.Code.ofSource z).evaln w.unpair.1 i).getD verumSourceNat)
        · rcases hev : (Nat.Partrec.Code.ofSource z).evaln w.unpair.1 i with _ | v
          · left
            rw [hev] at hname hadm
            simp only [Option.getD_none] at hname hadm
            rw [gateName, if_pos hadm] at hname
            exact eq_verum_of_sourceNat_eq_verum hc hname
          · right
            rw [hev] at hname hadm
            simp only [Option.getD_some] at hname hadm
            rw [gateName, if_pos hadm] at hname
            exact ⟨i, by rw [hev, hname]⟩
        · left
          rw [gateName, if_neg hadm] at hname
          exact eq_verum_of_sourceNat_eq_verum hc hname
      · exact hall t ht'

/-- **The Godel code of the negation of the day-window conjunction** — the argument at
which the represented inconsistency predicate is instantiated. -/
def negWindowCode (z w : ℕ) : ℕ :=
  negSourceFormulaCode (combineSourceNats (axiomWindow z w))

/-! ## Computability -/

/-- The splice is primitive recursive. -/
lemma combineTokens_primrec : Primrec combineTokens := by
  have hstep : Primrec₂ fun (_ : List ℕ) (p : ℕ × List ℕ) =>
      15 :: (tokensOfNat p.1 ++ p.2) :=
    show Primrec fun x : List ℕ × (ℕ × List ℕ) =>
        15 :: (tokensOfNat x.2.1 ++ x.2.2) from
      Primrec.list_cons.comp (Primrec.const 15)
        (Primrec.list_append.comp
          (tokensOfNat_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id
    (Primrec.const (encodeArithmeticFormulaSymbols (⊤ : ArithmeticSemiformula ℕ 0)))
    hstep).of_eq fun _ => rfl

/-- The name of the splice is primitive recursive. -/
lemma combineSourceNats_primrec : Primrec combineSourceNats :=
  tokenListNat_primrec.comp combineTokens_primrec

/-- Admissibility is decidable primitively recursively: both tests are. -/
lemma admissibleName_primrec : PrimrecPred AdmissibleName := by
  have h1 : PrimrecPred fun v : ℕ => tokenListNat (tokensOfNat v) = v :=
    PrimrecRel.comp Primrec.eq
      (tokenListNat_primrec.comp tokensOfNat_primrec) Primrec.id
  have h2 : PrimrecPred fun v : ℕ =>
      sourceRun (tokensOfNat v).length 0 (tokensOfNat v) = some ([] : List ℕ) :=
    ⟨inferInstance, sourceRun_full_prim.comp tokensOfNat_primrec⟩
  exact h1.and h2

/-- The gate is primitive recursive. -/
lemma gateName_primrec : Primrec gateName :=
  Primrec.ite admissibleName_primrec Primrec.id (Primrec.const verumSourceNat)

/-- The day window is primitive recursive in the machine name and the packed budget and
input list.  `Nat.Partrec.Code.primrec_evaln` supplies the bounded evaluator,
`Nat.Partrec.Code.ofSource_primrec` the decoding of the machine name, and
`gateName_primrec` the per-entry gate. -/
lemma axiomWindow_primrec : Primrec₂ axiomWindow := by
  have hlist : Primrec fun p : ℕ × ℕ => Denumerable.ofNat (List ℕ) p.2.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hstep : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) =>
      gateName (((Nat.Partrec.Code.ofSource p.1).evaln p.2.unpair.1 i).getD
        verumSourceNat) :=
    show Primrec fun x : (ℕ × ℕ) × ℕ =>
        gateName (((Nat.Partrec.Code.ofSource x.1.1).evaln x.1.2.unpair.1 x.2).getD
          verumSourceNat) from
      gateName_primrec.comp
        (Primrec.option_getD.comp
          (Nat.Partrec.Code.primrec_evaln.comp
            (((Primrec.fst.comp (Primrec.unpair.comp
                (Primrec.snd.comp Primrec.fst))).pair
              (Nat.Partrec.Code.ofSource_primrec.comp
                (Primrec.fst.comp Primrec.fst))).pair Primrec.snd))
          (Primrec.const verumSourceNat))
  exact (Primrec.list_map hlist hstep).of_eq fun _ => rfl

/-- The window code is computable — all that `codeOfREPred` consumes. -/
lemma negWindowCode_computable : Computable₂ negWindowCode :=
  negSourceFormulaCode_computable.comp
    (combineSourceNats_primrec.comp axiomWindow_primrec).to_comp

end LogicalInduction

#print axioms LogicalInduction.verumSourceNat
#print axioms LogicalInduction.combineTokens
#print axioms LogicalInduction.combineTokens_nil
#print axioms LogicalInduction.combineTokens_cons
#print axioms LogicalInduction.combineSourceNats
#print axioms LogicalInduction.conjSource
#print axioms LogicalInduction.combineTokens_map_sourceNat
#print axioms LogicalInduction.combineSourceNats_map_sourceNat
#print axioms LogicalInduction.compile_conjSource
#print axioms LogicalInduction.AdmissibleName
#print axioms LogicalInduction.gateName
#print axioms LogicalInduction.exists_source_of_admissibleName
#print axioms LogicalInduction.admissibleName_sourceNat
#print axioms LogicalInduction.gateName_sourceNat
#print axioms LogicalInduction.gateName_verumSourceNat
#print axioms LogicalInduction.exists_source_gateName
#print axioms LogicalInduction.axiomWindow
#print axioms LogicalInduction.exists_sources_axiomWindow
#print axioms LogicalInduction.negWindowCode
#print axioms LogicalInduction.combineTokens_primrec
#print axioms LogicalInduction.combineSourceNats_primrec
#print axioms LogicalInduction.admissibleName_primrec
#print axioms LogicalInduction.gateName_primrec
#print axioms LogicalInduction.axiomWindow_primrec
#print axioms LogicalInduction.negWindowCode_computable
