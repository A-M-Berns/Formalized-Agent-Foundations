/-
# The run-level lookup, and a `RunOracle` for a finite table

`FreezeStep.RunOracle` is the one hole left in the machine-class freeze: given the incoming
day's token block and the buffered sentence run's bits, return the frozen suffix.  This file
builds one, for a quote table presented as a finite list of entries.

The table's own key is **parsing**: `tableLookup` fires the row whose sentence the buffered
run denotes under `parseRpn`.  That is the semantic specification, and it carries no
syntactic side condition at all — `tableLookup_eq_on` and both bridges to the market's
code-level tables are unconditional.

What *does* carry a side condition is the concrete recognizer that computes the key inside
`Complexity.FP`.  It is `oracleOf`, a **constant-depth chain**: for each table entry two
tests, the day against a fixed numeral (`TokenFold.ifNumEq_mem_FP`), and the buffered run
against that entry's sentence by `SegRec.segNest` — the run recognizer, which walks the
finitely many *segment* patterns of the target, decides each hole's escape-leaf obligation
with `FiberTest.holeGuards`, each structured payload with `PayAuto`, and each structured
length field with `CtrAuto`.  That a run matches one of those patterns exactly when it
denotes the target is `StructPat.parseRpn_iff_segMatch`, which carries no side condition at
all.  So there is no syntactic condition left to thread.

## What this file assumes, and where it is written down

* the entry list presents `S` and `quote` faithfully (`TablePresentation.lookup_eq`);
* the constant output budget, which here is *derived* rather than assumed
  (`oracleOf_length_le`): the emitted suffix is one of finitely many constant words.

`BotFree` and `NoReserved` used to be assumptions here and are not any more.  The escape
leaf's decode test is performed (`FiberTest.fiberW_mem_FP`, over `DigitFP.sqrtRemW_mem_FP`)
rather than assumed away, and the structured paper-prime block is recognized
(`SegRec.ifParseFull_mem_FP`) rather than excluded.  Nothing about a frozen sentence's
syntax is assumed anywhere in this file.

Nothing here is a restriction on the freeze, the trader, or the market.  All of it is a
property of the table being frozen, or of the recognizer chosen for it.
-/
import LogicalInduction.Construction.Witnesses.FreezeStep
import LogicalInduction.Construction.Witnesses.FiberTestFP
import LogicalInduction.Construction.Witnesses.SegmentRecognizer

namespace LogicalInduction.FreezeOracle

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.FreezeStep

/-- One row of a frozen quote table. -/
structure TableEntry where
  /-- The day whose price is frozen. -/
  day : ℕ
  /-- The sentence whose price is frozen. -/
  sentence : Sentence
  /-- The frozen rational quote. -/
  value : ℚ

/-! ## The lookup, on tokens -/

/-- Look a buffered run and a day up in the table, taking the first matching row.

The run key is **parsing**, not spelling membership: the row fires exactly when the run
denotes the row's sentence under the grammar the freeze actually parses with.  Which
concrete recognizer computes that test is the oracle's business (`oracleOf` below), and
keeping the two apart is what lets the recognizer be replaced without touching any of the
bridges to the market's code-level tables. -/
def tableLookup (entries : List TableEntry) (b : List ℕ) (D : ℕ) : Option ℚ :=
  match entries with
  | [] => none
  | e :: rest =>
      if e.day = D ∧ parseRpn b.length b = some (e.sentence, []) then some e.value
      else tableLookup rest b D

/-- The run-level selector the table denotes. -/
def selRunOf (entries : List TableEntry) (b : List ℕ) (D : ℕ) : Bool :=
  (tableLookup entries b D).isSome

/-- The run-level quote table the table denotes. -/
def quoteRunOf (entries : List TableEntry) (b : List ℕ) (D : ℕ) : ℕ :=
  ((tableLookup entries b D).map Encodable.encode).getD 0

/-! ## The lookup, on words -/

/-- The suffix emitted for one row. -/
def entryBits (e : TableEntry) : List Bool := tokBits [1, Encodable.encode e.value, 8]

/-- **The oracle**: a constant-depth chain over the table's rows.

Per row it makes two tests: the day, against a fixed numeral, and the buffered run, against
the row's sentence — the latter by `SegRec.segNest` rather than by membership in a list of
constant spellings.  Two substitutions removed the two old side conditions.  `⊥`'s infinite
decode fibre lives inside a *hole* predicate that `FiberTest.holeGuards` decides, so the
pattern list is exhaustive without `BotFree`; and a structured paper-prime block is a
*segment* that `SegRec` recognizes with a finite automaton for the payload and a counter for
the unary length field, so the list is exhaustive without `NoReserved` either. -/
def oracleOf (entries : List TableEntry) (v : List Bool) : List Bool :=
  match entries with
  | [] => []
  | e :: rest =>
      if NumEqBits e.day (fstBlock v) then
        SegRec.segNest FiberTest.holeGuards sndBlock (fun _ => entryBits e)
          (fun v => oracleOf rest v) (StructPat.segPatterns e.sentence) v
      else oracleOf rest v

/-! ### What the chain emits -/

@[simp] lemma decodeBits_entryBits (e : TableEntry) :
    decodeBits (entryBits e) = [1, Encodable.encode e.value, 8] := by
  rw [entryBits, decodeBits_tokBits]

/-- **The chain computes the table lookup — with no condition on the table.**

The chain's per-row test is segment-pattern matching; the table's key is parsing.  That the
two agree is `StructPat.parseRpn_iff_segMatch`, which holds for every target, so no
syntactic side condition is consumed here or anywhere downstream.

Exactness is what is at stake, in both directions.  A run the parser accepts but the chain
rejects would leave that price leaf unfrozen; a run the chain accepts but the parser does
not would freeze a coordinate the table does not name.  `segNest` is exact because
`SegRec.segMatch_iff_accepts` splits each pattern's language into a part its automaton
decides and a part its counter decides, and neither approximates.

Proof kind: `P` proved.  Provenance: (a) `numEqBits_spec`, `SegRec.segNest_pos`,
`SegRec.segNest_neg`; (b) `StructPat.parseRpn_iff_segMatch`.
Paper node: `app:ifp` -/
lemma decodeBits_oracleOf : ∀ (entries : List TableEntry) (cur : List ℕ),
    (∀ d ∈ cur, d < 4) → ∀ bufW : List Bool,
    decodeBits (oracleOf entries (pair (digitsToBits cur) bufW))
      = if selRunOf entries (decodeBits bufW) (digitVal cur) then
          [1, quoteRunOf entries (decodeBits bufW) (digitVal cur), 8] else []
  | [], cur, _, bufW => by
      rw [oracleOf, selRunOf, tableLookup]
      simp [quoteRunOf, tableLookup]
  | (e :: rest), cur, hcur, bufW => by
      have hiff := StructPat.parseRpn_iff_segMatch e.sentence (decodeBits bufW)
      rw [oracleOf, fstBlock_pair]
      by_cases hday : NumEqBits e.day (digitsToBits cur)
      · have hd : digitVal cur = e.day := (numEqBits_spec e.day cur hcur).mp hday
        rw [if_pos hday]
        by_cases hp : parseRpn (decodeBits bufW).length (decodeBits bufW)
            = some (e.sentence, [])
        · have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
              = some e.value := by rw [tableLookup, if_pos ⟨hd.symm, hp⟩]
          rw [SegRec.segNest_pos _ _ _ _ _ _ (by
            rw [sndBlock_pair]; exact hiff.mp hp), decodeBits_entryBits]
          simp only [selRunOf, quoteRunOf, hlk]
          simp
        · have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
              = tableLookup rest (decodeBits bufW) (digitVal cur) := by
            rw [tableLookup, if_neg (fun hc => hp hc.2)]
          rw [SegRec.segNest_neg _ _ _ _ _ _ (by
            rw [sndBlock_pair]; exact fun hc => hp (hiff.mpr hc))]
          rw [decodeBits_oracleOf rest cur hcur bufW]
          simp only [selRunOf, quoteRunOf, hlk]
      · have hd : digitVal cur ≠ e.day := fun hc =>
          hday ((numEqBits_spec e.day cur hcur).mpr hc)
        have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
            = tableLookup rest (decodeBits bufW) (digitVal cur) := by
          rw [tableLookup, if_neg (fun hc => hd hc.1.symm)]
        rw [if_neg hday, decodeBits_oracleOf rest cur hcur bufW]
        simp only [selRunOf, quoteRunOf, hlk]

/-! ### Well-formedness and the constant budget -/

lemma blockWF_oracleOf : ∀ (entries : List TableEntry) (v : List Bool),
    BlockWF (oracleOf entries v)
  | [], v => by rw [oracleOf]; exact BlockWF.nil
  | (e :: rest), v => by
      rw [oracleOf]
      split_ifs
      · rcases SegRec.segNest_cases FiberTest.holeGuards sndBlock (fun _ => entryBits e)
            (fun v => oracleOf rest v) (StructPat.segPatterns e.sentence) v with h | h
        · rw [h]; exact blockWF_tokBits _
        · rw [h]; exact blockWF_oracleOf rest v
      · exact blockWF_oracleOf rest v

/-- The constant output budget: the widest suffix the table can emit. -/
def oracleLen (entries : List TableEntry) : ℕ :=
  entries.foldr (fun e n => max (entryBits e).length n) 0

lemma oracleOf_length_le : ∀ (entries : List TableEntry) (v : List Bool),
    (oracleOf entries v).length ≤ oracleLen entries
  | [], v => by rw [oracleOf, oracleLen]; simp
  | (e :: rest), v => by
      rw [oracleOf, oracleLen, List.foldr_cons]
      have hrec : (oracleOf rest v).length ≤ oracleLen rest := oracleOf_length_le rest v
      split_ifs
      · rcases SegRec.segNest_cases FiberTest.holeGuards sndBlock (fun _ => entryBits e)
            (fun v => oracleOf rest v) (StructPat.segPatterns e.sentence) v with h | h
        · rw [h]; exact le_max_left _ _
        · rw [h]; exact le_trans hrec (le_max_right _ _)
      · exact le_trans hrec (le_max_right _ _)

/-! ### Membership -/

/-- **The chain is polynomial time**: a fixed-depth nest of a numeral test and a pattern
test, one level per table row.

Proof kind: `C` composition.  Provenance: (b) `ifNumEq_mem_FP`, `SegRec.segNest_mem_FP`.
Paper node: `app:ifp` -/
lemma oracleOf_mem_FP : ∀ (entries : List TableEntry), oracleOf entries ∈ FP
  | [] => by
      have heq : oracleOf [] = fun _ : List Bool => ([] : List Bool) := by
        funext v; rw [oracleOf]
      rw [heq]; exact constFn_mem_FP []
  | (e :: rest) => by
      have hrec := oracleOf_mem_FP rest
      have hpat : (fun v => SegRec.segNest FiberTest.holeGuards sndBlock
          (fun _ => entryBits e) (fun v => oracleOf rest v)
          (StructPat.segPatterns e.sentence) v) ∈ FP :=
        SegRec.segNest_mem_FP _ sndBlock_mem_FP (constFn_mem_FP _) hrec _
      have h := ifNumEq_mem_FP fstBlock_mem_FP e.day hpat hrec
      have heq : (fun v => if NumEqBits e.day (fstBlock v) then
            SegRec.segNest FiberTest.holeGuards sndBlock (fun _ => entryBits e)
              (fun v => oracleOf rest v) (StructPat.segPatterns e.sentence) v
          else oracleOf rest v) = oracleOf (e :: rest) := by
        funext v; rw [oracleOf]
      rwa [heq] at h

/-! ## The oracle -/

/-- **A `RunOracle` for any finite table.**  Nothing is assumed about the table here; the
side conditions enter only when this oracle's `selRunOf`/`quoteRunOf` are matched against a
market's `selCode`/`quoteCode`, which is `TablePresentation` below.

Kind `N+` non-vacuity witness.  Provenance: (a) `oracleOf_mem_FP`, `blockWF_oracleOf`,
`oracleOf_length_le`, `decodeBits_oracleOf`.
Paper node: `app:ifp` -/
def runOracleOf (entries : List TableEntry) :
    RunOracle (selRunOf entries) (quoteRunOf entries) where
  R := oracleOf entries
  R_FP := oracleOf_mem_FP entries
  R_wf := fun _ _ => blockWF_oracleOf entries _
  R_len := oracleLen entries
  R_length_le := fun v => oracleOf_length_le entries v
  R_spec := fun cur hcur bufW => decodeBits_oracleOf entries cur hcur bufW

/-! ## Matching the oracle to a market's table

`runOracleOf` answers questions about *runs*; `MachineFiniteSupportPatch` asks about
*sentences*.  `parseRpn_iff_mem_spellings` is the bridge, and it is the only place the
recognition side conditions are used. -/

/-- The table lookup, keyed by sentence rather than by run. -/
def tableLookupOn (entries : List TableEntry) (φ : Sentence) (D : ℕ) : Option ℚ :=
  match entries with
  | [] => none
  | e :: rest =>
      if e.day = D ∧ e.sentence = φ then some e.value else tableLookupOn rest φ D

/-- **On a run that parses, the two lookups agree** — unconditionally.

Since `tableLookup` is keyed by parsing and `parseRpn` is a function, a run that parses to
`φ` fires exactly the rows whose sentence *is* `φ`.  No syntactic side condition survives
at this level; the recognition condition lives entirely in `decodeBits_oracleOf`. -/
lemma tableLookup_eq_on : ∀ (entries : List TableEntry),
    ∀ {b : List ℕ} {φ : Sentence}, parseRpn b.length b = some (φ, []) → ∀ D : ℕ,
    tableLookup entries b D = tableLookupOn entries φ D
  | [], b, φ, _, D => rfl
  | (e :: rest), b, φ, hb, D => by
      have hiff : parseRpn b.length b = some (e.sentence, []) ↔ e.sentence = φ := by
        constructor
        · intro h
          rw [hb] at h
          exact ((Prod.mk.inj (Option.some.inj h)).1).symm
        · intro h; rw [h]; exact hb
      rw [tableLookup, tableLookupOn]
      by_cases hc : e.day = D ∧ e.sentence = φ
      · rw [if_pos ⟨hc.1, hiff.mpr hc.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, hiff.mp h.2⟩), if_neg hc]
        exact tableLookup_eq_on rest hb D

/-- The condition under which an entry list presents a market's frozen quote table.

It is a property of the **table**, not of the freeze: the list must name exactly the
coordinates of `S` with their quotes.  Nothing syntactic survives here — the recognizer's
side condition is carried separately, at `runOracleOf`. -/
structure TablePresentation (S : Finset (ℕ × Sentence)) (quote : ℕ → Sentence → ℚ)
    (entries : List TableEntry) : Prop where
  /-- The list presents `S` and `quote` faithfully. -/
  lookup_eq : ∀ (D : ℕ) (φ : Sentence),
    tableLookupOn entries φ D = if (D, φ) ∈ S then some (quote D φ) else none

/-! ### The code-level selector and quote table a market induces -/

/-- The selector `S` induces on sentence codes. -/
def selCodeOf (S : Finset (ℕ × Sentence)) (D c : ℕ) : Bool :=
  match (Encodable.decode c : Option Sentence) with
  | some φ => decide ((D, φ) ∈ S)
  | none => false

/-- The quote table `quote` induces on sentence codes. -/
def quoteCodeOf (quote : ℕ → Sentence → ℚ) (D c : ℕ) : ℕ :=
  match (Encodable.decode c : Option Sentence) with
  | some φ => Encodable.encode (quote D φ)
  | none => 0

lemma selCodeOf_decode {S : Finset (ℕ × Sentence)} (D c : ℕ) {φ : Sentence}
    (h : (Encodable.decode c : Option Sentence) = some φ) :
    selCodeOf S D c = decide ((D, φ) ∈ S) := by rw [selCodeOf, h]

lemma quoteCodeOf_decode {quote : ℕ → Sentence → ℚ} (D c : ℕ) {φ : Sentence}
    (h : (Encodable.decode c : Option Sentence) = some φ) :
    quoteCodeOf quote D c = Encodable.encode (quote D φ) := by rw [quoteCodeOf, h]

/-! ### The bridges -/

lemma selRunOf_bridge {S : Finset (ℕ × Sentence)} {quote : ℕ → Sentence → ℚ}
    {entries : List TableEntry} (htab : TablePresentation S quote entries)
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) (D : ℕ) :
    selRunOf entries b D = selCodeOf S D (Encodable.encode φ) := by
  rw [selRunOf, tableLookup_eq_on entries hb D, htab.lookup_eq D φ,
    selCodeOf_decode D _ (Encodable.encodek φ)]
  by_cases hmem : (D, φ) ∈ S
  · rw [if_pos hmem]; simp [hmem]
  · rw [if_neg hmem]; simp [hmem]

/-- The quote bridge holds exactly where the freeze reads it: at a **selected** coordinate.

Off the table there is no run-level information about `quote D φ` at all, so the
unconditional form is not merely unproved but unsatisfiable for a table-driven oracle.  The
freeze never reads it there — `RpnFreeze.freezeEmitOn` consults `quoteRun` only inside the
`selRun` branch — so the guarded form is the honest hypothesis. -/
lemma quoteRunOf_bridge {S : Finset (ℕ × Sentence)} {quote : ℕ → Sentence → ℚ}
    {entries : List TableEntry} (htab : TablePresentation S quote entries)
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) (D : ℕ)
    (hsel : selRunOf entries b D = true) :
    quoteRunOf entries b D = quoteCodeOf quote D (Encodable.encode φ) := by
  have hlk : tableLookup entries b D = if (D, φ) ∈ S then some (quote D φ) else none := by
    rw [tableLookup_eq_on entries hb D, htab.lookup_eq D φ]
  have hmem : (D, φ) ∈ S := by
    by_contra hc
    rw [selRunOf, hlk, if_neg hc] at hsel
    simp at hsel
  rw [quoteRunOf, hlk, if_pos hmem, quoteCodeOf_decode D _ (Encodable.encodek φ)]
  simp

/-! ## The patch, for a presented table -/

/-- **`MachineFiniteSupportPatch` for any market whose frozen table is presented by an
entry list of reserved-atom-free sentences.**

Kind `C`; hypotheses `(a)` except the `TablePresentation`, which is the disclosed side
condition on the table.
Paper node: `app:ifp` -/
def machineFiniteSupportPatch_ofTable
    (P : History) (S : Finset (ℕ × Sentence)) (quote : ℕ → Sentence → ℚ)
    (hexact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ))
    (entries : List TableEntry) (htab : TablePresentation S quote entries) :
    MachineFiniteSupportPatch P S :=
  machineFiniteSupportPatch_of_rewriter P S quote hexact
    (selCodeOf S) (quoteCodeOf quote)
    (fun day code φ h => selCodeOf_decode day code h)
    (fun day code φ h => quoteCodeOf_decode day code h)
    (FreezeStep.freezeStreamRewriter_of_runOracle (runOracleOf entries)
      (selCodeOf S) (quoteCodeOf quote)
      (fun b _ hb D => selRunOf_bridge htab hb D)
      (fun b _ hb D hs => quoteRunOf_bridge htab hb D hs))

/-! ## A concrete table: the patch is not vacuous, and not degenerate

The empty table satisfies everything vacuously and would inhabit `MachineFiniteSupportPatch`
while forcing `P = P'`.  That is not a discharge, so this section exhibits a table with a
**real row**: day `0`, the sentence `atom 0`, quote `1/2`.  Its coordinate set is nonempty,
so the perturbation it licenses moves an actual price. -/

/-- An atom is recognizable as soon as it is not the reserved shape; `BotFree` is free. -/
lemma recognizable_atom (a : ℕ)
    (ha : ∀ pol fc : ℕ, a ≠ Nat.pair 5 (Nat.pair pol fc)) :
    Recognizable (LO.Propositional.Formula.atom a) where
  botFree := botFree_atom a
  noReserved := ha

/-- Atom `0` is not reserved: every reserved payload is positive. -/
lemma atom_zero_noReserved : ∀ pol fc : ℕ, (0 : ℕ) ≠ Nat.pair 5 (Nat.pair pol fc) := by
  intro pol fc h
  have hpos : 0 < Nat.pair 5 (Nat.pair pol fc) := by
    rw [Nat.pair]
    split <;> omega
  omega

/-- A one-row frozen table, at an arbitrary quote value.

The value is a parameter because `machine_lic_iff_of_finiteSupportPerturbation` needs a
patch for **each** of the two markets, and each patch carries its own table — that is how
`P` and `P'` are allowed to differ on `S` while both are patchable. -/
def exampleEntries (q : ℚ) : List TableEntry :=
  [⟨0, LO.Propositional.Formula.atom 0, q⟩]

/-- The coordinate set it presents. -/
def exampleS : Finset (ℕ × Sentence) := {(0, LO.Propositional.Formula.atom 0)}

/-- The quote it freezes. -/
def exampleQuote (q : ℚ) : ℕ → Sentence → ℚ := fun _ _ => q

/-- **The table is not empty** — this is what rules out the degenerate discharge.

Kind `N+` non-vacuity witness.
Paper node: `app:ifp` -/
lemma exampleS_nonempty : exampleS.Nonempty :=
  ⟨(0, LO.Propositional.Formula.atom 0), by simp [exampleS]⟩

lemma examplePresentation (q : ℚ) :
    TablePresentation exampleS (exampleQuote q) (exampleEntries q) where
  lookup_eq := by
    intro D φ
    rw [exampleEntries, tableLookupOn, tableLookupOn]
    by_cases h : (0 : ℕ) = D ∧ (LO.Propositional.Formula.atom 0 : Sentence) = φ
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, if_pos (by simp [exampleS])]
      rfl
    · rw [if_neg h, if_neg (by
        intro hc
        simp only [exampleS, Finset.mem_singleton, Prod.ext_iff] at hc
        exact h ⟨hc.1.symm, hc.2.symm⟩)]

/-- **`MachineFiniteSupportPatch` at a table with a real row.**

`exampleS_nonempty` is the check that this is not the degenerate discharge: the coordinate
set contains `(0, atom 0)`, so `P` and `P'` may genuinely differ there — and since `q` is a
parameter, the two markets get patches with *different* tables.

Side conditions carried: the table's one sentence is `Recognizable`
(`recognizable_atom`, `atom_zero_noReserved`) and the row presents `exampleS`/`exampleQuote`
faithfully (`examplePresentation`).  The constant output budget is derived, not assumed.
Paper node: `app:ifp` -/
def machineFiniteSupportPatch_example (q : ℚ) (P : History)
    (hexact : ∀ d φ, (d, φ) ∈ exampleS → P d φ = ((exampleQuote q d φ : ℚ) : ℝ)) :
    MachineFiniteSupportPatch P exampleS :=
  machineFiniteSupportPatch_ofTable P exampleS (exampleQuote q) hexact
    (exampleEntries q) (examplePresentation q)

/-- **Both markets of a genuine perturbation are patchable.**  `P` freezes at `q`, `P'` at
`q'`, on the same nonempty coordinate set — so this is the two-sided hypothesis
`machine_lic_iff_of_finiteSupportPerturbation` asks for, at a table that actually moves a
price.

What this does *not* supply is the markets themselves: the theorem also wants
`ComputableMarket P`, `ComputableMarket P'` and tail agreement, and no concrete pair is
constructed here.
Paper node: `app:ifp` -/
def machineFiniteSupportPatch_pair (q q' : ℚ) (P P' : History)
    (hexact : ∀ d φ, (d, φ) ∈ exampleS → P d φ = ((exampleQuote q d φ : ℚ) : ℝ))
    (hexact' : ∀ d φ, (d, φ) ∈ exampleS → P' d φ = ((exampleQuote q' d φ : ℚ) : ℝ)) :
    MachineFiniteSupportPatch P exampleS × MachineFiniteSupportPatch P' exampleS :=
  (machineFiniteSupportPatch_example q P hexact,
    machineFiniteSupportPatch_example q' P' hexact')

/-! ## The chain, end to end

Every link with every hypothesis explicit.  This is the audit that the inhabitant does not
silently require something it fails to supply: if any link did, the term below would not
elaborate.

`RunOracle` → `FreezeStreamRewriter` → `preserves_ec` → `MachineFiniteSupportPatch` →
`machine_lic_iff_of_finiteSupportPerturbation`. -/

/-- The coordinate set has a real member. -/
lemma mem_exampleS : (0, LO.Propositional.Formula.atom 0) ∈ exampleS := by
  simp [exampleS]

/-- And is therefore not the empty table, which would have inhabited everything vacuously
while forcing `P = P'`. -/
lemma exampleS_ne_empty : exampleS ≠ (∅ : Finset (ℕ × Sentence)) := by
  intro h
  have hm := mem_exampleS
  rw [h] at hm
  exact absurd hm (by simp)

/-- **The corrected `thm:ifp`, instantiated at a table that moves a real price.**

The remaining hypotheses are about the *markets*, not the freeze: `ComputableMarket` for
each and tail agreement off `exampleS`.  No concrete such pair is constructed here, so this
records that the freeze side is discharged — not that the theorem has been exhibited
non-vacuous end to end.

Kind `N+` non-vacuity witness.  Provenance: (a) `machineFiniteSupportPatch_example`.
Paper node: `app:ifp` -/
lemma machine_lic_iff_example (q q' : ℚ) (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ∉ exampleS → P d φ = P' d φ)
    (hexact : ∀ d φ, (d, φ) ∈ exampleS → P d φ = ((exampleQuote q d φ : ℚ) : ℝ))
    (hexact' : ∀ d φ, (d, φ) ∈ exampleS → P' d φ = ((exampleQuote q' d φ : ℚ) : ℝ)) :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  machine_lic_iff_of_finiteSupportPerturbation P P' DP exampleS hPcomp hP'comp hagree
    (machineFiniteSupportPatch_example q P hexact)
    (machineFiniteSupportPatch_example q' P' hexact')

/-! ## The patch, compiled from the market alone

Nothing above needs a caller-supplied presentation: for a finite coordinate set the entry
list is *canonical*, read straight off `S` and the market's own rational table.  So the
patch hypothesis of `machine_lic_iff_of_finiteSupportPerturbation` is not a real hypothesis
— it is compiler residue, and this section removes it.

What does **not** dissolve is `Recognizable`.  See the boundary note at the end of this
section for exactly what forces it. -/

/-- The canonical entry list for a finite coordinate set and a code-level quote table. -/
noncomputable def entriesOf (S : Finset (ℕ × Sentence)) (mq : ℕ → ℕ → ℚ) :
    List TableEntry :=
  S.toList.map fun p => ⟨p.1, p.2, mq p.1 (Encodable.encode p.2)⟩

lemma tableLookupOn_map : ∀ (l : List (ℕ × Sentence)) (mq : ℕ → ℕ → ℚ)
    (φ : Sentence) (D : ℕ),
    tableLookupOn (l.map fun p => ⟨p.1, p.2, mq p.1 (Encodable.encode p.2)⟩) φ D
      = if (D, φ) ∈ l then some (mq D (Encodable.encode φ)) else none
  | [], mq, φ, D => by rw [List.map_nil, tableLookupOn]; simp
  | (p :: l), mq, φ, D => by
      rw [List.map_cons, tableLookupOn, tableLookupOn_map l mq φ D]
      by_cases hc : p.1 = D ∧ p.2 = φ
      · have hp : p = (D, φ) := Prod.ext hc.1 hc.2
        rw [if_pos hc, if_pos (by rw [hp]; exact List.mem_cons_self ..), hc.1, hc.2]
      · rw [if_neg hc]
        by_cases hm : (D, φ) ∈ l
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        · rw [if_neg hm, if_neg (by
            intro hcons
            rcases List.mem_cons.mp hcons with h | h
            · exact hc ⟨congrArg Prod.fst h.symm, congrArg Prod.snd h.symm⟩
            · exact hm h)]

lemma tablePresentation_entriesOf (S : Finset (ℕ × Sentence)) (mq : ℕ → ℕ → ℚ) :
    TablePresentation S (fun d φ => mq d (Encodable.encode φ)) (entriesOf S mq) where
  lookup_eq := by
    intro D φ
    rw [entriesOf, tableLookupOn_map]
    simp only [Finset.mem_toList]

/-- **The patch, built from the market's own computability certificate.**

No presentation is supplied by the caller: the entry list is `entriesOf`, read off `S` and
the market's rational table.  `Classical.choice` enters only to name that table, which
`ComputableMarket` asserts to exist.

There is no condition on the sentences of `S`.  The recognizer that decides which runs
denote them is `SegRec.ifParseFull_mem_FP`, which walks the target's segment patterns with a
finite automaton for the shape and the structured payload and a one-counter machine for the
structured length field; nothing about the target restricts it.

Kind `C`; hypotheses `(a)`.
Paper node: `app:ifp` -/
noncomputable def machineFiniteSupportPatch (P : History)
    (S : Finset (ℕ × Sentence)) (hP : ComputableMarket P) :
    MachineFiniteSupportPatch P S :=
  let mc := hP.nonemptyComputation.some
  machineFiniteSupportPatch_ofTable P S (fun d φ => mc.quote d (Encodable.encode φ))
    (fun d φ _ => mc.quote_exact d φ) (entriesOf S mc.quote)
    (tablePresentation_entriesOf S mc.quote)

/-- Compatibility: the reserved-atom-free form, now an immediate specialization.

Kind `C`; hypotheses `(a)`.
Paper node: `app:ifp` -/
noncomputable def machineFiniteSupportPatch_ofNoReserved (P : History)
    (S : Finset (ℕ × Sentence)) (hP : ComputableMarket P)
    (_hnr : ∀ p ∈ S, NoReserved p.2) :
    MachineFiniteSupportPatch P S :=
  machineFiniteSupportPatch P S hP

/-- Compatibility: the syntactically recognizable form, likewise.

Kind `C`; hypotheses `(a)`.
Paper node: `app:ifp` -/
noncomputable def machineFiniteSupportPatch_ofRecognizable (P : History)
    (S : Finset (ℕ × Sentence)) (hP : ComputableMarket P)
    (_hrec : ∀ p ∈ S, Recognizable p.2) :
    MachineFiniteSupportPatch P S :=
  machineFiniteSupportPatch P S hP

/-- `P` and `P'` differ on only finitely many price coordinates, and no sentence involved
has a **reserved-atom** subformula.

This is the public hypothesis of the corrected theorem.  Its two halves are of different
kinds and should be read that way: finite support is a **mathematical** condition on the
perturbation, while `NoReserved` is a **representation** condition on the sentences, forced
by FAF's RPN syntax and not by the mathematics.

`BotFree`, the other half of the old `Recognizable`, is gone: the escape leaf's decode test
is now performed rather than assumed away (`FiberTest.holeGuards`). -/
def NoReservedSupportPerturbation (P P' : History) : Prop :=
  ∃ S : Finset (ℕ × Sentence),
    (∀ p ∈ S, NoReserved p.2) ∧ ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ

lemma NoReservedSupportPerturbation.toFiniteSupport {P P' : History}
    (h : NoReservedSupportPerturbation P P') : FiniteSupportPerturbation P P' := by
  obtain ⟨S, -, hagree⟩ := h
  exact ⟨S, hagree⟩

/-- `P` and `P'` differ on only finitely many price coordinates, and every sentence
involved is syntactically recognizable.

Retained for compatibility; `NoReservedSupportPerturbation` is strictly weaker and is what
the theorem below actually needs. -/
def RecognizableSupportPerturbation (P P' : History) : Prop :=
  ∃ S : Finset (ℕ × Sentence),
    (∀ p ∈ S, Recognizable p.2) ∧ ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ

lemma RecognizableSupportPerturbation.toNoReserved {P P' : History}
    (h : RecognizableSupportPerturbation P P') : NoReservedSupportPerturbation P P' := by
  obtain ⟨S, hrec, hagree⟩ := h
  exact ⟨S, fun p hp => (hrec p hp).noReserved, hagree⟩

lemma RecognizableSupportPerturbation.toFiniteSupport {P P' : History}
    (h : RecognizableSupportPerturbation P P') : FiniteSupportPerturbation P P' :=
  h.toNoReserved.toFiniteSupport

/-- **The corrected `thm:ifp`.**

Finite `(day, sentence)` support and computability of both markets — nothing else.  No
patch certificate: the `MachineFiniteSupportPatch` both markets need is *compiled* here,
from `S` and their own quote tables.  And no condition on the finitely many sentences whose
price moves: the recognizer that decides which token runs denote them
(`SegRec.ifParseFull_mem_FP`) is unconditional.

This is the canonical corrected replacement for the paper's finite-*days* statement, which
is **false** and stays refuted (`FinitePerturbationCounterexample.not_overgeneral_ifp`).
The two statements cannot be confused: finite coordinate support implies eventual day
agreement (`FiniteSupportPerturbation.tail_agree`) and the converse fails
(`tailAgree_not_finiteSupport`), so this theorem cannot re-derive the refuted one.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem machine_lic_iff_of_finiteSupport (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : FiniteSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP := by
  obtain ⟨S, hagree⟩ := hpert
  exact machine_lic_iff_of_finiteSupportPerturbation P P' DP S hPcomp hP'comp hagree
    (machineFiniteSupportPatch P S hPcomp)
    (machineFiniteSupportPatch P' S hP'comp)

/-- **The reserved-atom-free endpoint, now an immediate corollary.**

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem machine_lic_iff_of_noReservedSupport (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : NoReservedSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  machine_lic_iff_of_finiteSupport P P' DP hPcomp hP'comp hpert.toFiniteSupport

/-- **The syntactically recognizable endpoint, likewise.**

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem machine_lic_iff_of_recognizableSupport (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : RecognizableSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  machine_lic_iff_of_finiteSupport P P' DP hPcomp hP'comp hpert.toFiniteSupport

/-! ### What the two old side conditions stood for, and how each was discharged

`machine_lic_iff_of_finiteSupport` is the strongest statement proved here, and it is the
mathematically natural one: finite `(day, sentence)` support, computability of both markets,
nothing else.  Both syntactic conditions the earlier endpoints carried are gone, and neither
was weakened or renamed — each stood for a missing `Complexity.FP` device, and each device
was built.

* **`BotFree` stood for integer square root.**  A price leaf may be spelled with the
  two-token escape `[1, c]`, meaning `Encodable.decode c`, and Foundation's `Formula.ofNat`
  discards the payload at tag `0`, so `⊥` has infinitely many codes
  (`decode_falsum_noncanonical`).  Deciding "does this code denote `ψ`" is therefore
  `Nat.unpair` on the token's digits, i.e. integer square root.
  `DigitFP.sqrtRemW_mem_FP` and `DigitFP.unpairW_spec` supply the arithmetic and
  `FiberTest.fiberW_mem_FP` the decode test, while `RpnFreeze.patterns` replaces the
  constant spelling list, confining the infinite fibre inside a hole predicate.

* **`NoReserved` stood for a structured-payload recognizer**, and that is two problems, not
  one.  A leaf may also be spelled with the structured paper-prime block
  `[1, 0, pol] ++ 1^L ++ [0] ++ p ++ [19]`, which denotes *only* reserved atoms
  `atom (Nat.pair 5 _)` (`parseStructuredPaperPrime_shape`), so excluding those targets made
  the branch unreachable.  Covering them needed both of:

  - **the length identification**, `L = |p|`.  The numeral `0` is spelled `1^k 0` for every
    `k` (`parseStructuredNat`'s self-loop), so `L` is unbounded even for a fixed target and
    matching `1^L` against `|p|` is `aⁿbⁿ`.  No bounded-state device decides it;
    `CtrAuto.ctrMachine` — `RunAuto.BlockMachine` instantiated as a finite control paired
    with one unary counter, whose state grows a mark per token and stays inside
    `Complexity.FP` — does.
  - **the payload language** itself: *which* token strings denote the fixed code `fc`.  This
    is the larger half and it is not a matter of a finite spelling list either, because
    numeral padding and the double negation `[20, 20]` both preserve a code.  `PayAuto`
    decides it by top-down predictive parsing against a stack of obligations, carrying the
    pending negation as a parity bit rather than applying `negFormulaCode`; that keeps every
    child code an `unpair` component of its parent, so a potential argument bounds the
    reachable stacks and the state set is finite.  The parity trick is sound because
    `negFormulaCode` is an involution *on the parser's range* — not on `ℕ`, where tags 2/3
    discard their payload (`PayAuto.WFCode`).

Neither condition was ever a restriction on markets, traders, or perturbations: both were
conditions on the **syntax** of the finitely many sentences whose price moves.  Read against
the classification the file header asks for, finite support is condition (i), a mathematical
property of the perturbation — and there is no longer any condition (ii).

The patch hypothesis was residue of a *third* kind — neither mathematics nor representation,
but a compiler artifact — and it is gone too: `entriesOf` reads the table off `S` and the
market's own certificate, so no caller supplies anything.

What remains disclosed here is one thing only, and it is a property of the *construction*
rather than of the statement: the recognizer is compiled per frozen sentence, so its
polynomial-time witness carries constants (the automaton's state bound) that depend on that
sentence.  That is exactly the paper's own "finitely many constants can be hard-coded", and
it is sound precisely because the support is finite — which is the point at which the
published finite-*days* proof breaks and this one does not. -/

/-! ## A concrete computable market pair

`machine_lic_iff_example` still carries `ComputableMarket` hypotheses, so it says nothing
until a pair is exhibited.  This section builds one: two markets that price everything at
zero except the single coordinate `(0, atom 0)`, which one prices at `q` and the other at
`q'`.  They are computable in the sense `def:marketprocess` asks for — a rational table with
a `Nat.Partrec.Code` computing it on the *paired* input, so day `0` gets no free
special-casing — and they differ exactly on `exampleS`. -/

/-- The rational quote table: `q` at the frozen coordinate, zero everywhere else. -/
def twoPointQuote (q : ℚ) : ℕ → ℕ → ℚ := fun n c =>
  if n = 0 ∧ c = Encodable.encode (LO.Propositional.Formula.atom 0 : Sentence) then q
  else 0

/-- The market it presents. -/
def twoPointHistory (q : ℚ) : History := fun n φ => (twoPointQuote q n (Encodable.encode φ) : ℝ)

lemma twoPointQuote_mem_Icc {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n c : ℕ) :
    0 ≤ twoPointQuote q n c ∧ twoPointQuote q n c ≤ 1 := by
  rw [twoPointQuote]
  split_ifs
  · exact ⟨h0, h1⟩
  · exact ⟨le_refl 0, by norm_num⟩

lemma twoPointHistory_mem_Icc {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) (φ : Sentence) :
    0 ≤ twoPointHistory q n φ ∧ twoPointHistory q n φ ≤ 1 := by
  obtain ⟨ha, hb⟩ := twoPointQuote_mem_Icc h0 h1 n (Encodable.encode φ)
  constructor
  · show (0 : ℝ) ≤ ((twoPointQuote q n (Encodable.encode φ) : ℚ) : ℝ)
    exact_mod_cast ha
  · show ((twoPointQuote q n (Encodable.encode φ) : ℚ) : ℝ) ≤ 1
    exact_mod_cast hb

/-- **The table is computable**, as a function of the paired input. -/
lemma computable_twoPointQuote (q : ℚ) :
    Computable (fun z : ℕ => twoPointQuote q z.unpair.1 z.unpair.2) := by
  have h1 : Computable (fun z : ℕ => decide (z.unpair.1 = 0)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp
  have h2 : Computable (fun z : ℕ =>
      decide (z.unpair.2
        = Encodable.encode (LO.Propositional.Formula.atom 0 : Sentence))) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const _)).decide.to_comp
  refine (Computable.cond h1
    (Computable.cond h2 (Computable.const q) (Computable.const 0))
    (Computable.const 0)).of_eq (fun z => ?_)
  rw [twoPointQuote]
  by_cases ha : z.unpair.1 = 0
  · by_cases hb : z.unpair.2
        = Encodable.encode (LO.Propositional.Formula.atom 0 : Sentence)
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-- **Both markets are honest `ComputableMarket`s.**

Kind `N+` non-vacuity witness.  Provenance: (a) `computable_twoPointQuote`;
(b) `Nat.Partrec.Code.exists_code`.
Paper node: `app:ifp` -/
theorem computableMarket_twoPoint (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ComputableMarket (twoPointHistory q) := by
  refine ⟨twoPointHistory_mem_Icc h0 h1, ?_⟩
  have hcomp : Computable (fun z : ℕ =>
      Encodable.encode (twoPointQuote q z.unpair.1 z.unpair.2)) :=
    Computable.encode.comp (computable_twoPointQuote q)
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (twoPointQuote q z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨twoPointQuote q, code, fun n φ => rfl, fun z => ?_⟩
  rw [hcode]
  simp

/-- Off the frozen coordinate the two markets agree. -/
lemma twoPointHistory_agree (q q' : ℚ) :
    ∀ d φ, (d, φ) ∉ exampleS → twoPointHistory q d φ = twoPointHistory q' d φ := by
  intro d φ hmem
  have hne : ¬(d = 0 ∧ φ = (LO.Propositional.Formula.atom 0 : Sentence)) := by
    intro hc
    exact hmem (by simp [exampleS, hc.1, hc.2])
  have hq : ∀ r : ℚ, twoPointQuote r d (Encodable.encode φ) = 0 := by
    intro r
    rw [twoPointQuote, if_neg]
    intro hc
    exact hne ⟨hc.1, Encodable.encode_injective hc.2⟩
  rw [twoPointHistory, twoPointHistory, hq, hq]

/-- On the frozen coordinate the market really is at its table value. -/
lemma twoPointHistory_exact (q : ℚ) :
    ∀ d φ, (d, φ) ∈ exampleS →
      twoPointHistory q d φ = ((exampleQuote q d φ : ℚ) : ℝ) := by
  intro d φ hmem
  simp only [exampleS, Finset.mem_singleton, Prod.ext_iff] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  rw [twoPointHistory, twoPointQuote, if_pos ⟨rfl, rfl⟩]
  rfl

/-- **The two markets genuinely differ.**  Without this the pair would establish nothing —
the same degenerate route as the empty table, by a different door. -/
lemma twoPointHistory_ne {q q' : ℚ} (h : q ≠ q') :
    twoPointHistory q ≠ twoPointHistory q' := by
  intro hc
  have := congrFun (congrFun hc 0) (LO.Propositional.Formula.atom 0 : Sentence)
  rw [twoPointHistory, twoPointHistory, twoPointQuote, twoPointQuote,
    if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩] at this
  exact h (by exact_mod_cast this)

/-- The disagreement, at the coordinate itself.

Kind `N+` non-vacuity witness.
Paper node: `app:ifp` -/
lemma twoPointHistory_ne_at :
    twoPointHistory (1 / 2) 0 (LO.Propositional.Formula.atom 0 : Sentence)
      ≠ twoPointHistory (1 / 3) 0 (LO.Propositional.Formula.atom 0 : Sentence) := by
  rw [twoPointHistory, twoPointHistory, twoPointQuote, twoPointQuote,
    if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
  norm_num

/-- The pair is a finite-support perturbation in this file's own sense, and its support is
exactly `exampleS`: they agree off it (`twoPointHistory_agree`) and differ on it
(`twoPointHistory_ne_at`). -/
lemma twoPointHistory_finiteSupportPerturbation (q q' : ℚ) :
    FiniteSupportPerturbation (twoPointHistory q) (twoPointHistory q') :=
  ⟨exampleS, twoPointHistory_agree q q'⟩

/-- **The corrected `thm:ifp`, at a concrete pair of genuinely different computable
markets.**

Every hypothesis is discharged: both markets are `ComputableMarket`s with real
`Nat.Partrec.Code` tables, they agree off `exampleS`, they *disagree* on it
(`twoPointHistory_ne_at`), and each carries a `MachineFiniteSupportPatch` built from the
run-level lookup.  Nothing is assumed.

Kind `N+` non-vacuity witness.
Paper node: `app:ifp` -/
theorem machine_lic_iff_twoPoint (DP : DeductiveProcess) :
    IsMachineLogicalInductor (twoPointHistory (1 / 2)) DP
      ↔ IsMachineLogicalInductor (twoPointHistory (1 / 3)) DP :=
  machine_lic_iff_example (1 / 2) (1 / 3) _ _ DP
    (computableMarket_twoPoint (1 / 2) (by norm_num) (by norm_num))
    (computableMarket_twoPoint (1 / 3) (by norm_num) (by norm_num))
    (twoPointHistory_agree _ _)
    (twoPointHistory_exact _) (twoPointHistory_exact _)

/-! ## The strictness targets

The two sentences a `Recognizable`-restricted freeze cannot take, one for each half of the
restriction.  They are recorded here — with the negative facts proved, so nothing rests on
inspection — because they are the yardstick for whether a later compiler is genuinely
stronger: a result that covers *these* coordinates is strictly stronger in actual use than
`machine_lic_iff_of_recognizableSupport`, and one that does not is the same theorem under a
new name. -/

/-- A target with a `⊥` subformula: fails `BotFree`, so its escape leaf has infinitely many
codes (`decode_falsum_noncanonical`) and no finite spelling list is exhaustive. -/
def hardSentence : Sentence := (LO.Propositional.Formula.atom 0 : Sentence) ⋏ ⊥

/-- A reserved atom: fails `NoReserved`, so a structured paper-prime block denotes it and
the structured branch of `parseRpn` is reachable at that leaf. -/
def reservedSentence : Sentence :=
  LO.Propositional.Formula.atom (Nat.pair 5 (Nat.pair 0 0))

/-- **`hardSentence` fails `BotFree`.**

Kind `N-` negative witness.  Provenance: (a) `botFree_and`, `botFree_falsum`.
Paper node: `app:ifp` -/
lemma not_botFree_hardSentence : ¬ BotFree hardSentence := by
  rw [hardSentence]
  intro h
  exact botFree_falsum ((botFree_and _ _).mp h).2

/-- **`reservedSentence` fails `NoReserved`.**

Kind `N-` negative witness.  Provenance: (a) `noReserved_atom`.
Paper node: `app:ifp` -/
lemma not_noReserved_reservedSentence : ¬ NoReserved reservedSentence := by
  rw [reservedSentence]
  intro h
  exact (noReserved_atom _).mp h 0 0 rfl

lemma not_recognizable_hardSentence : ¬ Recognizable hardSentence :=
  fun h => not_botFree_hardSentence h.botFree

lemma not_recognizable_reservedSentence : ¬ Recognizable reservedSentence :=
  fun h => not_noReserved_reservedSentence h.noReserved

/-- A two-row coordinate set, one row for each half of the old restriction. -/
def hardS : Finset (ℕ × Sentence) := {(0, hardSentence), (1, reservedSentence)}

lemma mem_hardS_hard : (0, hardSentence) ∈ hardS := by simp [hardS]

lemma mem_hardS_reserved : (1, reservedSentence) ∈ hardS := by simp [hardS]

/-- **`hardS` is outside the reach of the recognizable-support theorem** — both of its rows
are, in fact.  This is what a strictness claim for a later unrestricted compiler has to
beat.

Kind `N-` negative witness.  Provenance: (a) `not_recognizable_hardSentence`.
Paper node: `app:ifp` -/
lemma not_recognizable_hardS : ¬ ∀ p ∈ hardS, Recognizable p.2 := by
  intro h
  exact not_recognizable_hardSentence (h (0, hardSentence) mem_hardS_hard)

/-! ## Strictness: a frozen coordinate the old theorem provably could not reach

`hardSentence` fails `BotFree` (`not_botFree_hardSentence`), so
`machine_lic_iff_of_recognizableSupport` does not apply to any coordinate set containing it
— `not_recognizable_hardS` is that fact, proved rather than asserted.
`machine_lic_iff_of_noReservedSupport` does apply, and this section carries the difference
all the way to a concrete pair of computable markets that differ at exactly that
coordinate.

The construction is `twoPointHistory` with the frozen sentence a parameter; the `atom 0`
instance above is kept because it is inventoried, and this one is what shows the
strengthening is not vacuous. -/

/-- The rational quote table: `q` at `(0, φ)`, zero everywhere else. -/
def pointQuote (φ : Sentence) (q : ℚ) : ℕ → ℕ → ℚ := fun n c =>
  if n = 0 ∧ c = Encodable.encode φ then q else 0

/-- The market it presents. -/
def pointHistory (φ : Sentence) (q : ℚ) : History :=
  fun n χ => (pointQuote φ q n (Encodable.encode χ) : ℝ)

/-- Its single moved coordinate. -/
def pointS (φ : Sentence) : Finset (ℕ × Sentence) := {(0, φ)}

lemma pointQuote_mem_Icc (φ : Sentence) {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n c : ℕ) :
    0 ≤ pointQuote φ q n c ∧ pointQuote φ q n c ≤ 1 := by
  rw [pointQuote]
  split_ifs
  · exact ⟨h0, h1⟩
  · exact ⟨le_refl 0, by norm_num⟩

lemma pointHistory_mem_Icc (φ : Sentence) {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (n : ℕ) (χ : Sentence) :
    0 ≤ pointHistory φ q n χ ∧ pointHistory φ q n χ ≤ 1 := by
  obtain ⟨ha, hb⟩ := pointQuote_mem_Icc φ h0 h1 n (Encodable.encode χ)
  constructor
  · show (0 : ℝ) ≤ ((pointQuote φ q n (Encodable.encode χ) : ℚ) : ℝ)
    exact_mod_cast ha
  · show ((pointQuote φ q n (Encodable.encode χ) : ℚ) : ℝ) ≤ 1
    exact_mod_cast hb

/-- **The table is computable**, as a function of the paired input. -/
lemma computable_pointQuote (φ : Sentence) (q : ℚ) :
    Computable (fun z : ℕ => pointQuote φ q z.unpair.1 z.unpair.2) := by
  have h1 : Computable (fun z : ℕ => decide (z.unpair.1 = 0)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp
  have h2 : Computable (fun z : ℕ =>
      decide (z.unpair.2 = Encodable.encode φ)) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const _)).decide.to_comp
  refine (Computable.cond h1
    (Computable.cond h2 (Computable.const q) (Computable.const 0))
    (Computable.const 0)).of_eq (fun z => ?_)
  rw [pointQuote]
  by_cases ha : z.unpair.1 = 0
  · by_cases hb : z.unpair.2 = Encodable.encode φ
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-- **The market is an honest `ComputableMarket`**, at any frozen sentence.

Kind `N+` non-vacuity witness.  Provenance: (a) `computable_pointQuote`;
(b) `Nat.Partrec.Code.exists_code`.
Paper node: `app:ifp` -/
theorem computableMarket_point (φ : Sentence) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ComputableMarket (pointHistory φ q) := by
  refine ⟨pointHistory_mem_Icc φ h0 h1, ?_⟩
  have hcomp : Computable (fun z : ℕ =>
      Encodable.encode (pointQuote φ q z.unpair.1 z.unpair.2)) :=
    Computable.encode.comp (computable_pointQuote φ q)
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (pointQuote φ q z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨pointQuote φ q, code, fun n χ => rfl, fun z => ?_⟩
  rw [hcode]
  simp

/-- Off the frozen coordinate the two markets agree. -/
lemma pointHistory_agree (φ : Sentence) (q q' : ℚ) :
    ∀ d χ, (d, χ) ∉ pointS φ → pointHistory φ q d χ = pointHistory φ q' d χ := by
  intro d χ hmem
  have hne : ¬(d = 0 ∧ χ = φ) := by
    intro hc
    exact hmem (by simp [pointS, hc.1, hc.2])
  have hq : ∀ r : ℚ, pointQuote φ r d (Encodable.encode χ) = 0 := by
    intro r
    rw [pointQuote, if_neg]
    intro hc
    exact hne ⟨hc.1, Encodable.encode_injective hc.2⟩
  rw [pointHistory, pointHistory, hq, hq]

/-- **The two markets genuinely differ, at the frozen coordinate.**

Kind `N+` non-vacuity witness.
Paper node: `app:ifp` -/
lemma pointHistory_ne_at (φ : Sentence) :
    pointHistory φ (1 / 2) 0 φ ≠ pointHistory φ (1 / 3) 0 φ := by
  rw [pointHistory, pointHistory, pointQuote, pointQuote,
    if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
  norm_num

/-- **No recognizable-support perturbation reaches the `hardSentence` point pair.**  This is
the *perturbation-level* negative the strictness claim actually needs: because
`RecognizableSupportPerturbation` is an existential over the support set `S`, a sentence-level
failure (`not_recognizable_hardSentence`) does not by itself rule the old endpoint out — one
must also force the moved coordinate into *every* admissible `S`.  Here the two markets differ
at `(0, hardSentence)` (`pointHistory_ne_at`), so any `S` witnessing agreement off `S` must
contain it, and then recognizability of its second component fails.

Kind `N-` negative witness.  Provenance: (a) `not_recognizable_hardSentence`,
`pointHistory_ne_at`.
Paper node: `app:ifp` -/
lemma not_recognizableSupport_hardPoint :
    ¬ RecognizableSupportPerturbation
        (pointHistory hardSentence (1 / 2)) (pointHistory hardSentence (1 / 3)) := by
  rintro ⟨S, hrec, hagree⟩
  by_cases hmem : (0, hardSentence) ∈ S
  · exact not_recognizable_hardSentence (hrec _ hmem)
  · exact pointHistory_ne_at hardSentence (hagree 0 hardSentence hmem)

/-- **No no-reserved-support perturbation reaches the `reservedSentence` point pair.**  The
companion perturbation-level negative for the `NoReserved` half: the two markets differ at
`(0, reservedSentence)` (`pointHistory_ne_at`), forcing that coordinate into every admissible
support set, where `NoReserved` of its second component fails
(`not_noReserved_reservedSentence`).

Kind `N-` negative witness.  Provenance: (a) `not_noReserved_reservedSentence`,
`pointHistory_ne_at`.
Paper node: `app:ifp` -/
lemma not_noReservedSupport_reservedPoint :
    ¬ NoReservedSupportPerturbation
        (pointHistory reservedSentence (1 / 2)) (pointHistory reservedSentence (1 / 3)) := by
  rintro ⟨S, hnr, hagree⟩
  by_cases hmem : (0, reservedSentence) ∈ S
  · exact not_noReserved_reservedSentence (hnr _ hmem)
  · exact pointHistory_ne_at reservedSentence (hagree 0 reservedSentence hmem)

/-- `hardSentence` has no reserved-atom subformula, so it is inside the new theorem's
hypothesis — while failing the old one's (`not_recognizable_hardSentence`). -/
lemma noReserved_hardSentence : NoReserved hardSentence := by
  rw [hardSentence, noReserved_and]
  exact ⟨atom_zero_noReserved, noReserved_falsum⟩

/-- **The strictness regression: the corrected theorem at a `⊥`-containing frozen
sentence.**

Every hypothesis is discharged — both markets are `ComputableMarket`s with real
`Nat.Partrec.Code` tables, they agree off the single coordinate `(0, hardSentence)` and
disagree on it (`pointHistory_ne_at`) — and this perturbation is one the previous endpoint
provably could not take: `not_recognizableSupport_hardPoint` establishes
`¬ RecognizableSupportPerturbation` of the two markets outright (not merely that the
sentence fails `Recognizable`), so `machine_lic_iff_of_recognizableSupport` is inapplicable
here by a proved *perturbation-level* negative rather than by inspection.  This is what makes
the strengthening strict *in use* and not only in statement.

Kind `N+` non-vacuity witness.  Provenance: (a) `computableMarket_point`,
`machine_lic_iff_of_finiteSupport`.
Paper node: `app:ifp` -/
theorem machine_lic_iff_hardPoint (DP : DeductiveProcess) :
    IsMachineLogicalInductor (pointHistory hardSentence (1 / 2)) DP
      ↔ IsMachineLogicalInductor (pointHistory hardSentence (1 / 3)) DP :=
  machine_lic_iff_of_finiteSupport _ _ DP
    (computableMarket_point hardSentence (1 / 2) (by norm_num) (by norm_num))
    (computableMarket_point hardSentence (1 / 3) (by norm_num) (by norm_num))
    ⟨pointS hardSentence, pointHistory_agree hardSentence _ _⟩

/-- **The strictness regression at a *reserved* frozen sentence.**

`reservedSentence` is `atom (Nat.pair 5 (Nat.pair 0 0))`, and it fails `NoReserved`
(`not_noReserved_reservedSentence`) — so neither `machine_lic_iff_of_recognizableSupport`
nor `machine_lic_iff_of_noReservedSupport` applies to this perturbation, established outright
by the perturbation-level negative `not_noReservedSupport_reservedPoint` (which forces the
differing coordinate into every admissible support set) rather than by inspection.  It is
exactly the case the structured paper-prime branch of
`parseRpn` exists for: a run may denote this sentence through a block
`[1, 0, pol] ++ 1^L ++ [0] ++ p ++ [19]` whose unary length field is unbounded, and the
freeze's recognizer has to accept every one of them.

Together with `machine_lic_iff_hardPoint` — which does the same for the `BotFree` half —
this is what makes the unrestricted endpoint strictly stronger *in use* rather than only in
statement.

Kind `N+` non-vacuity witness.  Provenance: (a) `computableMarket_point`,
`machine_lic_iff_of_finiteSupport`.
Paper node: `app:ifp` -/
theorem machine_lic_iff_reservedPoint (DP : DeductiveProcess) :
    IsMachineLogicalInductor (pointHistory reservedSentence (1 / 2)) DP
      ↔ IsMachineLogicalInductor (pointHistory reservedSentence (1 / 3)) DP :=
  machine_lic_iff_of_finiteSupport _ _ DP
    (computableMarket_point reservedSentence (1 / 2) (by norm_num) (by norm_num))
    (computableMarket_point reservedSentence (1 / 3) (by norm_num) (by norm_num))
    ⟨pointS reservedSentence, pointHistory_agree reservedSentence _ _⟩

/-- **`pointS reservedSentence` is outside the reach of both earlier endpoints.**

Kind `N-` negative witness.  Provenance: (a) `not_noReserved_reservedSentence`.
Paper node: `app:ifp` -/
lemma not_noReserved_pointS_reserved :
    ¬ ∀ p ∈ pointS reservedSentence, NoReserved p.2 := by
  intro h
  exact not_noReserved_reservedSentence (h (0, reservedSentence) (by simp [pointS]))

#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_of_finiteSupport
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_reservedPoint
#print axioms LogicalInduction.FreezeOracle.not_noReserved_pointS_reserved
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_of_noReservedSupport
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch_ofNoReserved
#print axioms LogicalInduction.FreezeOracle.computableMarket_point
#print axioms LogicalInduction.FreezeOracle.pointHistory_ne_at
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_hardPoint
#print axioms LogicalInduction.FreezeOracle.not_recognizable_hardS
#print axioms LogicalInduction.FreezeOracle.not_recognizable_reservedSentence
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch_ofRecognizable
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_of_recognizableSupport
#print axioms LogicalInduction.FreezeOracle.computableMarket_twoPoint
#print axioms LogicalInduction.FreezeOracle.twoPointHistory_ne_at
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_twoPoint
#print axioms LogicalInduction.FreezeOracle.machine_lic_iff_example
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch_ofTable
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch_example
#print axioms LogicalInduction.FreezeOracle.machineFiniteSupportPatch_pair
#print axioms LogicalInduction.FreezeOracle.decodeBits_oracleOf
#print axioms LogicalInduction.FreezeOracle.oracleOf_mem_FP
#print axioms LogicalInduction.FreezeOracle.runOracleOf

end LogicalInduction.FreezeOracle
