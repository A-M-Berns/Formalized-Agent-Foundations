/-
# The run-level lookup, and a `RunOracle` for a finite table

`FreezeStep.RunOracle` is the one hole left in the machine-class freeze: given the incoming
day's token block and the buffered sentence run's bits, return the frozen suffix.  This file
builds one, for a quote table presented as a finite list of entries.

The lookup is a **constant-depth chain**, not a parser.  For each table entry it makes two
tests: the day, against a fixed numeral (`TokenFold.ifNumEq_mem_FP`), and the buffered run,
against each of the finitely many complete spellings of that entry's sentence
(`TokenFold.ifMatch_mem_FP`).  That the spellings are finitely many is
`RpnFreeze.spellings`, and that membership in that list *is* denotation is
`RpnFreeze.parseRpn_iff_mem_spellings` — which is where the table's side conditions enter.

## What this file assumes, and where it is written down

`TablePresentation` below carries the conditions, and they are the same three already
collected in `CanonicalCodes.lean`'s "The recognition side conditions, in one place":

* every table sentence is `Recognizable` (`BotFree` and `NoReserved`) — otherwise the
  spelling list is not exhaustive and the chain rejects runs it should accept;
* the entry list presents `S` and `quote` faithfully (`lookup_eq`);
* the constant output budget, which here is *derived* rather than assumed
  (`oracleOf_length_le`): the emitted suffix is one of finitely many constant words.

Nothing here is a restriction on the freeze, the trader, or the market.  All of it is a
property of the table being frozen.
-/
import LogicalInduction.Construction.Witnesses.FreezeStep

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

/-- Look a buffered run and a day up in the table, taking the first matching row. -/
def tableLookup (entries : List TableEntry) (b : List ℕ) (D : ℕ) : Option ℚ :=
  match entries with
  | [] => none
  | e :: rest =>
      if e.day = D ∧ b ∈ RpnFreeze.spellings e.sentence then some e.value
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

/-- Does the buffer spell any of these token lists? -/
def spellChain (sps : List (List ℕ)) (hit miss bufW : List Bool) : List Bool :=
  match sps with
  | [] => miss
  | s :: rest => if decodeBits bufW = s then hit else spellChain rest hit miss bufW

/-- **The oracle**: a constant-depth chain over the table's rows. -/
def oracleOf (entries : List TableEntry) (v : List Bool) : List Bool :=
  match entries with
  | [] => []
  | e :: rest =>
      if NumEqBits e.day (fstBlock v) then
        spellChain (RpnFreeze.spellings e.sentence) (entryBits e)
          (oracleOf rest v) (sndBlock v)
      else oracleOf rest v

/-! ### What the chain emits -/

lemma decodeBits_spellChain : ∀ (sps : List (List ℕ)) (hit miss bufW : List Bool),
    decodeBits (spellChain sps hit miss bufW)
      = if decodeBits bufW ∈ sps then decodeBits hit else decodeBits miss
  | [], hit, miss, bufW => by rw [spellChain]; simp
  | (s :: sps), hit, miss, bufW => by
      rw [spellChain]
      by_cases h : decodeBits bufW = s
      · rw [if_pos h, if_pos (by rw [h]; exact List.mem_cons_self ..)]
      · rw [if_neg h, decodeBits_spellChain sps hit miss bufW]
        by_cases h2 : decodeBits bufW ∈ sps
        · rw [if_pos h2, if_pos (List.mem_cons_of_mem _ h2)]
        · rw [if_neg h2, if_neg (by
            intro hc
            rcases List.mem_cons.mp hc with hc | hc
            · exact h hc
            · exact h2 hc)]

@[simp] lemma decodeBits_entryBits (e : TableEntry) :
    decodeBits (entryBits e) = [1, Encodable.encode e.value, 8] := by
  rw [entryBits, decodeBits_tokBits]

/-- **The chain computes the table lookup.**

Proof kind: `P` proved.  Provenance: (a) `numEqBits_spec`, `decodeBits_spellChain`.
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
      rw [oracleOf, fstBlock_pair, sndBlock_pair]
      by_cases hday : NumEqBits e.day (digitsToBits cur)
      · have hd : digitVal cur = e.day := (numEqBits_spec e.day cur hcur).mp hday
        rw [if_pos hday, decodeBits_spellChain]
        by_cases hsp : decodeBits bufW ∈ RpnFreeze.spellings e.sentence
        · have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
              = some e.value := by
            rw [tableLookup, if_pos ⟨hd.symm, hsp⟩]
          rw [if_pos hsp, decodeBits_entryBits]
          simp only [selRunOf, quoteRunOf, hlk]
          simp
        · have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
              = tableLookup rest (decodeBits bufW) (digitVal cur) := by
            rw [tableLookup, if_neg (fun hc => hsp hc.2)]
          rw [if_neg hsp, decodeBits_oracleOf rest cur hcur bufW]
          simp only [selRunOf, quoteRunOf, hlk]
      · have hd : digitVal cur ≠ e.day := fun hc =>
          hday ((numEqBits_spec e.day cur hcur).mpr hc)
        have hlk : tableLookup (e :: rest) (decodeBits bufW) (digitVal cur)
            = tableLookup rest (decodeBits bufW) (digitVal cur) := by
          rw [tableLookup, if_neg (fun hc => hd hc.1.symm)]
        rw [if_neg hday, decodeBits_oracleOf rest cur hcur bufW]
        simp only [selRunOf, quoteRunOf, hlk]

/-! ### Well-formedness and the constant budget -/

lemma blockWF_spellChain : ∀ (sps : List (List ℕ)) (hit miss bufW : List Bool),
    BlockWF hit → BlockWF miss → BlockWF (spellChain sps hit miss bufW)
  | [], hit, miss, bufW, _, hm => by rw [spellChain]; exact hm
  | (s :: sps), hit, miss, bufW, hh, hm => by
      rw [spellChain]
      split_ifs
      · exact hh
      · exact blockWF_spellChain sps hit miss bufW hh hm

lemma blockWF_oracleOf : ∀ (entries : List TableEntry) (v : List Bool),
    BlockWF (oracleOf entries v)
  | [], v => by rw [oracleOf]; exact BlockWF.nil
  | (e :: rest), v => by
      rw [oracleOf]
      split_ifs
      · exact blockWF_spellChain _ _ _ _ (blockWF_tokBits _) (blockWF_oracleOf rest v)
      · exact blockWF_oracleOf rest v

/-- The constant output budget: the widest suffix the table can emit. -/
def oracleLen (entries : List TableEntry) : ℕ :=
  entries.foldr (fun e n => max (entryBits e).length n) 0

lemma length_spellChain_le : ∀ (sps : List (List ℕ)) (hit miss bufW : List Bool) (n : ℕ),
    hit.length ≤ n → miss.length ≤ n → (spellChain sps hit miss bufW).length ≤ n
  | [], hit, miss, bufW, n, _, hm => by rw [spellChain]; exact hm
  | (s :: sps), hit, miss, bufW, n, hh, hm => by
      rw [spellChain]
      split_ifs
      · exact hh
      · exact length_spellChain_le sps hit miss bufW n hh hm

lemma oracleOf_length_le : ∀ (entries : List TableEntry) (v : List Bool),
    (oracleOf entries v).length ≤ oracleLen entries
  | [], v => by rw [oracleOf, oracleLen]; simp
  | (e :: rest), v => by
      rw [oracleOf, oracleLen, List.foldr_cons]
      have hrec : (oracleOf rest v).length ≤ oracleLen rest := oracleOf_length_le rest v
      split_ifs
      · exact length_spellChain_le _ _ _ _ _ (le_max_left _ _)
          (le_trans hrec (le_max_right _ _))
      · exact le_trans hrec (le_max_right _ _)

/-! ### Membership -/

lemma spellChain_mem_FP : ∀ (sps : List (List ℕ)) {B H M : List Bool → List Bool},
    B ∈ FP → H ∈ FP → M ∈ FP →
    (fun z => spellChain sps (H z) (M z) (B z)) ∈ FP
  | [], B, H, M, _, _, hM => by
      have heq : (fun z => spellChain [] (H z) (M z) (B z)) = M := by
        funext z; rw [spellChain]
      rwa [heq]
  | (s :: sps), B, H, M, hB, hH, hM => by
      have hrec := spellChain_mem_FP sps hB hH hM
      have h := ifMatch_mem_FP s hB hH hrec
      have heq : (fun z => if decodeBits (B z) = s then H z
            else spellChain sps (H z) (M z) (B z))
          = fun z => spellChain (s :: sps) (H z) (M z) (B z) := by
        funext z; rw [spellChain]
      rwa [heq] at h

/-- **The chain is polynomial time**: a fixed-depth nest of a numeral test and a
spelling test, one level per table row.

Proof kind: `C` composition.  Provenance: (b) `ifNumEq_mem_FP`, `ifMatch_mem_FP`.
Paper node: `app:ifp` -/
lemma oracleOf_mem_FP : ∀ (entries : List TableEntry), oracleOf entries ∈ FP
  | [] => by
      have heq : oracleOf [] = fun _ : List Bool => ([] : List Bool) := by
        funext v; rw [oracleOf]
      rw [heq]; exact constFn_mem_FP []
  | (e :: rest) => by
      have hrec := oracleOf_mem_FP rest
      have hspell : (fun v => spellChain (RpnFreeze.spellings e.sentence) (entryBits e)
          (oracleOf rest v) (sndBlock v)) ∈ FP :=
        spellChain_mem_FP _ sndBlock_mem_FP (constFn_mem_FP _) hrec
      have h := ifNumEq_mem_FP fstBlock_mem_FP e.day hspell hrec
      have heq : (fun v => if NumEqBits e.day (fstBlock v) then
            spellChain (RpnFreeze.spellings e.sentence) (entryBits e)
              (oracleOf rest v) (sndBlock v)
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

/-- **On a run that parses, the two lookups agree.**  This is where `Recognizable` is
used, and the only place. -/
lemma tableLookup_eq_on : ∀ (entries : List TableEntry),
    (∀ e ∈ entries, Recognizable e.sentence) →
    ∀ {b : List ℕ} {φ : Sentence}, parseRpn b.length b = some (φ, []) → ∀ D : ℕ,
    tableLookup entries b D = tableLookupOn entries φ D
  | [], _, b, φ, _, D => rfl
  | (e :: rest), hrec, b, φ, hb, D => by
      have hrece : Recognizable e.sentence := hrec e (List.mem_cons_self ..)
      have hiff : b ∈ RpnFreeze.spellings e.sentence ↔ e.sentence = φ := by
        rw [← RpnFreeze.parseRpn_iff_mem_spellings hrece b]
        constructor
        · intro h
          rw [hb] at h
          exact ((Prod.mk.inj (Option.some.inj h)).1).symm
        · intro h; rw [h]; exact hb
      rw [tableLookup, tableLookupOn]
      by_cases hc : e.day = D ∧ e.sentence = φ
      · rw [if_pos ⟨hc.1, hiff.mpr hc.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, hiff.mp h.2⟩), if_neg hc]
        exact tableLookup_eq_on rest
          (fun e' he' => hrec e' (List.mem_cons_of_mem _ he')) hb D

/-- The conditions under which an entry list presents a market's frozen quote table.

Both are properties of the **table**, not of the freeze: the sentences must be recognizable
(`CanonicalCodes.lean`'s two per-sentence conditions, bundled as `Recognizable`), and the
list must name exactly the coordinates of `S` with their quotes. -/
structure TablePresentation (S : Finset (ℕ × Sentence)) (quote : ℕ → Sentence → ℚ)
    (entries : List TableEntry) : Prop where
  /-- Every table sentence is recognizable from its run. -/
  recognizable : ∀ e ∈ entries, Recognizable e.sentence
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
  rw [selRunOf, tableLookup_eq_on entries htab.recognizable hb D, htab.lookup_eq D φ,
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
    rw [tableLookup_eq_on entries htab.recognizable hb D, htab.lookup_eq D φ]
  have hmem : (D, φ) ∈ S := by
    by_contra hc
    rw [selRunOf, hlk, if_neg hc] at hsel
    simp at hsel
  rw [quoteRunOf, hlk, if_pos hmem, quoteCodeOf_decode D _ (Encodable.encodek φ)]
  simp

/-! ## The patch, for a presented table -/

/-- **`MachineFiniteSupportPatch` for any market whose frozen table is presented by a
recognizable entry list.**

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
    (ha : ∀ pol fc : ℕ, a ≠ Nat.pair 7 (Nat.pair pol fc)) :
    Recognizable (LO.Propositional.Formula.atom a) where
  botFree := botFree_atom a
  noReserved := ha

/-- Atom `0` is not reserved: every reserved payload is positive. -/
lemma atom_zero_noReserved : ∀ pol fc : ℕ, (0 : ℕ) ≠ Nat.pair 7 (Nat.pair pol fc) := by
  intro pol fc h
  have hpos : 0 < Nat.pair 7 (Nat.pair pol fc) := by
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
  recognizable := by
    intro e he
    simp only [exampleEntries, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact recognizable_atom 0 atom_zero_noReserved
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
