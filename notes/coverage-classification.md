# Per-label coverage-strength classification

_The second half of the M7-ERRATA-AUDIT F9 repair: the endpoint-coverage checker proves every
annotated paper label has an inventory endpoint; this file records **how strong** that coverage
is.  `scripts/check_endpoint_coverage.py` enforces that the table below classifies exactly the
non-excluded annotated labels, so a new label cannot ship without an honest strength call, and a
stale row fails the build._

**Global model disclosure (applies to every row).**  All tiers are **relative to the disclosed
repository model**: sentences are propositional (`Formula ℕ`), and efficient computability is the
fuel-clocked `Nat.Partrec.Code` interpreter (`dd:fuel`, F10) — not the paper's first-order syntax
or a conventional complexity class.  A row marked *complete* claims the paper statement is reached
**within that model**, not that the model equivalence is proved.

**Tier vocabulary**
- **complete** — unconditional over the constructed `LIA` at paper strength; remaining premises
  are ones the paper itself takes (e.g. joint consistency, a Σ₁-sound `Θ ⊇ IΣ₁` for the
  represents-computations clause).
- **conditional** — paper-strength statement, conditional on `[IsLogicalInductor P DP]` (the
  risk-posture conditionality shared by the property tail); no extra representation or
  operational interfaces.
- **qualified** — full strength only for a restricted class or with a retained
  representation/operational interface the paper discharges (each row says which).
- **interface** — the label is covered by definitional/interface structures or component
  lemmas; the paper-strength statement is not a single endpoint.

| label | tier | justification |
|---|---|---|
| def:affcomsen | complete | direct rendering (`AffineCombination`) |
| def:bap | complete | direct rendering (`BoundedCombinationSequence`) |
| def:blcp | qualified | bounded LUV-combination sequence over the threshold-abstracted LUV type |
| def:dedproc | complete | direct rendering (`DeductiveProcess` + computation certificate) |
| def:deferralfunc | complete | direct rendering |
| def:ec | qualified | the `dd:fuel` substitution itself: fuel-clocked interpreter, not a complexity class (F10) |
| def:ece | qualified | P-generability rendered in the fuel/token model |
| def:fuz | qualified | generable weighting in the fuel/token model |
| def:lia | complete | the constructed recursive algorithm (`liaStates`/`liaHistory`) |
| def:lic | complete | range law bundled (F0); trader class is `def:ec`'s (globally disclosed) |
| def:luv | qualified | threshold-sentence abstraction; certified first-order bridge only for the `dd:luv-arith` class (F7) |
| def:trader | complete | direct rendering |
| def:tradestrat | complete | direct rendering |
| lem:mesh | interface | operational mesh-softmax witness structure, not a standalone endpoint |
| thm:affcoh | conditional | analytic capstone over `[IsLogicalInductor]` with the paper's BCS data |
| thm:affpolymax | conditional | same |
| thm:affprovind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:benford | conditional | pseudorandomness premises are the paper's own; maturity constructed (F2) |
| thm:ccee | qualified | quotation/representation data (`QuotationTheoryPresentation`, quote codes) retained |
| thm:cee | qualified | same |
| thm:ceu | qualified | same |
| thm:con | conditional | genuine trader proof over `[IsLogicalInductor]` |
| thm:dontwait | complete | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:dus | qualified | unconditional over `LIA`, but the `M7-DUS-APPROX` approximation/emission data is a retained input |
| thm:ec | qualified | finite-precision threshold-LUV representation (`ApproxValuesUpTo`) retained |
| thm:ei | qualified | indicator linkage over threshold LUVs retained |
| thm:epr | qualified | unconditional-over-LIA variant exists but retains quote-code data |
| thm:er | qualified | representation/reflection data retained |
| thm:expcoh | qualified | representation discharged from arithmetic for `dd:luv-arith` (`expcoh_arith`); general LUVs retain `WorldValued`/`ConvergencePresentation` + mesh-softmax ops |
| thm:exppolymax | qualified | same pattern (`exppolymax_arith`) |
| thm:expprovind | qualified | **fully unconditional for certified `dd:luv-arith`** (all three comparison forms); general LUV-combination forms conditional + exact-theory presentation |
| thm:halts | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:ifp | qualified | efficiently-patchable perturbations only; the paper's unrestricted statement has a recorded erratum (PE1) |
| thm:incons | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lc | conditional | probability measure on completed worlds constructed (F1) over `[IsLogicalInductor]` |
| thm:lex | conditional | propositional rendering over `[IsLogicalInductor]` |
| thm:li | complete | computable finite-support belief-sequence form (F8) |
| thm:lia | complete | the central construction, kernel-clean |
| thm:loe | qualified | varying-sequence linearity via combination provind (+ exact-theory presentation); fully unconditional for `dd:luv-arith` fixed indices |
| thm:loops | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lp | complete | public diagonal derived from the market computation (F3); unconditional over `LIA` |
| thm:nd | conditional | global theory/world premises are the paper's own |
| thm:ob | qualified | prefix-machine presentation and Kraft data retained |
| thm:obu | conditional | over `[IsLogicalInductor]` with the paper's enumeration data |
| thm:pac | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:pazfc | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:peraffkno | conditional | analytic capstone over `[IsLogicalInductor]` |
| thm:perexpkno | qualified | `perexpkno_arith` discharges representation for `dd:luv-arith`; general retains presentation + ops |
| thm:perkno | conditional | over `[IsLogicalInductor]` |
| thm:prand | conditional | paper's pseudorandomness premises; maturity constructed (F2) |
| thm:prandaff | conditional | same |
| thm:prandexp | qualified | same + threshold-LUV representation |
| thm:provind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:recunbiasedaff | conditional | maturity constructed internally (F2) |
| thm:recurringunbiasedness | conditional | same |
| thm:recurringunbiasednessexp | qualified | threshold-LUV representation; PE2 hypothesis-swap erratum recorded |
| thm:ref | qualified | representation/reflection data retained |
| thm:scon | complete | fixed and growing forms unconditional (F4) |
| thm:simcal | conditional | maturity constructed internally (F2) |
| thm:st | qualified | representation/reflection data retained |
| thm:strict | qualified | strict-separator presentation retained |
| thm:tbo | conditional | over `[IsLogicalInductor]` |
| thm:wub | qualified | unconditional-over-LIA variants retain the paper's operational feedback data |
| thm:wubaff | qualified | feedback emission/truth witnesses retained |
| thm:wubexp | qualified | same + threshold-LUV representation (`wubexp_arith` discharges the representation half for `dd:luv-arith`) |
