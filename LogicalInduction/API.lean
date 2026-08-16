import LogicalInduction.Properties

/-!
# Logical Induction consumer API

This is the recommended import for research that uses the logical-induction framework
and its general property theorems:

```lean
import LogicalInduction.API
```

The supported vocabulary includes `Sentence`, valuations and markets (`History`),
`PCWorld`, `DeductiveProcess`, `EF`, `Strategy`, `Trader`, exploitation,
`EfficientlyComputable`, `IsLogicalInductor`, affine combinations, LUVs and
expectations, the shared asymptotic relations, and the `lic_*` property families.

This import intentionally stops before `LogicalInduction.Construction`: downstream work
on markets, traders, variants of the criterion, and new consequences should not need the
LIA compiler, digit-stream implementation, or concrete representation witnesses.  Lean
does expose declarations from transitive imports, but their visibility is not a stability
promise.  In particular, raw `Nat.Partrec.Code`, clock/digit emitters, RPN parsing, and
property-proof trader implementations are not the recommended consumer interface.

For the concrete LIA existence endpoints, import
`LogicalInduction.Construction.LIACompiler`.  Import `LogicalInduction` only when the
complete construction and all witness machinery are actually needed.

## Honest efficiency and logical-substrate boundaries

`EfficientlyComputable` is this formalization's symbol-metered, fuel-clocked
`Nat.Partrec.Code.evaln` model (`dd:fuel`), not a hidden machine-complexity class.  No
theorem says that every polynomial-time trader in the paper's intended sense belongs to
it.  `RpnSentenceCodes`, `RpnSpliceStream.ec`, and
`EfficientlyComputable.ofSingleTradeBlocks`/`ofTradeBlocks` are the supported high-level
certification interfaces when clients build new traders.

The propositional LUV presentation and the `dd:mesh` approximation remain part of the
statements that use them.  Likewise, `lic_iff_of_finitePerturbation` retains its explicit
`EfficientPrefixPatch` qualification; this API does not manufacture a witness or conceal
that the repository currently has none.  The detailed disclosures remain authoritative in
`LogicalInduction/README.md` and the model card in `Framework/Computable.lean`.
-/
