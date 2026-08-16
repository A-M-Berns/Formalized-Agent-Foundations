import ModalAgents.Behavioral

/-!
# Modal Agents consumer API

The supported downstream import for modal-agent and open-source-game research is:

```lean
import ModalAgents.API
```

Its main vocabulary is `ModalAgent`, `Modalized`, `outcome`, `Cooperates`, `Defects`,
`ProvablyDefects`, behavioral equivalence `BehavEquiv` (notation `≈` after
`open scoped ModalAgent`), the four concrete bots, the fixed-point interface, the
cooperation theorems, and the arithmetic lifts.

The recursive `F_of`/substitution development and most of `GlFixedPointBridge` are proof
infrastructure, not a recommended dependency surface.  `GlFixedPointBridge.toSeq` remains
a supported interoperability boundary because it occurs in the arithmetic-lift results;
the vendored provability-logic implementation behind it is not thereby designated as
ModalAgents API.

`Defects X Y` means that GL does not prove cooperation.  It is strictly weaker than
`ProvablyDefects X Y`, which positively proves the negated outcome and is the form that
has an arithmetic lift.  The three irreducibly weak defection results and their
`□⊥`/`□□⊥` obstructions, as well as the restriction to modal rather than arbitrary
arithmetic agents, remain exactly as disclosed in `ModalAgents/README.md`.
-/
