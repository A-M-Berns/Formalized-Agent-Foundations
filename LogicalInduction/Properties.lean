/-
# Part III — Property tail (`LogicalInduction.Properties`)

Every property is conditioned on `[IsLogicalInductor P]` and proved via the
assume-fail → build-trader → invoke-criterion pattern, with the exploiting trader's
efficient computability certified through `EF.cost`. Grouped by paper subsection (see
roadmap §3, Part III). **Bold = M3 downstream-priority slice** (discharges deference
hypotheses).

* Convergence / Coherence:    **`thm:con`**, **`thm:lc`**
* Timely learning:            **`thm:provind`**, `thm:perkno`, `thm:tbo`
* Affine lifts (via `thm:affpolymax`): `thm:affprovind`, `thm:affcoh`, `thm:peraffkno`,
    `thm:recunbiasedaff`, `thm:wubaff`, `thm:prandaff`
* Calibration / unbiasedness: `thm:simcal`, `thm:recurringunbiasedness`, `thm:wub`
* Statistical patterns:       `thm:benford`, `thm:prand`
* Logical relationships:      `thm:lex`
* Non-Dogmatism / closure:    **`thm:nd`**, `thm:ifp`, `thm:obu`, `thm:ob`, `thm:dus`,
    `thm:strict`, `thm:scon`
* Expectations (LUV lifts):   **`thm:ec`**, **`thm:loe`**, `thm:ei`, **`thm:expprovind`**,
    `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`,
    `thm:wubexp`, `thm:prandexp`
* Trust in consistency:       `thm:pac`, `thm:pazfc`, `thm:incons`
* Halting:                    `thm:halts`, `thm:loops`, `thm:dontwait`
* Introspection:              `thm:ref`, `thm:lp`, `thm:epr`
* Self-Trust:                 `thm:er`, **`thm:cee`**, **`thm:ceu`**, **`thm:ccee`**,
    **`thm:st`**

Naming caution (from the deference audit): the shorthand "cee" = the paper's `thm:ceu`
*No Expected Net Update*; the paper's `thm:cee` is the distinct *Expected Future
Expectations*. Don't conflate them.

This Part will certainly grow past one file — promote it to a `Properties/` directory
(one file per family) plus this file as the roll-up when it does.
-/

namespace LogicalInduction

end LogicalInduction
