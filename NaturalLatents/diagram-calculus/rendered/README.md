# Rendered diagrams

`mediation.tex` and `determinism.tex` are emitted by `render` in `../Spike.lean` — they are
not hand-written. That is requirement **R1.5**: what is rendered is derived from the same
value the theorems are about.

Regenerate with:

```sh
lake env lean NaturalLatents/diagram-calculus/Spike.lean   # the two #evals print them
```

## How these are meant to be checked

Side by side against the paper's PNGs, **by a human** (R1.3, R1.4). It is not possible to
prove a renderer matches a raster image. The claim this directory supports is "a reader can
compare these against Figures 1 and 8", never "verified equivalent".

| rendered | paper figure | source PNG | compared |
| --- | --- | --- | --- |
| `mediation.tex` | Fig. 1, the Mediation condition | `mediation.png` | ⬜ not yet |
| `determinism.tex` | the `Y ← X → Y` notation (p. 2, and inside Figs 4–9) | — | ⬜ not yet |

Both are marked *not yet* deliberately: the spike demonstrates that rendering is mechanical,
it does not claim the comparison has been done. Doing it is cheap and belongs with the real
encoding, not with a feasibility probe.

Note what `determinism.tex` shows: `\Lambda'` appears at **two distinct nodes**, which is
the whole point of requirement R2.1. A renderer over an encoding that identified nodes with
variables could not produce this picture.
