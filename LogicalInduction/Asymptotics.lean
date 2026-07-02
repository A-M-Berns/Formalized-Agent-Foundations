/-
# Asymptotics (`dd:asymp`)

The single home for the limit vocabulary used across the property tail: `≈ₙ` / `≳ₙ`,
"eventually within ε", and "converges to". Built on Mathlib's
`Tendsto (· − ·) atTop (𝓝 0)` and `∀ᶠ n in atTop, …`. Define each idiom **once** here;
do not redefine per file.

Convention: state results in the **limiting** form by default (the downstream deference
work consumes it); add the finite-stage form only where a consumer needs it.

TODO(blueprint:dd:asymp): define `≈ₙ`, `≳ₙ`, and the eventually-within-ε predicate.
-/

namespace LogicalInduction

end LogicalInduction
