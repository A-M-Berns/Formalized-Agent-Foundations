import APITests.LogicalInduction
import APITests.ModalAgents
import APITests.CartesianFrames
import APITests.FiniteFactoredSets
import APITests.Condensation
import APITests.ShannonInformation
import APITests.ShannonInformationFiniteEntropy
import APITests.ShannonInformationChainRule
import APITests.ShannonInformationInequalities
import APITests.ShannonInformationDerived

/-! Client-style compilation tests for every completed paper's supported API, plus the
shared (non-paper) `ShannonInformation` layer.

`APITests.Condensation` is here although `condensation` is still registered `in-progress`:
the registry's `api`/`api_test` keys become *mandatory* at `completed`, but they may be
filled in early, and the test is only useful if it is in the default build from the day it
lands.

`APITests.ShannonInformationFiniteEntropy` is split out from `APITests.ShannonInformation`
because it needs a targeted `Mathlib.Probability.Distributions.Geometric` import that the
rest of the API tests deliberately do without.  `APITests.ShannonInformationChainRule`
builds on it — it reuses that file's constructed geometric witness rather than rebuilding
one — so it imports it rather than `APITests.ShannonInformation`.  `…Inequalities` and
`…Derived` continue the same chain: `…Derived` reuses `…Inequalities`' infinite-range
`geomPair`. -/
