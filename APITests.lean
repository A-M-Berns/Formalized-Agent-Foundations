import APITests.LogicalInduction
import APITests.ModalAgents
import APITests.CartesianFrames
import APITests.FiniteFactoredSets
import APITests.ShannonInformation
import APITests.ShannonInformationFiniteEntropy

/-! Client-style compilation tests for every completed paper's supported API, plus the
shared (non-paper) `ShannonInformation` layer.

`APITests.ShannonInformationFiniteEntropy` is split out from `APITests.ShannonInformation`
because it needs a targeted `Mathlib.Probability.Distributions.Geometric` import that the
rest of the API tests deliberately do without. -/
