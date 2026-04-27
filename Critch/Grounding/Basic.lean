/-
  Grounding bounded provability in Foundation's restricted provability.

  This file will package `Theory.RestrictedProvable` as the concrete bounded
  provability predicate for Layer B.
-/

import Critch.BoundedProvability.Basic
import Foundation.FirstOrder.Incompleteness.RestrictedProvability

namespace LO

namespace FirstOrder
namespace Critch

open Arithmetic

variable {L : Language} [L.ReferenceableBy ℒₒᵣ] [L.Encodable] [L.LORDefinable]

noncomputable def restrictedBoundedProvability (T : Theory L) [T.Δ₁] :
    BoundedProvability 𝗜𝚺₁ T where
  prov := fun e ↦ (T.restrictedProvable e).val

end Critch
end FirstOrder
end LO
