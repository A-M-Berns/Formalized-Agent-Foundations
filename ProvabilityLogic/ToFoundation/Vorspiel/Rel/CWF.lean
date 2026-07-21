module

public import Foundation.Vorspiel.Rel.CWF

/-!
Foundation used to name the height function of a converse well-founded relation
`fcwHeight`, but `cwfHeight` was the correct/intended name (matching the
`ConverseWellFounded`/`IsConverseWellFounded` naming already used there). This has
been resolved upstream by the `fcwHeight` → `cwfHeight` rename in `b62b3bac` (#840),
so `cwfHeight` and its API now live directly in `Foundation.Vorspiel.Rel.CWF`.

What remains staged here is only the content that is still missing upstream:
`ConverseWellFounded.irrefl` and the `Std.Irrefl (flip r) → Std.Irrefl r` instance.
-/

@[expose]
public section

section

variable {α} {r : Rel α α}

instance [Std.Irrefl (flip r)] : Std.Irrefl r := by
  constructor;
  have := Std.Irrefl.irrefl (r := flip r);
  simpa;

lemma ConverseWellFounded.irrefl [IsConverseWellFounded α r] : Std.Irrefl r := by
  have := WellFounded.irrefl (r := flip r) IsConverseWellFounded.cwf;
  infer_instance;

end
