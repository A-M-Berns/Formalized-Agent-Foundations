module

public import Foundation.Vorspiel.Rel.CWF

/-!
Foundation now names the height function of a converse well-founded relation
`cwfHeight`, matching the `ConverseWellFounded`/`IsConverseWellFounded` naming already
used there (superseding the earlier `fcwHeight` name); `cwfHeight` and its API now live
directly in `Foundation.Vorspiel.Rel.CWF`.

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
