module

public import ProvabilityLogic.Hilbert.GL.Basic
public import ProvabilityLogic.Kripke.Cone

@[expose]
public section

open scoped Formula

variable {α : Type u}

abbrev Logic (α) := Set (Formula α)

end
