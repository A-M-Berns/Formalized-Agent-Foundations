module

public import ProvabilityLogic.Hilbert.Basic
public import ProvabilityLogic.Kripke.Cone

@[expose]
public section

variable {α : Type u}

abbrev Logic (α) := Set (Formula α)

end
