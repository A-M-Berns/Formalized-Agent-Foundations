/-
  Modal agent framework built on GL (Gödel-Löb provability logic).

  An agent is a modal formula φ(p) where p is the opponent's action atom.
  The agent "cooperates" when □φ is provable in GL, i.e., the agent's
  source code provably outputs Cooperate.

  Key imports from Foundation:
  - LO.Modal.Formula        (modal formula type with □, atoms, connectives)
  - Modal.GL                (the Hilbert system GL = K + Löb axiom)
  - GL Kripke completeness  (finite model property, decidability)

  Defines: Agent, cooperates_against, mutual_cooperation.
-/

import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness
