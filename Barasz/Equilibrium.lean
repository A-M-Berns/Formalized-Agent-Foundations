/-
  Program equilibrium as Nash equilibrium of the "open-source game."

  In the program game, each player submits source code (a modal agent).
  The payoffs are determined by running the agents against each other.
  A program equilibrium is a Nash equilibrium of this game.

  Key results to formalize:
  - (PrudentBot, PrudentBot) is a program equilibrium of the PD
  - This equilibrium achieves mutual cooperation (Reward, Reward)
  - The standard (Defect, Defect) Nash equilibrium is Pareto-dominated

  Connects: Barasz.Game (Nash equilibrium)
            Barasz.Cooperation (modal agents, cooperation)
-/

import Barasz.Game
import Barasz.Cooperation
