import Lib.LinearAlgebra.CyclicAverage
import Lib.LinearAlgebra.LatticeOrbitIndex
import Lib.LinearAlgebra.SquareZeroExchange

/-!
# Reusable V10 Section 6 library

This root exports proof-independent mathematics extracted from checked V10 modules and checked in
the Hopf development. Files below `Lib/` do not import `S6Shortcuts`, `S6`, `Hopf`, `Challenge`,
or `Solution`; proof-specific data and adapters live downstream.

The current first extraction contains the linear-algebraic results from V10 Section 6. Group and
homological exports are added in the next coherent migration commit.
-/
