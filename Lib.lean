import Lib.GroupTheory.Abelianization.SemidirectProduct
import Lib.GroupTheory.SplitExtension
import Lib.GroupTheory.TwoExceptionalGluing
import Lib.HomologicalAlgebra.UnitTransgression
import Lib.LinearAlgebra.CyclicAverage
import Lib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Lib.LinearAlgebra.SquareZero

/-!
# Reusable V10 Section 6 library

This root exports proof-independent mathematics extracted from checked V10 modules and checked in
the Hopf development. Files below `Lib/` do not import `S6Shortcuts`, `S6`, `Hopf`, `Challenge`,
or `Solution`; proof-specific data and adapters live downstream.

The exported modules contain the reusable algebraic results formalized from V10 Section 6. Results
which still lack a Lean proof are documented as gaps rather than represented by placeholders.
-/
