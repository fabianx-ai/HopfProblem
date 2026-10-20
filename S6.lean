import Lib
import S6.CyclicAverage
import S6.LatticeOrbitIndex
import S6.SquareZeroExchange
import S6.TwoExceptionalGluing
import S6.UnitTransgression

/-!
# V10 Section 6 paper adapters

This root exports unconditional finite certificates and paper-facing adapters from the companion
V10 short-proof project. Reusable proof-independent machinery lives under `Lib/`; the `S6/`
modules connect that library to the paper's concrete data. This root does not provide the analytic
construction and makes no assertion that the six-sphere carries a complex structure.
-/
