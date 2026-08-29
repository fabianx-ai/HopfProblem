import Lib

/-!
# Per-export axiom audit for the reusable library

Compile this file directly. It deliberately is not imported by `Lib.lean`, because `#print axioms`
is an evidence command rather than library content.
-/

#print axioms Lib.LinearAlgebra.CyclicAverage.cyclicAverage
#print axioms Lib.LinearAlgebra.CyclicAverage.mul_sum_powers_eq_sum_powers
#print axioms Lib.LinearAlgebra.CyclicAverage.sum_powers_mul_eq_sum_powers
#print axioms Lib.LinearAlgebra.CyclicAverage.mul_cyclicAverage
#print axioms Lib.LinearAlgebra.CyclicAverage.cyclicAverage_mul
#print axioms Lib.LinearAlgebra.CyclicAverage.cyclicAverage_apply_of_fixed
#print axioms Lib.LinearAlgebra.CyclicAverage.isProj_cyclicAverage
#print axioms Lib.LinearAlgebra.CyclicAverage.cyclicAverage_idempotent
#print axioms Lib.LinearAlgebra.CyclicAverage.range_cyclicAverage
#print axioms Lib.LinearAlgebra.CyclicAverage.comp_cyclicAverage

#print axioms Lib.LinearAlgebra.LatticeOrbitIndex.latticeMap
#print axioms Lib.LinearAlgebra.LatticeOrbitIndex.LatticeOrbits
#print axioms Lib.LinearAlgebra.LatticeOrbitIndex.latticeMap_injective
#print axioms Lib.LinearAlgebra.LatticeOrbitIndex.natCard_latticeOrbits_eq_natAbs_det

#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange_zero
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange_apply
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange_mul_exchange
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchangeEquiv
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchangeEquiv_toLinearMap
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchangeEquiv_apply
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchangeEquiv_symm_toLinearMap
#print axioms Lib.LinearAlgebra.SquareZeroExchange.quadratic_term_eq_zero
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange_preserves_bilin
#print axioms Lib.LinearAlgebra.SquareZeroExchange.exchange_preserves_bilin_of_isSkewAdjoint
