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

#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingDefect
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingDefect_common_projected_seed
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingDefect_consecutive
#print axioms Lib.GroupTheory.TwoExceptionalGluing.relationMap
#print axioms Lib.GroupTheory.TwoExceptionalGluing.GluingCokernel
#print axioms Lib.GroupTheory.TwoExceptionalGluing.bezoutQ
#print axioms Lib.GroupTheory.TwoExceptionalGluing.classifyingMap
#print axioms Lib.GroupTheory.TwoExceptionalGluing.classifyingMap_relationMap_eq_zero
#print axioms Lib.GroupTheory.TwoExceptionalGluing.range_relationMap_eq_ker_classifyingMap
#print axioms Lib.GroupTheory.TwoExceptionalGluing.classifyingMap_surjective
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingCokernelEquivZMod
#print axioms Lib.GroupTheory.TwoExceptionalGluing.GluingGroup
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingGroupCommGroup
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingGroupEquivZMod
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingCokernelEquivIntOfDefectEqZero
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingCokernel_subsingleton_of_defect_natAbs_eq_one
#print axioms Lib.GroupTheory.TwoExceptionalGluing.consecutive_gluingCokernel_subsingleton
#print axioms Lib.GroupTheory.TwoExceptionalGluing.isMulCommutative_of_twoExceptionalRelations
#print axioms Lib.GroupTheory.TwoExceptionalGluing.GluingGenerator
#print axioms Lib.GroupTheory.TwoExceptionalGluing.gluingRelations
#print axioms Lib.GroupTheory.TwoExceptionalGluing.PresentedGluingGroup
#print axioms Lib.GroupTheory.TwoExceptionalGluing.presentedGluingGroup_isMulCommutative
#print axioms Lib.GroupTheory.TwoExceptionalGluing.common_projected_seed_observables

#print axioms Lib.GroupTheory.SplitExtension.coinvariantRelations
#print axioms Lib.GroupTheory.SplitExtension.coinvariantKernel
#print axioms Lib.GroupTheory.SplitExtension.coinvariantKernelNormal
#print axioms Lib.GroupTheory.SplitExtension.Coinvariants
#print axioms Lib.GroupTheory.SplitExtension.coinvariantsCommGroup
#print axioms Lib.GroupTheory.SplitExtension.coinvariantOf
#print axioms Lib.GroupTheory.SplitExtension.coinvariantOf_action
#print axioms Lib.GroupTheory.SplitExtension.semidirectToFactors
#print axioms Lib.GroupTheory.SplitExtension.abelianizationToFactors
#print axioms Lib.GroupTheory.SplitExtension.coinvariantsToAbelianization
#print axioms Lib.GroupTheory.SplitExtension.coinvariantsToAbelianization_mk
#print axioms Lib.GroupTheory.SplitExtension.abelianizationToFactors_of_inl
#print axioms Lib.GroupTheory.SplitExtension.abelianizationToFactors_of_inr
#print axioms Lib.GroupTheory.SplitExtension.abelianizationToFactors_coinvariantsToAbelianization_mk
#print axioms Lib.GroupTheory.SplitExtension.factorsToAbelianization
#print axioms Lib.GroupTheory.SplitExtension.semidirectAbelianizationEquiv
#print axioms Lib.GroupTheory.SplitExtension.splittingAction
#print axioms Lib.GroupTheory.SplitExtension.semidirectToExtension
#print axioms Lib.GroupTheory.SplitExtension.semidirectToExtension_apply
#print axioms Lib.GroupTheory.SplitExtension.splittingMulEquiv
#print axioms Lib.GroupTheory.SplitExtension.splitExtensionAbelianizationEquiv

#print axioms Lib.HomologicalAlgebra.UnitTransgression.transgressionMap
#print axioms Lib.HomologicalAlgebra.UnitTransgression.TransgressionKernel
#print axioms Lib.HomologicalAlgebra.UnitTransgression.TransgressionCokernel
#print axioms Lib.HomologicalAlgebra.UnitTransgression.transgressionMap_apply
#print axioms Lib.HomologicalAlgebra.UnitTransgression.transgressionKernel_subsingleton
#print axioms Lib.HomologicalAlgebra.UnitTransgression.transgressionCokernelEquivZMod
#print axioms Lib.HomologicalAlgebra.UnitTransgression.LowDegreeFiltration
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h2F2_eq_top
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h3F2_eq_top
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h1_subsingleton
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h2EquivZMod
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h3EquivZMod
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h2_subsingleton_of_isUnit
#print axioms Lib.HomologicalAlgebra.UnitTransgression.h3_subsingleton_of_isUnit
#print axioms Lib.HomologicalAlgebra.UnitTransgression.all_subsingleton_of_isUnit
