import Lib

/-!
# Per-export axiom audit for the reusable library

Compile this file directly. It deliberately is not imported by `Lib.lean`, because `#print axioms`
is an evidence command rather than library content.
-/

#print axioms Module.End.cyclicAverage
#print axioms Module.End.mul_sum_powers_eq_sum_powers
#print axioms Module.End.sum_powers_mul_eq_sum_powers
#print axioms Module.End.mul_cyclicAverage
#print axioms Module.End.cyclicAverage_mul
#print axioms Module.End.cyclicAverage_apply_of_fixed
#print axioms Module.End.isProj_cyclicAverage
#print axioms Module.End.isIdempotentElem_cyclicAverage
#print axioms Module.End.range_cyclicAverage
#print axioms Module.End.comp_cyclicAverage

#print axioms Matrix.natAbs_det_eq_natCard_quotient_range_toLin'

#print axioms Module.End.oneAddSMul
#print axioms Module.End.oneAddSMul_zero
#print axioms Module.End.oneAddSMul_apply
#print axioms Module.End.oneAddSMul_mul_oneAddSMul
#print axioms Module.End.oneAddSMulEquiv
#print axioms Module.End.oneAddSMulEquiv_toLinearMap
#print axioms Module.End.oneAddSMulEquiv_apply
#print axioms Module.End.oneAddSMulEquiv_symm_toLinearMap
#print axioms Module.End.quadratic_term_eq_zero
#print axioms Module.End.oneAddSMul_preserves_bilin
#print axioms Module.End.oneAddSMul_preserves_bilin_of_isSkewAdjoint

#print axioms Abelianization.mapMulAut
#print axioms SemidirectProduct.abelianizationRepresentation
#print axioms SemidirectProduct.AbelianizationCoinvariants
#print axioms SemidirectProduct.coinvariantsMk
#print axioms SemidirectProduct.coinvariantsMk_action
#print axioms SemidirectProduct.abelianizationMulEquiv
#print axioms SemidirectProduct.abelianizationMulEquiv_apply_of_inl
#print axioms SemidirectProduct.abelianizationMulEquiv_apply_of_inr
#print axioms SemidirectProduct.abelianizationMulEquiv_symm_apply_inl
#print axioms SemidirectProduct.abelianizationMulEquiv_symm_apply_inr

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
