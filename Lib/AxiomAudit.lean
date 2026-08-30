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
#print axioms Matrix.quotientRangeToLin'EquivZModOfIsCoprime
#print axioms Matrix.quotientRangeToLinEquivZModOfIsCoprime

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
#print axioms GroupExtension.Splitting.abelianizationMulEquiv

#print axioms Subgroup.isMulCommutative_of_closure_eq_top
#print axioms AddSubgroup.isAddCommutative_of_closure_eq_top
#print axioms AddSubgroup.eq_of_le_of_quotient_subsingleton
#print axioms AddSubgroup.eq_top_of_le_of_quotient_subsingleton

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
