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

#print axioms LinearMap.dualMap_sub
#print axioms LinearMap.dualAnnihilator_range_sub_eq_ker_sub_dualMap
#print axioms LinearMap.dualAnnihilator_range_sub_id_eq_fixedSubmodule
#print axioms LinearMap.range_dualMap_eq_fixedSubmodule_of_surjective_of_ker_eq_range_sub_id
#print axioms LinearMap.dualEquivFixedSubmoduleOfSurjectiveOfKerEqRangeSubId
#print axioms LinearMap.dualEquivFixedSubmoduleOfSurjectiveOfKerEqRangeSubId_apply_coe
#print axioms LinearMap.injective_of_duality_naturality_of_surjective
#print axioms LinearMap.map_range_eq_fixedSubmodule_of_duality_naturality

#print axioms exteriorPower.finBasis
#print axioms exteriorPower.finBasis_map_coefficient
#print axioms exteriorPower.finMatrix
#print axioms exteriorPower.toMatrix_map
#print axioms exteriorPower.finCoordinates
#print axioms exteriorPower.finCoordinates_apply
#print axioms exteriorPower.finCoordinates_map

#print axioms exteriorPower.reindexedFinBasis
#print axioms exteriorPower.reindexedFinBasis_apply
#print axioms exteriorPower.reindexedFinCoordinates
#print axioms exteriorPower.reindexedFinCoordinates_apply
#print axioms exteriorPower.reindexedFinCoordinates_basis
#print axioms exteriorPower.reindexedFinMatrix
#print axioms exteriorPower.reindexedFinBasis_map_coefficient
#print axioms exteriorPower.toMatrix_map_reindexed
#print axioms exteriorPower.reindexedFinCoordinates_map

#print axioms exteriorPower.wedge
#print axioms exteriorPower.coe_wedge
#print axioms exteriorPower.finCoordinates_finBasis
#print axioms exteriorPower.finBasis_wedge_of_not_disjoint
#print axioms exteriorPower.finCoordinates_wedge_of_not_disjoint
#print axioms exteriorPower.finBasis_wedge_of_disjoint
#print axioms exteriorPower.finCoordinates_wedge_of_disjoint

#print axioms Set.powersetCard.orderIsoOfFin_permOfDisjoint_castAdd
#print axioms Set.powersetCard.orderIsoOfFin_permOfDisjoint_natAdd
#print axioms Set.powersetCard.permOfDisjoint_eq
#print axioms Set.powersetCard.permOfDisjoint_eq_of_orderEmbOfFin

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

-- Lane A (singular homology core)
#print axioms SingularMayerVietoris.exact_at_ambient
#print axioms SphereHomology.unitSphere_homology_subsingleton
#print axioms LinearSphereAction.homology_eq_sign_smul

-- Lane D1 (Morse theory I)
#print axioms ManifoldMorse.exists_morse_function
#print axioms SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn
#print axioms ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits
#print axioms ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points

-- Lane H (complex analysis)
#print axioms RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero
#print axioms HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution
#print axioms AnalyticRootCover.exists_analytic_square_root
#print axioms AnalyticRootCover.exists_analytic_square_root_ball

-- Lane D2 (Whitney embedding, projection bundle, collar, cells)
#print axioms exists_tubularNeighborhood_in_open_of_embedded_closedBall

-- Lane I (quotients, mapping torus, split extensions)
#print axioms SplitGroupExtension.mulEquiv
#print axioms MappingTorusHomology.monodromyHomologyMap

-- Lane C (Hurewicz theorem, higher degrees and sphere connectivity)
#print axioms Hurewicz.hurewiczLinearEquiv
#print axioms Hurewicz.hurewiczLinearEquivOfTwoLE
#print axioms Hurewicz.pi_subsingleton_of_homology_vanishing
#print axioms Hurewicz.sphere_pi_subsingleton_of_lt
#print axioms Hurewicz.sphere_homotopicRel_of_topClass_eq
#print axioms Hurewicz.sphere_homotopic_id_of_topClass
#print axioms Hurewicz.right_inverse_is_left_inverse
#print axioms Hurewicz.exists_basepoint_adjustment
#print axioms Hurewicz.hurewiczLinearEquivOfTwoLE_natural
#print axioms Hurewicz.subsingleton_singularHomology_of_lt
#print axioms DiskCube.homeomorph
#print axioms DiskCube.boundary_iff

#print axioms MorseCancellation.cancel_of_transverse_level_isotopy
#print axioms MorseRearrangement.exists_morse_rearrangement_of_no_connection
#print axioms MorseCancellation.exists_excellent_indexed_morse_birth
#print axioms simplyConnectedSpace_of_open_cover
#print axioms MorseCells.built_of_compact_smooth_manifold
#print axioms AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros

#check CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor
#print axioms CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor
#check CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_H
#print axioms CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_H
#check CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_δ'_app
#print axioms CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_δ'_app

#check LinearMap.RankOneNormalization
#print axioms LinearMap.RankOneNormalization
#check LinearMap.RankOneNormalization.mk
#print axioms LinearMap.RankOneNormalization.mk
#check LinearMap.RankOneNormalization.source
#print axioms LinearMap.RankOneNormalization.source
#check LinearMap.RankOneNormalization.target
#print axioms LinearMap.RankOneNormalization.target
#check LinearMap.RankOneNormalization.normalized
#print axioms LinearMap.RankOneNormalization.normalized
#check LinearMap.RankOneNormalization.coefficient
#print axioms LinearMap.RankOneNormalization.coefficient
#check LinearMap.RankOneNormalization.normalized_eq_lsmul
#print axioms LinearMap.RankOneNormalization.normalized_eq_lsmul
#check LinearMap.RankOneNormalization.map_eq_zero_iff
#print axioms LinearMap.RankOneNormalization.map_eq_zero_iff
#check LinearMap.RankOneNormalization.map_ne_zero_iff
#print axioms LinearMap.RankOneNormalization.map_ne_zero_iff
#check LinearMap.RankOneNormalization.injective_iff_coefficient_ne_zero
#print axioms LinearMap.RankOneNormalization.injective_iff_coefficient_ne_zero
#check LinearMap.RankOneNormalization.injective_iff_ne_zero
#print axioms LinearMap.RankOneNormalization.injective_iff_ne_zero
#check LinearMap.RankOneNormalization.kernelEquivNormalized
#print axioms LinearMap.RankOneNormalization.kernelEquivNormalized
#check LinearMap.RankOneNormalization.kernelEquiv
#print axioms LinearMap.RankOneNormalization.kernelEquiv
#check LinearMap.RankOneNormalization.cokernelEquivNormalized
#print axioms LinearMap.RankOneNormalization.cokernelEquivNormalized
#check LinearMap.RankOneNormalization.cokernelEquiv
#print axioms LinearMap.RankOneNormalization.cokernelEquiv
#check LinearMap.RankOneNormalization.bijective_iff_isUnit
#print axioms LinearMap.RankOneNormalization.bijective_iff_isUnit

#check ThreeColumnPage.Data
#print axioms ThreeColumnPage.Data
#check ThreeColumnPage.Data.mk
#print axioms ThreeColumnPage.Data.mk
#check ThreeColumnPage.Data.E
#print axioms ThreeColumnPage.Data.E
#check ThreeColumnPage.Data.addCommGroup
#print axioms ThreeColumnPage.Data.addCommGroup
#check ThreeColumnPage.Data.module
#print axioms ThreeColumnPage.Data.module
#check ThreeColumnPage.Data.differential
#print axioms ThreeColumnPage.Data.differential
#check ThreeColumnPage.Data.source
#print axioms ThreeColumnPage.Data.source
#check ThreeColumnPage.Data.target
#print axioms ThreeColumnPage.Data.target
#check ThreeColumnPage.Data.middle
#print axioms ThreeColumnPage.Data.middle
#check ThreeColumnPage.Data.ofCoefficients
#print axioms ThreeColumnPage.Data.ofCoefficients
#check ThreeColumnPage.Data.normalization
#print axioms ThreeColumnPage.Data.normalization
#check ThreeColumnPage.Data.coefficient
#print axioms ThreeColumnPage.Data.coefficient
#check ThreeColumnPage.Data.ofCoefficients_coefficient
#print axioms ThreeColumnPage.Data.ofCoefficients_coefficient
#check ThreeColumnPage.Data.Kernel
#print axioms ThreeColumnPage.Data.Kernel
#check ThreeColumnPage.Data.Cokernel
#print axioms ThreeColumnPage.Data.Cokernel
#check ThreeColumnPage.Data.kernelEquiv
#print axioms ThreeColumnPage.Data.kernelEquiv
#check ThreeColumnPage.Data.cokernelEquiv
#print axioms ThreeColumnPage.Data.cokernelEquiv
#check ThreeColumnPage.Data.differential_bijective_iff_isUnit
#print axioms ThreeColumnPage.Data.differential_bijective_iff_isUnit
#check ThreeColumnPage.Data.differential_injective_iff_ne_zero
#print axioms ThreeColumnPage.Data.differential_injective_iff_ne_zero

#check ThreeColumnPage.FilteredAbutment
#print axioms ThreeColumnPage.FilteredAbutment
#check ThreeColumnPage.FilteredAbutment.mk
#print axioms ThreeColumnPage.FilteredAbutment.mk
#check ThreeColumnPage.FilteredAbutment.H
#print axioms ThreeColumnPage.FilteredAbutment.H
#check ThreeColumnPage.FilteredAbutment.addCommGroup
#print axioms ThreeColumnPage.FilteredAbutment.addCommGroup
#check ThreeColumnPage.FilteredAbutment.degreeOne
#print axioms ThreeColumnPage.FilteredAbutment.degreeOne
#check ThreeColumnPage.FilteredAbutment.bottom
#print axioms ThreeColumnPage.FilteredAbutment.bottom
#check ThreeColumnPage.FilteredAbutment.middle
#print axioms ThreeColumnPage.FilteredAbutment.middle
#check ThreeColumnPage.FilteredAbutment.bottom_le_middle
#print axioms ThreeColumnPage.FilteredAbutment.bottom_le_middle
#check ThreeColumnPage.FilteredAbutment.bottomGraded
#print axioms ThreeColumnPage.FilteredAbutment.bottomGraded
#check ThreeColumnPage.FilteredAbutment.middleGraded
#print axioms ThreeColumnPage.FilteredAbutment.middleGraded
#check ThreeColumnPage.FilteredAbutment.topGraded
#print axioms ThreeColumnPage.FilteredAbutment.topGraded
#check ThreeColumnPage.FilteredAbutment.all_subsingleton_iff
#print axioms ThreeColumnPage.FilteredAbutment.all_subsingleton_iff
#check ThreeColumnPage.FilteredAbutment.all_subsingleton_iff_isUnit_of_coefficients_eq
#print axioms ThreeColumnPage.FilteredAbutment.all_subsingleton_iff_isUnit_of_coefficients_eq
#check Monoid.PushoutI.equivOfCocone
#print axioms Monoid.PushoutI.equivOfCocone
#check Monoid.PushoutI.equivOfCocone_apply_of
#print axioms Monoid.PushoutI.equivOfCocone_apply_of
#check Monoid.PushoutI.equivOfCocone_symm_apply_f
#print axioms Monoid.PushoutI.equivOfCocone_symm_apply_f


#check Path.trans_mem
#print axioms Path.trans_mem
#check FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc
#print axioms FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc
#check FundamentalGroup.VanKampen.LocalPathValue
#print axioms FundamentalGroup.VanKampen.LocalPathValue
#check FundamentalGroup.VanKampen.LocalPathValue.mk
#print axioms FundamentalGroup.VanKampen.LocalPathValue.mk
#check FundamentalGroup.VanKampen.LocalPathValue.value
#print axioms FundamentalGroup.VanKampen.LocalPathValue.value
#check FundamentalGroup.VanKampen.LocalPathValue.refl
#print axioms FundamentalGroup.VanKampen.LocalPathValue.refl
#check FundamentalGroup.VanKampen.LocalPathValue.trans
#print axioms FundamentalGroup.VanKampen.LocalPathValue.trans
#check FundamentalGroup.VanKampen.LocalPathValue.subpath_mul
#print axioms FundamentalGroup.VanKampen.LocalPathValue.subpath_mul
#check FundamentalGroup.VanKampen.LocalPathValue.compatible
#print axioms FundamentalGroup.VanKampen.LocalPathValue.compatible
#check FundamentalGroup.VanKampen.LocalPathValue.value_cast
#print axioms FundamentalGroup.VanKampen.LocalPathValue.value_cast
#check FundamentalGroup.VanKampen.LocalPathValue.HomotopyInvariant
#print axioms FundamentalGroup.VanKampen.LocalPathValue.HomotopyInvariant
#check FundamentalGroup.VanKampen.PathValue
#print axioms FundamentalGroup.VanKampen.PathValue
#check FundamentalGroup.VanKampen.PathValue.mk
#print axioms FundamentalGroup.VanKampen.PathValue.mk
#check FundamentalGroup.VanKampen.PathValue.value
#print axioms FundamentalGroup.VanKampen.PathValue.value
#check FundamentalGroup.VanKampen.PathValue.refl
#print axioms FundamentalGroup.VanKampen.PathValue.refl
#check FundamentalGroup.VanKampen.PathValue.trans
#print axioms FundamentalGroup.VanKampen.PathValue.trans
#check FundamentalGroup.VanKampen.PathValue.subpath_mul
#print axioms FundamentalGroup.VanKampen.PathValue.subpath_mul
#check FundamentalGroup.VanKampen.PathValue.value_cast
#print axioms FundamentalGroup.VanKampen.PathValue.value_cast
#check FundamentalGroup.VanKampen.PathValue.value_subpath_zero_one
#print axioms FundamentalGroup.VanKampen.PathValue.value_subpath_zero_one
#check FundamentalGroup.VanKampen.PathValue.Extends
#print axioms FundamentalGroup.VanKampen.PathValue.Extends
#check FundamentalGroup.VanKampen.PathValue.HomotopyInvariant
#print axioms FundamentalGroup.VanKampen.PathValue.HomotopyInvariant
#check FundamentalGroup.VanKampen.TwoOpenCover
#print axioms FundamentalGroup.VanKampen.TwoOpenCover
#check FundamentalGroup.VanKampen.TwoOpenCover.mk
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.mk
#check FundamentalGroup.VanKampen.TwoOpenCover.U
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.U
#check FundamentalGroup.VanKampen.TwoOpenCover.V
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.V
#check FundamentalGroup.VanKampen.TwoOpenCover.cover
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.cover
#check FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedU
#check FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedV
#check FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedIntersection
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedIntersection
#check FundamentalGroup.VanKampen.TwoOpenCover.base
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.base
#check FundamentalGroup.VanKampen.TwoOpenCover.baseU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseU
#check FundamentalGroup.VanKampen.TwoOpenCover.baseV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseV
#check FundamentalGroup.VanKampen.TwoOpenCover.chart
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chart
#check FundamentalGroup.VanKampen.TwoOpenCover.base_mem_chart
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.base_mem_chart
#check FundamentalGroup.VanKampen.TwoOpenCover.chart_open
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chart_open
#check FundamentalGroup.VanKampen.TwoOpenCover.chart_cover
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chart_cover
#check FundamentalGroup.VanKampen.TwoOpenCover.mem_U_or_V
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.mem_U_or_V
#check FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo
#check FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo_mem
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo_mem
#check FundamentalGroup.VanKampen.TwoOpenCover.pathTo
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathTo
#check FundamentalGroup.VanKampen.TwoOpenCover.pathTo_base
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathTo_base
#check FundamentalGroup.VanKampen.TwoOpenCover.pathTo_mem
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathTo_mem
#check FundamentalGroup.VanKampen.TwoOpenCover.overlap
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlap
#check FundamentalGroup.VanKampen.TwoOpenCover.baseUPoint
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseUPoint
#check FundamentalGroup.VanKampen.TwoOpenCover.baseVPoint
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseVPoint
#check FundamentalGroup.VanKampen.TwoOpenCover.baseOverlapPoint
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseOverlapPoint
#check FundamentalGroup.VanKampen.TwoOpenCover.baseChart
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.baseChart
#check FundamentalGroup.VanKampen.TwoOpenCover.UGroup
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.UGroup
#check FundamentalGroup.VanKampen.TwoOpenCover.VGroup
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.VGroup
#check FundamentalGroup.VanKampen.TwoOpenCover.OverlapGroup
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.OverlapGroup
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapToU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapToU
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapToV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapToV
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionU
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionV
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_compatible
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_compatible
#check FundamentalGroup.VanKampen.TwoOpenCover.Compatible
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.Compatible
#check FundamentalGroup.VanKampen.pathIn
#print axioms FundamentalGroup.VanKampen.pathIn
#check FundamentalGroup.VanKampen.pathIn_apply
#print axioms FundamentalGroup.VanKampen.pathIn_apply
#check FundamentalGroup.VanKampen.pathIn_map
#print axioms FundamentalGroup.VanKampen.pathIn_map
#check FundamentalGroup.VanKampen.pathIn_refl
#print axioms FundamentalGroup.VanKampen.pathIn_refl
#check FundamentalGroup.VanKampen.pathIn_trans
#print axioms FundamentalGroup.VanKampen.pathIn_trans
#check FundamentalGroup.VanKampen.homotopyIn
#print axioms FundamentalGroup.VanKampen.homotopyIn
#check FundamentalGroup.VanKampen.homotopy_trans_mem
#print axioms FundamentalGroup.VanKampen.homotopy_trans_mem
#check FundamentalGroup.VanKampen.homotopy_transRefl_mem
#print axioms FundamentalGroup.VanKampen.homotopy_transRefl_mem
#check FundamentalGroup.VanKampen.homotopy_subpathTransSubpathRefl_mem
#print axioms FundamentalGroup.VanKampen.homotopy_subpathTransSubpathRefl_mem
#check FundamentalGroup.VanKampen.homotopy_subpathTransSubpath_mem
#print axioms FundamentalGroup.VanKampen.homotopy_subpathTransSubpath_mem
#check FundamentalGroup.VanKampen.mem_Icc_of_subpath_mem
#print axioms FundamentalGroup.VanKampen.mem_Icc_of_subpath_mem
#check FundamentalGroup.VanKampen.subpathTransSubpathIn
#print axioms FundamentalGroup.VanKampen.subpathTransSubpathIn
#check FundamentalGroup.VanKampen.PathClass.pathClass_property_cast
#print axioms FundamentalGroup.VanKampen.PathClass.pathClass_property_cast
#check FundamentalGroup.VanKampen.PathClass.pathClass_induction_of_open_cover
#print axioms FundamentalGroup.VanKampen.PathClass.pathClass_induction_of_open_cover
#check FundamentalGroup.VanKampen.PathClass.quotient_symm_trans_cancel
#print axioms FundamentalGroup.VanKampen.PathClass.quotient_symm_trans_cancel
#check FundamentalGroup.VanKampen.PathClass.quotient_trans_right_cancel
#print axioms FundamentalGroup.VanKampen.PathClass.quotient_trans_right_cancel
#check FundamentalGroup.VanKampen.PathClass.basedLoop
#print axioms FundamentalGroup.VanKampen.PathClass.basedLoop
#check FundamentalGroup.VanKampen.PathClass.pathDifference
#print axioms FundamentalGroup.VanKampen.PathClass.pathDifference
#check FundamentalGroup.VanKampen.PathClass.basedLoop_refl
#print axioms FundamentalGroup.VanKampen.PathClass.basedLoop_refl
#check FundamentalGroup.VanKampen.PathClass.basedLoop_trans
#print axioms FundamentalGroup.VanKampen.PathClass.basedLoop_trans
#check FundamentalGroup.VanKampen.PathClass.basedLoop_comparison
#print axioms FundamentalGroup.VanKampen.PathClass.basedLoop_comparison
#check FundamentalGroup.VanKampen.TwoOpenCover.hom_ext
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.hom_ext
#check FundamentalGroup.VanKampen.TwoOpenCover.chartPath
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chartPath
#check FundamentalGroup.VanKampen.TwoOpenCover.chartPath_base
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chartPath_base
#check FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass
#check FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass_base
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass_base
#check FundamentalGroup.VanKampen.TwoOpenCover.closePath
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.closePath
#check FundamentalGroup.VanKampen.TwoOpenCover.closePath_refl
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.closePath_refl
#check FundamentalGroup.VanKampen.TwoOpenCover.closePath_trans
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.closePath_trans
#check FundamentalGroup.VanKampen.TwoOpenCover.closePath_homotopic
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.closePath_homotopic
#check FundamentalGroup.VanKampen.TwoOpenCover.closePath_loop
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.closePath_loop
#check FundamentalGroup.VanKampen.TwoOpenCover.chartHom
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.chartHom
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_refl
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_refl
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_trans
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_trans
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_subpath_mul
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_subpath_mul
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_homotopy
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_homotopy
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapPath
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapPath
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_U
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_U
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_V
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_V
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapClose
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapClose
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU_close
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU_close
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV_close
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV_close
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible_UV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible_UV
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible
#check FundamentalGroup.VanKampen.TwoOpenCover.localPathValue
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localPathValue
#check FundamentalGroup.VanKampen.TwoOpenCover.localPathValue_homotopyInvariant
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localPathValue_homotopyInvariant
#check FundamentalGroup.VanKampen.TwoOpenCover.localValue_map_loop
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.localValue_map_loop
#check FundamentalGroup.VanKampen.PathValue.fundamentalGroupHom
#print axioms FundamentalGroup.VanKampen.PathValue.fundamentalGroupHom
#check FundamentalGroup.VanKampen.PathValue.fundamentalGroupHom_mk
#print axioms FundamentalGroup.VanKampen.PathValue.fundamentalGroupHom_mk
#check FundamentalGroup.VanKampen.mem_of_subpath_mem
#print axioms FundamentalGroup.VanKampen.mem_of_subpath_mem
#check FundamentalGroup.VanKampen.subpath_mem_mono
#print axioms FundamentalGroup.VanKampen.subpath_mem_mono
#check FundamentalGroup.VanKampen.exists_path_subdivision
#print axioms FundamentalGroup.VanKampen.exists_path_subdivision
#check FundamentalGroup.VanKampen.LocalPathValue.IsPrimitive
#print axioms FundamentalGroup.VanKampen.LocalPathValue.IsPrimitive
#check FundamentalGroup.VanKampen.LocalPathValue.IsPrimitiveUpTo
#print axioms FundamentalGroup.VanKampen.LocalPathValue.IsPrimitiveUpTo
#check FundamentalGroup.VanKampen.LocalPathValue.isPrimitiveUpTo_zero
#print axioms FundamentalGroup.VanKampen.LocalPathValue.isPrimitiveUpTo_zero
#check FundamentalGroup.VanKampen.LocalPathValue.exists_primitiveUpTo_step
#print axioms FundamentalGroup.VanKampen.LocalPathValue.exists_primitiveUpTo_step
#check FundamentalGroup.VanKampen.LocalPathValue.exists_primitive
#print axioms FundamentalGroup.VanKampen.LocalPathValue.exists_primitive
#check FundamentalGroup.VanKampen.LocalPathValue.primitive_unique
#print axioms FundamentalGroup.VanKampen.LocalPathValue.primitive_unique
#check FundamentalGroup.VanKampen.convexComb_monotone
#print axioms FundamentalGroup.VanKampen.convexComb_monotone
#check FundamentalGroup.VanKampen.convexComb_comp
#print axioms FundamentalGroup.VanKampen.convexComb_comp
#check FundamentalGroup.VanKampen.subpath_subpath
#print axioms FundamentalGroup.VanKampen.subpath_subpath
#check FundamentalGroup.VanKampen.intervalHalf
#print axioms FundamentalGroup.VanKampen.intervalHalf
#check FundamentalGroup.VanKampen.trans_convexComb_first_half
#print axioms FundamentalGroup.VanKampen.trans_convexComb_first_half
#check FundamentalGroup.VanKampen.trans_convexComb_second_half
#print axioms FundamentalGroup.VanKampen.trans_convexComb_second_half
#check FundamentalGroup.VanKampen.trans_apply_intervalHalf
#print axioms FundamentalGroup.VanKampen.trans_apply_intervalHalf
#check FundamentalGroup.VanKampen.trans_subpath_first_half
#print axioms FundamentalGroup.VanKampen.trans_subpath_first_half
#check FundamentalGroup.VanKampen.trans_subpath_second_half
#print axioms FundamentalGroup.VanKampen.trans_subpath_second_half
#check FundamentalGroup.VanKampen.LocalPathValue.value_eq_of_path_eq
#print axioms FundamentalGroup.VanKampen.LocalPathValue.value_eq_of_path_eq
#check FundamentalGroup.VanKampen.LocalPathValue.isPrimitive_subpath
#print axioms FundamentalGroup.VanKampen.LocalPathValue.isPrimitive_subpath
#check FundamentalGroup.VanKampen.LocalPathValue.transport
#print axioms FundamentalGroup.VanKampen.LocalPathValue.transport
#check FundamentalGroup.VanKampen.LocalPathValue.transport_zero
#print axioms FundamentalGroup.VanKampen.LocalPathValue.transport_zero
#check FundamentalGroup.VanKampen.LocalPathValue.transport_isPrimitive
#print axioms FundamentalGroup.VanKampen.LocalPathValue.transport_isPrimitive
#check FundamentalGroup.VanKampen.LocalPathValue.transport_subpath
#print axioms FundamentalGroup.VanKampen.LocalPathValue.transport_subpath
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_cast
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_cast
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_zero_one
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_zero_one
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_local
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_local
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_refl
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_refl
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_mul
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_mul
#check FundamentalGroup.VanKampen.LocalPathValue.rawValue_trans
#print axioms FundamentalGroup.VanKampen.LocalPathValue.rawValue_trans
#check FundamentalGroup.VanKampen.LocalPathValue.extension
#print axioms FundamentalGroup.VanKampen.LocalPathValue.extension
#check FundamentalGroup.VanKampen.LocalPathValue.extension_extends
#print axioms FundamentalGroup.VanKampen.LocalPathValue.extension_extends
#check FundamentalGroup.VanKampen.squareHorizontal
#print axioms FundamentalGroup.VanKampen.squareHorizontal
#check FundamentalGroup.VanKampen.squareVertical
#print axioms FundamentalGroup.VanKampen.squareVertical
#check FundamentalGroup.VanKampen.squarePathHomotopy
#print axioms FundamentalGroup.VanKampen.squarePathHomotopy
#check FundamentalGroup.VanKampen.convexComb_mem_Icc
#print axioms FundamentalGroup.VanKampen.convexComb_mem_Icc
#check FundamentalGroup.VanKampen.squarePathHomotopy_mem_rectangle
#print axioms FundamentalGroup.VanKampen.squarePathHomotopy_mem_rectangle
#check FundamentalGroup.VanKampen.rectangleHorizontalVertical
#print axioms FundamentalGroup.VanKampen.rectangleHorizontalVertical
#check FundamentalGroup.VanKampen.rectangleVerticalHorizontal
#print axioms FundamentalGroup.VanKampen.rectangleVerticalHorizontal
#check FundamentalGroup.VanKampen.rectangleHorizontalVertical_map
#print axioms FundamentalGroup.VanKampen.rectangleHorizontalVertical_map
#check FundamentalGroup.VanKampen.rectangleVerticalHorizontal_map
#print axioms FundamentalGroup.VanKampen.rectangleVerticalHorizontal_map
#check FundamentalGroup.VanKampen.rectangleHorizontalVertical_mem
#print axioms FundamentalGroup.VanKampen.rectangleHorizontalVertical_mem
#check FundamentalGroup.VanKampen.rectangleVerticalHorizontal_mem
#print axioms FundamentalGroup.VanKampen.rectangleVerticalHorizontal_mem
#check FundamentalGroup.VanKampen.rectangleBoundaryHomotopy
#print axioms FundamentalGroup.VanKampen.rectangleBoundaryHomotopy
#check FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_apply
#print axioms FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_apply
#check FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_mem
#print axioms FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_mem
#check FundamentalGroup.VanKampen.PathValue.square_cell_of_local
#print axioms FundamentalGroup.VanKampen.PathValue.square_cell_of_local
#check FundamentalGroup.VanKampen.PathValue.value_eq_one_of_constant
#print axioms FundamentalGroup.VanKampen.PathValue.value_eq_one_of_constant
#check FundamentalGroup.VanKampen.PathValue.square_strip
#print axioms FundamentalGroup.VanKampen.PathValue.square_strip
#check FundamentalGroup.VanKampen.PathValue.value_squareHorizontal_homotopy
#print axioms FundamentalGroup.VanKampen.PathValue.value_squareHorizontal_homotopy
#check FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_zero
#print axioms FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_zero
#check FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_one
#print axioms FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_one
#check FundamentalGroup.VanKampen.PathValue.value_eq_of_homotopy_of_open_cover
#print axioms FundamentalGroup.VanKampen.PathValue.value_eq_of_homotopy_of_open_cover
#check FundamentalGroup.VanKampen.PathValue.homotopyInvariant_of_open_cover
#print axioms FundamentalGroup.VanKampen.PathValue.homotopyInvariant_of_open_cover
#check FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue
#check FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_extends
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_extends
#check FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_homotopyInvariant
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_homotopyInvariant
#check FundamentalGroup.VanKampen.TwoOpenCover.lift
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.lift
#check FundamentalGroup.VanKampen.TwoOpenCover.lift_mk_of_mem
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.lift_mk_of_mem
#check FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionU
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionU
#check FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionV
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionV
#check FundamentalGroup.VanKampen.TwoOpenCover.ChartGroup
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.ChartGroup
#check FundamentalGroup.VanKampen.TwoOpenCover.overlapHom
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.overlapHom
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_comp_overlapHom
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_comp_overlapHom
#check FundamentalGroup.VanKampen.TwoOpenCover.Pushout
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.Pushout
#check FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv
#check FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_of
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_of
#check FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_symm_inclusionHom
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_symm_inclusionHom

-- Basic: every public source declaration in source order.
#check Mathoverflow1973.MappingTorus.Circle
#print axioms Mathoverflow1973.MappingTorus.Circle
#check Mathoverflow1973.MappingTorus.deck
#print axioms Mathoverflow1973.MappingTorus.deck
#check Mathoverflow1973.MappingTorus.deck_zero
#print axioms Mathoverflow1973.MappingTorus.deck_zero
#check Mathoverflow1973.MappingTorus.deck_add
#print axioms Mathoverflow1973.MappingTorus.deck_add
#check Mathoverflow1973.MappingTorus.deck_continuous
#print axioms Mathoverflow1973.MappingTorus.deck_continuous
#check Mathoverflow1973.MappingTorus.deckHomeomorph
#print axioms Mathoverflow1973.MappingTorus.deckHomeomorph
#check Mathoverflow1973.MappingTorus.orbitSetoid
#print axioms Mathoverflow1973.MappingTorus.orbitSetoid
#check Mathoverflow1973.MappingTorus.Torus
#print axioms Mathoverflow1973.MappingTorus.Torus
#check Mathoverflow1973.MappingTorus.instLocal1
#print axioms Mathoverflow1973.MappingTorus.instLocal1
#check Mathoverflow1973.MappingTorus.mk
#print axioms Mathoverflow1973.MappingTorus.mk
#check Mathoverflow1973.MappingTorus.mk_continuous
#print axioms Mathoverflow1973.MappingTorus.mk_continuous
#check Mathoverflow1973.MappingTorus.mk_surjective
#print axioms Mathoverflow1973.MappingTorus.mk_surjective
#check Mathoverflow1973.MappingTorus.mk_eq_mk_iff
#print axioms Mathoverflow1973.MappingTorus.mk_eq_mk_iff
#check Mathoverflow1973.MappingTorus.mk_deck
#print axioms Mathoverflow1973.MappingTorus.mk_deck
#check Mathoverflow1973.MappingTorus.mk_sub_one
#print axioms Mathoverflow1973.MappingTorus.mk_sub_one
#check Mathoverflow1973.MappingTorus.mk_add_one
#print axioms Mathoverflow1973.MappingTorus.mk_add_one
#check Mathoverflow1973.MappingTorus.mk_preimage_image
#print axioms Mathoverflow1973.MappingTorus.mk_preimage_image
#check Mathoverflow1973.MappingTorus.mk_open
#print axioms Mathoverflow1973.MappingTorus.mk_open
#check Mathoverflow1973.MappingTorus.circle_intCast
#print axioms Mathoverflow1973.MappingTorus.circle_intCast
#check Mathoverflow1973.MappingTorus.circle_coe_eq_iff
#print axioms Mathoverflow1973.MappingTorus.circle_coe_eq_iff
#check Mathoverflow1973.MappingTorus.base
#print axioms Mathoverflow1973.MappingTorus.base
#check Mathoverflow1973.MappingTorus.base_mk
#print axioms Mathoverflow1973.MappingTorus.base_mk

-- TranslationCocycle: every public source declaration in source order.
#check Mathoverflow1973.MappingTorus.TranslationCocycle
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle
#check Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder
#check Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder_continuous
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder_continuous
#check Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder_deck
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.cylinder_deck
#check Mathoverflow1973.MappingTorus.TranslationCocycle.map
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.map
#check Mathoverflow1973.MappingTorus.TranslationCocycle.map_mk
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.map_mk
#check Mathoverflow1973.MappingTorus.TranslationCocycle.map_add_apply
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.map_add_apply
#check Mathoverflow1973.MappingTorus.TranslationCocycle.map_zero_apply
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.map_zero_apply
#check Mathoverflow1973.MappingTorus.TranslationCocycle.shear
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.shear
#check Mathoverflow1973.MappingTorus.TranslationCocycle.base_shear
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.base_shear
#check Mathoverflow1973.MappingTorus.TranslationCocycle.shear_add_apply
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.shear_add_apply
#check Mathoverflow1973.MappingTorus.TranslationCocycle.zsmul_shift_eq_zero_of_shear_eq
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.zsmul_shift_eq_zero_of_shear_eq
#check Mathoverflow1973.MappingTorus.TranslationCocycle.shear_zero
#print axioms Mathoverflow1973.MappingTorus.TranslationCocycle.shear_zero

-- SquareZeroWinding: every public source declaration in source order.
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_continuous
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_continuous
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_continuous
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_continuous
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_mem_lattice
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_mem_lattice
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_mem_lattice
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_symm_mem_lattice
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_map_lattice
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_map_lattice
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.Torus
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.Torus
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusLinearEquiv
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusLinearEquiv
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_mkQ
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_mkQ
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_zero_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_zero_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_zero_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_zero_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_add_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.linearEquiv_add_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_add_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.torusContinuousAddEquiv_add_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.monodromy
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.monodromy
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.monodromy_zpow
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.monodromy_zpow
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_continuous
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_continuous
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_zero
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_zero
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_one
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_one
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_add_int_sub_linearEquiv_neg
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_add_int_sub_linearEquiv_neg
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_defect_mem_lattice
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingLift_defect_mem_lattice
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift_continuous
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift_continuous
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift_add_int
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.windingShift_add_int
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.translationCocycle
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.translationCocycle
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear_zero
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear_zero
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear_add_apply
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Data.shear_add_apply
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.functional_windingLift
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.functional_windingLift
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.windingShift_detector_ne_zero
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.windingShift_detector_ne_zero
#check Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.shear_injective
#print axioms Mathoverflow1973.MappingTorus.SquareZeroWinding.Detector.shear_injective
