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

#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
#check FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV_surjective_of_overlapHomU_surjective
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV_surjective_of_overlapHomU_surjective
#check FundamentalGroup.basepointChange_naturality
#print axioms FundamentalGroup.basepointChange_naturality
#check FundamentalGroup.basepointChange_naturality_apply
#print axioms FundamentalGroup.basepointChange_naturality_apply
#check FundamentalGroup.map_surjective_at_of_path
#print axioms FundamentalGroup.map_surjective_at_of_path
#check FundamentalGroup.map_surjective_at_of_pathConnected
#print axioms FundamentalGroup.map_surjective_at_of_pathConnected
#check FundamentalGroup.eq_one_of_path
#print axioms FundamentalGroup.eq_one_of_path
#check FundamentalGroup.simplyConnectedSpace_iff_eq_one
#print axioms FundamentalGroup.simplyConnectedSpace_iff_eq_one
#check FundamentalGroup.simplyConnectedSpace_of_eq_one
#print axioms FundamentalGroup.simplyConnectedSpace_of_eq_one
#check FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedSpace
#print axioms FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedSpace

/-! ## `Lib.Topology.Covering.QuotientConnectedness` -/

#check IsQuotientCoveringMap.pathConnectedSpace_of_fundamentalGroupToMulOpposite_surjective
#print axioms IsQuotientCoveringMap.pathConnectedSpace_of_fundamentalGroupToMulOpposite_surjective

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

-- Manifold scalar restriction and smooth descent: every public declaration in source order.
#check IsManifold.restrictScalars
#print axioms IsManifold.restrictScalars
#check ContMDiffWithinAt.restrictScalars
#print axioms ContMDiffWithinAt.restrictScalars
#check ContMDiffAt.restrictScalars
#print axioms ContMDiffAt.restrictScalars
#check ContMDiff.restrictScalars
#print axioms ContMDiff.restrictScalars
#check ContMDiffOn.restrictScalars
#print axioms ContMDiffOn.restrictScalars
#check Diffeomorph.restrictScalars
#print axioms Diffeomorph.restrictScalars
#check PartialDiffeomorph.restrictScalars
#print axioms PartialDiffeomorph.restrictScalars
#check contMDiff_of_comp_surjective_localDiffeomorph
#print axioms contMDiff_of_comp_surjective_localDiffeomorph
#check contMDiff_of_comp_surjective_localDiffeomorph_restrictScalars
#print axioms contMDiff_of_comp_surjective_localDiffeomorph_restrictScalars
#check contMDiffOn_of_contMDiff_restriction
#print axioms contMDiffOn_of_contMDiff_restriction

-- CochainTransgression: every intended public source declaration in source order.
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.mk
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.mk
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.F
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.F
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.complex
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.complex
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.ι
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.ι
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.zero
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.zero
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.initial_exact
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.initial_exact
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.exact
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.exact
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.mono_ι
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.mono_ι
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.epi_g
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.epi_g
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.boundary
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.boundary
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.toBoundary
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.toBoundary
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.toBoundary_ι
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.toBoundary_ι
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.ι_toBoundary
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.ι_toBoundary
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.first
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.first
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.second
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.second
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.first_shortExact
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.first_shortExact
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.second_shortExact
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.second_shortExact
#check CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.connectingTwo
#print axioms CategoryTheory.Abelian.ExtTransgression.TwoStepResolution.connectingTwo
#check CategoryTheory.Abelian.ExtTransgression.cyclesComplex
#print axioms CategoryTheory.Abelian.ExtTransgression.cyclesComplex
#check CategoryTheory.Abelian.ExtTransgression.cyclesComplex_exact
#print axioms CategoryTheory.Abelian.ExtTransgression.cyclesComplex_exact
#check CategoryTheory.Abelian.ExtTransgression.cyclesComplex_epi_g
#print axioms CategoryTheory.Abelian.ExtTransgression.cyclesComplex_epi_g
#check CategoryTheory.Abelian.ExtTransgression.iCycles_toCycles
#print axioms CategoryTheory.Abelian.ExtTransgression.iCycles_toCycles
#check CategoryTheory.Abelian.ExtTransgression.cyclesInitial_exact
#print axioms CategoryTheory.Abelian.ExtTransgression.cyclesInitial_exact
#check CategoryTheory.Abelian.ExtTransgression.cyclesResolution
#print axioms CategoryTheory.Abelian.ExtTransgression.cyclesResolution
#check CategoryTheory.Abelian.ExtTransgression.cochainTransgression
#print axioms CategoryTheory.Abelian.ExtTransgression.cochainTransgression

-- ExactFunctoriality: every intended public source declaration in source order.
#check CategoryTheory.Abelian.Ext.mapExactFunctor_compFunctor
#print axioms CategoryTheory.Abelian.Ext.mapExactFunctor_compFunctor
#check CategoryTheory.Abelian.Ext.mapExactFunctor_id
#print axioms CategoryTheory.Abelian.Ext.mapExactFunctor_id
#check CategoryTheory.Abelian.Ext.mapExactFunctor_natTrans
#print axioms CategoryTheory.Abelian.Ext.mapExactFunctor_natTrans

-- ExactFunctorComparison: every intended public source declaration in source order.
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_mk₀
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_mk₀
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_naturality
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_naturality
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_connecting
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_connecting
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_zero_bijective
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_zero_bijective
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_bijective
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.map_bijective
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.equiv
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.equiv
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.precompose
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.precompose
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.comp
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.comp
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.natTrans
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.natTrans
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.comp_natTrans
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.comp_natTrans
#check CategoryTheory.Abelian.Ext.ExactFunctorComparison.natTrans_id
#print axioms CategoryTheory.Abelian.Ext.ExactFunctorComparison.natTrans_id

/-! ## `Lib.Topology.Sheaves.AddCommGrpPushforward` -/

#check TopCat.Sheaf.pushforwardAdditive
#print axioms TopCat.Sheaf.pushforwardAdditive

/-! ## `Lib.Topology.Sheaves.Cohomology.AddCommGroup` -/

#check CategoryTheory.Sheaf.cohomologyAddCommGroup
#print axioms CategoryTheory.Sheaf.cohomologyAddCommGroup

/-! ## `Lib.Topology.Sheaves.ConstantPushforward.GlobalSections` -/

#check TopCat.ConstantSheaf.integralSheaf
#print axioms TopCat.ConstantSheaf.integralSheaf
#check TopCat.ConstantSheaf.integralHomGlobalEquiv
#print axioms TopCat.ConstantSheaf.integralHomGlobalEquiv
#check TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality
#print axioms TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality
#check TopCat.ConstantSheaf.integralHomGlobalEquiv_id
#print axioms TopCat.ConstantSheaf.integralHomGlobalEquiv_id
#check TopCat.ConstantSheaf.integralGlobalSectionsEquiv
#print axioms TopCat.ConstantSheaf.integralGlobalSectionsEquiv
#check TopCat.ConstantSheaf.integralHomPushforwardEquiv
#print axioms TopCat.ConstantSheaf.integralHomPushforwardEquiv
#check TopCat.ConstantSheaf.integralHomPushforwardEquiv_global
#print axioms TopCat.ConstantSheaf.integralHomPushforwardEquiv_global
#check TopCat.ConstantSheaf.integralHomPushforwardEquiv_naturality
#print axioms TopCat.ConstantSheaf.integralHomPushforwardEquiv_naturality
#check TopCat.ConstantSheaf.integralPushforwardHom_global
#print axioms TopCat.ConstantSheaf.integralPushforwardHom_global
#check TopCat.ConstantSheaf.integralPushforwardHom_comp
#print axioms TopCat.ConstantSheaf.integralPushforwardHom_comp
#check TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective
#print axioms TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective

-- ResolutionTransgression: every intended public source declaration in source order.
#check CategoryTheory.Sheaf.Leray.AbelianSheaf
#print axioms CategoryTheory.Sheaf.Leray.AbelianSheaf
#check CategoryTheory.Sheaf.Leray.integralSheaf
#print axioms CategoryTheory.Sheaf.Leray.integralSheaf
#check CategoryTheory.Sheaf.Leray.abelianSheafHasExt
#print axioms CategoryTheory.Sheaf.Leray.abelianSheafHasExt
#check CategoryTheory.Sheaf.Leray.sheafCohomologyAddCommGroup
#print axioms CategoryTheory.Sheaf.Leray.sheafCohomologyAddCommGroup
#check CategoryTheory.Sheaf.Leray.pushforward
#print axioms CategoryTheory.Sheaf.Leray.pushforward
#check CategoryTheory.Sheaf.Leray.pushforwardAdditive
#print axioms CategoryTheory.Sheaf.Leray.pushforwardAdditive
#check CategoryTheory.Sheaf.Leray.higherDirectImage
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImage
#check CategoryTheory.Sheaf.Leray.higherDirectImageSheaf
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageSheaf
#check CategoryTheory.Sheaf.Leray.higherDirectImageResolutionIso
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageResolutionIso
#check CategoryTheory.Sheaf.Leray.pushedResolution
#print axioms CategoryTheory.Sheaf.Leray.pushedResolution
#check CategoryTheory.Sheaf.Leray.E₂
#print axioms CategoryTheory.Sheaf.Leray.E₂
#check CategoryTheory.Sheaf.Leray.resolutionCohomologyIso
#print axioms CategoryTheory.Sheaf.Leray.resolutionCohomologyIso
#check CategoryTheory.Sheaf.Leray.resolutionExtZeroIso
#print axioms CategoryTheory.Sheaf.Leray.resolutionExtZeroIso
#check CategoryTheory.Sheaf.Leray.resolutionTransgressionMorphism
#print axioms CategoryTheory.Sheaf.Leray.resolutionTransgressionMorphism
#check CategoryTheory.Sheaf.Leray.resolutionTransgressionAdd
#print axioms CategoryTheory.Sheaf.Leray.resolutionTransgressionAdd
#check CategoryTheory.Sheaf.Leray.resolutionTransgression
#print axioms CategoryTheory.Sheaf.Leray.resolutionTransgression

-- DegreeZero: every intended public source declaration in source order.
#check CategoryTheory.Sheaf.Leray.higherDirectImageZeroIsoPushforward
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageZeroIsoPushforward
#check CategoryTheory.Sheaf.Leray.higherDirectImageZeroSheafIsoPushforward
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageZeroSheafIsoPushforward

-- Gluing over a covered base: every handwritten declaration plus structure constructors and
-- field projections, in compiled public declaration order (generated recursors excluded).
#check Mathoverflow1973.ThreefoldGluing.Data
#print axioms Mathoverflow1973.ThreefoldGluing.Data
#check Mathoverflow1973.ThreefoldGluing.Data.mk
#print axioms Mathoverflow1973.ThreefoldGluing.Data.mk
#check Mathoverflow1973.ThreefoldGluing.Data.J
#print axioms Mathoverflow1973.ThreefoldGluing.Data.J
#check Mathoverflow1973.ThreefoldGluing.Data.patch
#print axioms Mathoverflow1973.ThreefoldGluing.Data.patch
#check Mathoverflow1973.ThreefoldGluing.Data.cover
#print axioms Mathoverflow1973.ThreefoldGluing.Data.cover
#check Mathoverflow1973.ThreefoldGluing.Data.piece
#print axioms Mathoverflow1973.ThreefoldGluing.Data.piece
#check Mathoverflow1973.ThreefoldGluing.Data.toBase
#print axioms Mathoverflow1973.ThreefoldGluing.Data.toBase
#check Mathoverflow1973.ThreefoldGluing.Data.toBase_mem
#print axioms Mathoverflow1973.ThreefoldGluing.Data.toBase_mem
#check Mathoverflow1973.ThreefoldGluing.Data.transition
#print axioms Mathoverflow1973.ThreefoldGluing.Data.transition
#check Mathoverflow1973.ThreefoldGluing.Data.source_eq
#print axioms Mathoverflow1973.ThreefoldGluing.Data.source_eq
#check Mathoverflow1973.ThreefoldGluing.Data.self_eq
#print axioms Mathoverflow1973.ThreefoldGluing.Data.self_eq
#check Mathoverflow1973.ThreefoldGluing.Data.symm_eq
#print axioms Mathoverflow1973.ThreefoldGluing.Data.symm_eq
#check Mathoverflow1973.ThreefoldGluing.Data.preserves_base
#print axioms Mathoverflow1973.ThreefoldGluing.Data.preserves_base
#check Mathoverflow1973.ThreefoldGluing.Data.cocycle
#print axioms Mathoverflow1973.ThreefoldGluing.Data.cocycle
#check Mathoverflow1973.ThreefoldGluing.Data.transition_map_source
#print axioms Mathoverflow1973.ThreefoldGluing.Data.transition_map_source
#check Mathoverflow1973.ThreefoldGluing.Data.transition_inter
#print axioms Mathoverflow1973.ThreefoldGluing.Data.transition_inter
#check Mathoverflow1973.ThreefoldGluing.Data.gluingCore
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluingCore
#check Mathoverflow1973.ThreefoldGluing.Data.gluing
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluing
#check Mathoverflow1973.ThreefoldGluing.Data.Space
#print axioms Mathoverflow1973.ThreefoldGluing.Data.Space
#check Mathoverflow1973.ThreefoldGluing.Data.inclusion
#print axioms Mathoverflow1973.ThreefoldGluing.Data.inclusion
#check Mathoverflow1973.ThreefoldGluing.Data.inclusion_openEmbedding
#print axioms Mathoverflow1973.ThreefoldGluing.Data.inclusion_openEmbedding
#check Mathoverflow1973.ThreefoldGluing.Data.inclusion_jointly_surjective
#print axioms Mathoverflow1973.ThreefoldGluing.Data.inclusion_jointly_surjective
#check Mathoverflow1973.ThreefoldGluing.Data.inclusion_eq_iff
#print axioms Mathoverflow1973.ThreefoldGluing.Data.inclusion_eq_iff
#check Mathoverflow1973.ThreefoldGluing.Data.representative
#print axioms Mathoverflow1973.ThreefoldGluing.Data.representative
#check Mathoverflow1973.ThreefoldGluing.Data.inclusion_representative
#print axioms Mathoverflow1973.ThreefoldGluing.Data.inclusion_representative
#check Mathoverflow1973.ThreefoldGluing.Data.parametrization
#print axioms Mathoverflow1973.ThreefoldGluing.Data.parametrization
#check Mathoverflow1973.ThreefoldGluing.Data.parametrization_target
#print axioms Mathoverflow1973.ThreefoldGluing.Data.parametrization_target
#check Mathoverflow1973.ThreefoldGluing.Data.parametrization_transition
#print axioms Mathoverflow1973.ThreefoldGluing.Data.parametrization_transition
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.mk
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.mk
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.patch
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.patch
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.cover
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.cover
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.disjoint
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.disjoint
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.piece
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.piece
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase_mem
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase_mem
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.overlap
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.overlap
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.source_eq
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.source_eq
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.target_eq
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.target_eq
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.preserves_base
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.preserves_base
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_none_none
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_none_none
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_none_some
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_none_some
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_none
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_none
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_self
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_self
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_some_of_ne
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_some_of_ne
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_self
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_self
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_symm
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_symm
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.overlap_symm_preserves_base
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.overlap_symm_preserves_base
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase_preimage_own
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toBase_preimage_own
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.filling_preimage_eq_empty
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.filling_preimage_eq_empty
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_some_source_eq_empty
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_some_some_source_eq_empty
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_source_eq
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_source_eq
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_preserves_base
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_preserves_base
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.eq_or_eq_or_eq_of_common_base
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.eq_or_eq_or_eq_of_common_base
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_cocycle
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_cocycle
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toData
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toData
#check Mathoverflow1973.ThreefoldGluing.Data.parametrization_symm_inclusion
#print axioms Mathoverflow1973.ThreefoldGluing.Data.parametrization_symm_inclusion
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_symm
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_symm
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_inclusion
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_inclusion
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_inclusion_mem_source
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_inclusion_mem_source
#check Mathoverflow1973.ThreefoldGluing.Data.chartedSpace
#print axioms Mathoverflow1973.ThreefoldGluing.Data.chartedSpace
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_mem_atlas
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_mem_atlas
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_transition_apply
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_transition_apply
#check Mathoverflow1973.ThreefoldGluing.Data.gluedChart_transition_contMDiff
#print axioms Mathoverflow1973.ThreefoldGluing.Data.gluedChart_transition_contMDiff
#check Mathoverflow1973.ThreefoldGluing.Data.isManifold_of_contMDiffOn_transition
#print axioms Mathoverflow1973.ThreefoldGluing.Data.isManifold_of_contMDiffOn_transition
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_contMDiff
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_contMDiff
#check Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toData_transition_contMDiff
#print axioms Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toData_transition_contMDiff

/-! ## `Lib.Topology.Sheaves.ConstantPushforward` -/

#check TopCat.ConstantSheaf.presheaf
#print axioms TopCat.ConstantSheaf.presheaf
#check TopCat.ConstantSheaf.sheaf
#print axioms TopCat.ConstantSheaf.sheaf
#check TopCat.ConstantSheaf.unit
#print axioms TopCat.ConstantSheaf.unit
#check TopCat.ConstantSheaf.unit_app_surjective
#print axioms TopCat.ConstantSheaf.unit_app_surjective
#check TopCat.ConstantSheaf.unit_app_injective
#print axioms TopCat.ConstantSheaf.unit_app_injective
#check TopCat.ConstantSheaf.unit_app_bijective
#print axioms TopCat.ConstantSheaf.unit_app_bijective
#check TopCat.ConstantSheaf.rawPushforwardHom
#print axioms TopCat.ConstantSheaf.rawPushforwardHom
#check TopCat.ConstantSheaf.pushforwardHom
#print axioms TopCat.ConstantSheaf.pushforwardHom
#check TopCat.ConstantSheaf.unit_pushforwardHom
#print axioms TopCat.ConstantSheaf.unit_pushforwardHom
#check TopCat.ConstantSheaf.pushforwardHom_app_unit
#print axioms TopCat.ConstantSheaf.pushforwardHom_app_unit
#check TopCat.ConstantSheaf.pushforwardHom_isIso_of_isBasis
#print axioms TopCat.ConstantSheaf.pushforwardHom_isIso_of_isBasis
#check TopCat.ConstantSheaf.pushforwardHom_isIso
#print axioms TopCat.ConstantSheaf.pushforwardHom_isIso

/-! ## `Lib.Topology.Sheaves.FiniteClosedPushforward` -/

#check TopCat.FiniteClosedPushforward.fiber_mem_preimage
#print axioms TopCat.FiniteClosedPushforward.fiber_mem_preimage
#check TopCat.FiniteClosedPushforward.exists_open_preimage_subset
#print axioms TopCat.FiniteClosedPushforward.exists_open_preimage_subset
#check TopCat.FiniteClosedPushforward.pushforwardStalkComponent
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkComponent
#check TopCat.FiniteClosedPushforward.pushforwardStalkComponent_germ
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkComponent_germ
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_apply
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_apply
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_germ
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_germ
#check TopCat.FiniteClosedPushforward.exists_section_germ_eq_of_finite
#print axioms TopCat.FiniteClosedPushforward.exists_section_germ_eq_of_finite
#check TopCat.FiniteClosedPushforward.pushforward_germ_eq_of_fiber_germ_eq
#print axioms TopCat.FiniteClosedPushforward.pushforward_germ_eq_of_fiber_germ_eq
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_injective
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_injective
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_surjective
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_surjective
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_bijective
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_bijective
#check TopCat.FiniteClosedPushforward.pushforwardStalkEquiv
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkEquiv
#check TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_apply
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_apply
#check TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_germ
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_germ
#check TopCat.FiniteClosedPushforward.pushforwardStalkHom_naturality
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkHom_naturality
#check TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_naturality
#print axioms TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_naturality

/-! ## `Lib.Topology.Sheaves.FiniteClosedPushforward.Exact` -/

#check TopCat.FiniteClosedPushforward.pullback_preservesFiniteLimits
#print axioms TopCat.FiniteClosedPushforward.pullback_preservesFiniteLimits
#check TopCat.FiniteClosedPushforward.pushforward_preservesInjectiveObjects
#print axioms TopCat.FiniteClosedPushforward.pushforward_preservesInjectiveObjects
#check TopCat.FiniteClosedPushforward.pushforward_exact
#print axioms TopCat.FiniteClosedPushforward.pushforward_exact
#check TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
#print axioms TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
#check TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
#print axioms TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
#check TopCat.FiniteClosedPushforward.pushforward_shortExact
#print axioms TopCat.FiniteClosedPushforward.pushforward_shortExact

/-! ## `Lib.Topology.Sheaves.FiniteClosedPushforward.Cohomology` -/

#check TopCat.FiniteClosedPushforward.cohomologyForward
#print axioms TopCat.FiniteClosedPushforward.cohomologyForward
#check TopCat.FiniteClosedPushforward.cohomologyForward_bijective
#print axioms TopCat.FiniteClosedPushforward.cohomologyForward_bijective
#check TopCat.FiniteClosedPushforward.cohomologyEquiv
#print axioms TopCat.FiniteClosedPushforward.cohomologyEquiv
#check TopCat.FiniteClosedPushforward.cohomologyEquiv_symm_apply
#print axioms TopCat.FiniteClosedPushforward.cohomologyEquiv_symm_apply
#check TopCat.FiniteClosedPushforward.cohomologyForward_equiv
#print axioms TopCat.FiniteClosedPushforward.cohomologyForward_equiv
#check TopCat.FiniteClosedPushforward.cohomologyForward_naturality
#print axioms TopCat.FiniteClosedPushforward.cohomologyForward_naturality
#check TopCat.FiniteClosedPushforward.cohomologyEquiv_naturality
#print axioms TopCat.FiniteClosedPushforward.cohomologyEquiv_naturality

/-! ## `Lib.Topology.Sheaves.OpenRestriction` -/

#check TopCat.Sheaf.OpenRestriction.inclusion
#print axioms TopCat.Sheaf.OpenRestriction.inclusion
#check TopCat.Sheaf.OpenRestriction.inclusion_isOpenEmbedding
#print axioms TopCat.Sheaf.OpenRestriction.inclusion_isOpenEmbedding
#check TopCat.Sheaf.OpenRestriction.inclusion_mono
#print axioms TopCat.Sheaf.OpenRestriction.inclusion_mono
#check TopCat.Sheaf.OpenRestriction.openImage
#print axioms TopCat.Sheaf.OpenRestriction.openImage
#check TopCat.Sheaf.OpenRestriction.openImage_full
#print axioms TopCat.Sheaf.OpenRestriction.openImage_full
#check TopCat.Sheaf.OpenRestriction.preimageOpen
#print axioms TopCat.Sheaf.OpenRestriction.preimageOpen
#check TopCat.Sheaf.OpenRestriction.openImage_obj_le
#print axioms TopCat.Sheaf.OpenRestriction.openImage_obj_le
#check TopCat.Sheaf.OpenRestriction.openImage_preimage
#print axioms TopCat.Sheaf.OpenRestriction.openImage_preimage
#check TopCat.Sheaf.OpenRestriction.costructuredArrow_isEmpty
#print axioms TopCat.Sheaf.OpenRestriction.costructuredArrow_isEmpty
#check TopCat.Sheaf.OpenRestriction.lan_obj_isZero_of_not_le
#print axioms TopCat.Sheaf.OpenRestriction.lan_obj_isZero_of_not_le
#check TopCat.Sheaf.OpenRestriction.lan_preservesMonomorphisms
#print axioms TopCat.Sheaf.OpenRestriction.lan_preservesMonomorphisms
#check TopCat.Sheaf.OpenRestriction.openImage_continuous
#print axioms TopCat.Sheaf.OpenRestriction.openImage_continuous
#check TopCat.Sheaf.OpenRestriction.openImage_cocontinuous
#print axioms TopCat.Sheaf.OpenRestriction.openImage_cocontinuous
#check TopCat.Sheaf.OpenRestriction.restriction
#print axioms TopCat.Sheaf.OpenRestriction.restriction
#check TopCat.Sheaf.OpenRestriction.restriction_eq_sheafRestrict
#print axioms TopCat.Sheaf.OpenRestriction.restriction_eq_sheafRestrict
#check TopCat.Sheaf.OpenRestriction.restriction_additive
#print axioms TopCat.Sheaf.OpenRestriction.restriction_additive
#check TopCat.Sheaf.OpenRestriction.restriction_rightAdjoint
#print axioms TopCat.Sheaf.OpenRestriction.restriction_rightAdjoint
#check TopCat.Sheaf.OpenRestriction.restriction_leftAdjoint
#print axioms TopCat.Sheaf.OpenRestriction.restriction_leftAdjoint
#check TopCat.Sheaf.OpenRestriction.restriction_preservesFiniteLimits
#print axioms TopCat.Sheaf.OpenRestriction.restriction_preservesFiniteLimits
#check TopCat.Sheaf.OpenRestriction.restriction_preservesFiniteColimits
#print axioms TopCat.Sheaf.OpenRestriction.restriction_preservesFiniteColimits
#check TopCat.Sheaf.OpenRestriction.extension
#print axioms TopCat.Sheaf.OpenRestriction.extension
#check TopCat.Sheaf.OpenRestriction.extension_preservesMonomorphisms
#print axioms TopCat.Sheaf.OpenRestriction.extension_preservesMonomorphisms
#check TopCat.Sheaf.OpenRestriction.restriction_preservesInjectiveObjects
#print axioms TopCat.Sheaf.OpenRestriction.restriction_preservesInjectiveObjects

/-! ## `Lib.Topology.Sheaves.OpenRestriction.Cohomology` -/

#check TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
#print axioms TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
#check TopCat.Sheaf.OpenRestriction.freeOpen
#print axioms TopCat.Sheaf.OpenRestriction.freeOpen
#check TopCat.Sheaf.OpenRestriction.freeHomEquiv
#print axioms TopCat.Sheaf.OpenRestriction.freeHomEquiv
#check TopCat.Sheaf.OpenRestriction.freeHomEquiv_naturality
#print axioms TopCat.Sheaf.OpenRestriction.freeHomEquiv_naturality
#check TopCat.Sheaf.OpenRestriction.freeHomAddEquiv
#print axioms TopCat.Sheaf.OpenRestriction.freeHomAddEquiv
#check TopCat.Sheaf.OpenRestriction.openImage_top
#print axioms TopCat.Sheaf.OpenRestriction.openImage_top
#check TopCat.Sheaf.OpenRestriction.restrictionGlobalEquiv
#print axioms TopCat.Sheaf.OpenRestriction.restrictionGlobalEquiv
#check TopCat.Sheaf.OpenRestriction.restrictionGlobalEquiv_naturality
#print axioms TopCat.Sheaf.OpenRestriction.restrictionGlobalEquiv_naturality
#check TopCat.Sheaf.OpenRestriction.homRestrictionEquiv
#print axioms TopCat.Sheaf.OpenRestriction.homRestrictionEquiv
#check TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_sections
#print axioms TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_sections
#check TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_naturality
#print axioms TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_naturality
#check TopCat.Sheaf.OpenRestriction.representingUnit
#print axioms TopCat.Sheaf.OpenRestriction.representingUnit
#check TopCat.Sheaf.OpenRestriction.representingUnit_comp
#print axioms TopCat.Sheaf.OpenRestriction.representingUnit_comp
#check TopCat.Sheaf.OpenRestriction.representingUnit_bijective
#print axioms TopCat.Sheaf.OpenRestriction.representingUnit_bijective
#check TopCat.Sheaf.OpenRestriction.zeroEquiv
#print axioms TopCat.Sheaf.OpenRestriction.zeroEquiv
#check TopCat.Sheaf.OpenRestriction.cohomologyForward
#print axioms TopCat.Sheaf.OpenRestriction.cohomologyForward
#check TopCat.Sheaf.OpenRestriction.cohomologyForward_bijective
#print axioms TopCat.Sheaf.OpenRestriction.cohomologyForward_bijective
#check TopCat.Sheaf.OpenRestriction.cohomologyEquiv
#print axioms TopCat.Sheaf.OpenRestriction.cohomologyEquiv
#check TopCat.Sheaf.OpenRestriction.cohomologyEquiv_mk₀
#print axioms TopCat.Sheaf.OpenRestriction.cohomologyEquiv_mk₀
#check TopCat.Sheaf.OpenRestriction.cohomologyEquiv_naturality
#print axioms TopCat.Sheaf.OpenRestriction.cohomologyEquiv_naturality

/-! ## `Lib.Topology.Sheaves.PrincipalCoverLocalSystem` -/

#check PrincipalCoverLocalSystem.LiftedOpen
#print axioms PrincipalCoverLocalSystem.LiftedOpen
#check PrincipalCoverLocalSystem.liftedAction
#print axioms PrincipalCoverLocalSystem.liftedAction
#check PrincipalCoverLocalSystem.liftedInclusion
#print axioms PrincipalCoverLocalSystem.liftedInclusion
#check PrincipalCoverLocalSystem.equivariantSections
#print axioms PrincipalCoverLocalSystem.equivariantSections
#check PrincipalCoverLocalSystem.mem_equivariantSections
#print axioms PrincipalCoverLocalSystem.mem_equivariantSections
#check PrincipalCoverLocalSystem.restrict
#print axioms PrincipalCoverLocalSystem.restrict
#check PrincipalCoverLocalSystem.presheaf
#print axioms PrincipalCoverLocalSystem.presheaf
#check PrincipalCoverLocalSystem.presheaf_map_apply
#print axioms PrincipalCoverLocalSystem.presheaf_map_apply
#check PrincipalCoverLocalSystem.presheaf_isSheaf
#print axioms PrincipalCoverLocalSystem.presheaf_isSheaf
#check PrincipalCoverLocalSystem.sheaf
#print axioms PrincipalCoverLocalSystem.sheaf
#check PrincipalCoverLocalSystem.invariantCoefficients
#print axioms PrincipalCoverLocalSystem.invariantCoefficients
#check PrincipalCoverLocalSystem.liftedTopHomeomorph
#print axioms PrincipalCoverLocalSystem.liftedTopHomeomorph
#check PrincipalCoverLocalSystem.globalSectionsEquivInvariantCoefficients
#print axioms PrincipalCoverLocalSystem.globalSectionsEquivInvariantCoefficients
#check PrincipalCoverLocalSystem.globalSectionsEquivInvariantCoefficients_apply
#print axioms PrincipalCoverLocalSystem.globalSectionsEquivInvariantCoefficients_apply

/-! ## `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Stalk` -/

#check PrincipalCoverLocalSystem.evaluationCocone
#print axioms PrincipalCoverLocalSystem.evaluationCocone
#check PrincipalCoverLocalSystem.stalkEvaluation
#print axioms PrincipalCoverLocalSystem.stalkEvaluation
#check PrincipalCoverLocalSystem.stalkEvaluation_germ
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_germ
#check PrincipalCoverLocalSystem.stalkEvaluation_germ_smul
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_germ_smul
#check PrincipalCoverLocalSystem.stalkEvaluation_surjective
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_surjective
#check PrincipalCoverLocalSystem.stalkEvaluation_injective
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_injective
#check PrincipalCoverLocalSystem.stalkEvaluation_bijective
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_bijective
#check PrincipalCoverLocalSystem.stalkEvaluation_isIso
#print axioms PrincipalCoverLocalSystem.stalkEvaluation_isIso
#check PrincipalCoverLocalSystem.stalkIsoCoefficientAtLift
#print axioms PrincipalCoverLocalSystem.stalkIsoCoefficientAtLift

/-! ## `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Comparison` -/

#check PrincipalCoverLocalSystem.StalkComparisonData
#print axioms PrincipalCoverLocalSystem.StalkComparisonData
#check PrincipalCoverLocalSystem.StalkComparisonData.mk
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.mk
#check PrincipalCoverLocalSystem.StalkComparisonData.stalkMap
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.stalkMap
#check PrincipalCoverLocalSystem.StalkComparisonData.section_isLocallyConstant
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.section_isLocallyConstant
#check PrincipalCoverLocalSystem.StalkComparisonData.section_equivariant
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.section_equivariant
#check PrincipalCoverLocalSystem.StalkComparisonData.toSection
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.toSection
#check PrincipalCoverLocalSystem.StalkComparisonData.sectionMap
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.sectionMap
#check PrincipalCoverLocalSystem.StalkComparisonData.presheafHom
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.presheafHom
#check PrincipalCoverLocalSystem.StalkComparisonData.hom
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.hom
#check PrincipalCoverLocalSystem.StalkComparisonData.stalkFunctorMap_comp_stalkEvaluation
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.stalkFunctorMap_comp_stalkEvaluation
#check PrincipalCoverLocalSystem.StalkComparisonData.stalkFunctorMap_isIso
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.stalkFunctorMap_isIso
#check PrincipalCoverLocalSystem.StalkComparisonData.hom_isIso
#print axioms PrincipalCoverLocalSystem.StalkComparisonData.hom_isIso

/-! ## `Lib.CategoryTheory.Sites.Leray.HigherDirectImageSheafification` -/

#check CategoryTheory.Sheaf.Leray.presheafStalk_preservesFiniteLimits
#print axioms CategoryTheory.Sheaf.Leray.presheafStalk_preservesFiniteLimits
#check CategoryTheory.Sheaf.Leray.presheafStalk_preservesFiniteColimits
#print axioms CategoryTheory.Sheaf.Leray.presheafStalk_preservesFiniteColimits
#check CategoryTheory.Sheaf.Leray.mapComplexHomologyIso
#print axioms CategoryTheory.Sheaf.Leray.mapComplexHomologyIso
#check CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_hom_naturality
#print axioms CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_hom_naturality
#check CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_hom_naturality_assoc
#print axioms CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_hom_naturality_assoc
#check CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_inv_naturality
#print axioms CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_inv_naturality
#check CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_inv_naturality_assoc
#print axioms CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_inv_naturality_assoc
#check CategoryTheory.Sheaf.Leray.underlyingPresheafComplex
#print axioms CategoryTheory.Sheaf.Leray.underlyingPresheafComplex
#check CategoryTheory.Sheaf.Leray.homologyPresheaf
#print axioms CategoryTheory.Sheaf.Leray.homologyPresheaf
#check CategoryTheory.Sheaf.Leray.stalkHomologyPresheafIso
#print axioms CategoryTheory.Sheaf.Leray.stalkHomologyPresheafIso
#check CategoryTheory.Sheaf.Leray.sheafification
#print axioms CategoryTheory.Sheaf.Leray.sheafification
#check CategoryTheory.Sheaf.Leray.sheafification_additive
#print axioms CategoryTheory.Sheaf.Leray.sheafification_additive
#check CategoryTheory.Sheaf.Leray.sheafification_preservesFiniteLimits
#print axioms CategoryTheory.Sheaf.Leray.sheafification_preservesFiniteLimits
#check CategoryTheory.Sheaf.Leray.sheafification_preservesFiniteColimits
#print axioms CategoryTheory.Sheaf.Leray.sheafification_preservesFiniteColimits
#check CategoryTheory.Sheaf.Leray.sheafificationUnderlyingIso
#print axioms CategoryTheory.Sheaf.Leray.sheafificationUnderlyingIso
#check CategoryTheory.Sheaf.Leray.sheafificationComplexIso
#print axioms CategoryTheory.Sheaf.Leray.sheafificationComplexIso
#check CategoryTheory.Sheaf.Leray.sheafHomologyIsoSheafification
#print axioms CategoryTheory.Sheaf.Leray.sheafHomologyIsoSheafification
#check CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationIso
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationIso
#check CategoryTheory.Sheaf.Leray.inverseImageResolutionSections
#print axioms CategoryTheory.Sheaf.Leray.inverseImageResolutionSections
#check CategoryTheory.Sheaf.Leray.higherDirectImageResolutionPresheafObjIso
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageResolutionPresheafObjIso
#check CategoryTheory.Sheaf.Leray.higherDirectImageResolutionStalkIso
#print axioms CategoryTheory.Sheaf.Leray.higherDirectImageResolutionStalkIso

/-! ## `Lib.LinearAlgebra.Dual.Contragredient` -/

#check LinearRepresentation.ofMultiplicativeEquiv
#print axioms LinearRepresentation.ofMultiplicativeEquiv
#check LinearRepresentation.ofMultiplicativeEquiv_apply
#print axioms LinearRepresentation.ofMultiplicativeEquiv_apply
#check LinearRepresentation.ofMultiplicative
#print axioms LinearRepresentation.ofMultiplicative
#check LinearRepresentation.ofMultiplicative_apply
#print axioms LinearRepresentation.ofMultiplicative_apply
#check LinearRepresentation.contragredient
#print axioms LinearRepresentation.contragredient
#check LinearRepresentation.contragredient_apply
#print axioms LinearRepresentation.contragredient_apply
#check LinearRepresentation.freeGroup_invariant_iff
#print axioms LinearRepresentation.freeGroup_invariant_iff

/-! ## `Lib.CategoryTheory.Sites.Leray.StalkLocalCriterion` -/

#check CategoryTheory.Sheaf.Leray.stalkMap_bijective_of_local_lift_kill
#print axioms CategoryTheory.Sheaf.Leray.stalkMap_bijective_of_local_lift_kill

/-! ## `Lib.Topology.Homotopy.LocallyContractible` -/

#check StronglyLocallyContractibleSpace.of_open_neighborhoods
#print axioms StronglyLocallyContractibleSpace.of_open_neighborhoods
#check IsLocalHomeomorph.stronglyLocallyContractibleSpace_of_surjective
#print axioms IsLocalHomeomorph.stronglyLocallyContractibleSpace_of_surjective

/-! ## `Lib.Analysis.Normed.LocallyContractible` -/

#check normedSpaceStronglyLocallyContractible
#print axioms normedSpaceStronglyLocallyContractible
#check Metric.ballInClosedBallHomeomorph
#print axioms Metric.ballInClosedBallHomeomorph
#check Metric.ballInClosedBall_contractible
#print axioms Metric.ballInClosedBall_contractible
#check Metric.closedBallStronglyLocallyContractible
#print axioms Metric.closedBallStronglyLocallyContractible

/-! ## `Lib.Geometry.Manifold.ChartedSpace.LocallyContractible` -/

#check chartedSpaceStronglyLocallyContractible
#print axioms chartedSpaceStronglyLocallyContractible
