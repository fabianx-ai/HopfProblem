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

