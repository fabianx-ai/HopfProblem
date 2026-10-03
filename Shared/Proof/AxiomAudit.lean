/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Shared.Proof.Algebra.Group.LatticeImageCollapse
import Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix
import Shared.Proof.AlgebraicTopology.Hurewicz.SphereGenerator
import Shared.Proof.Analysis.Complex.RiemannMapping.SectorRoots
import Shared.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization
import Shared.Proof.Data.Int.SignedResidual

/-!
# Axiom probes for the declarations under `Shared/Proof`

Compile this file directly; nothing imports it, because `#print axioms` is an evidence
command rather than library content.

`Shared/Proof` holds the declarations that both the old proof (`Hopf/Proof`) and the center
construction (`Center/Proof`, `W4W1` on `center-solution`) use.  `Solution.lean` covers those in
the dependency closure of the old proof's final theorem; this file probes every declaration of
the tree regardless.
-/

/-! ## `Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix` -/

#check @SixthHurewicz.cubeHomologyClass
#print axioms SixthHurewicz.cubeHomologyClass
#check @SixthHurewicz.homotopyMap
#print axioms SixthHurewicz.homotopyMap
#check @SixthHurewicz.hurewiczLinearEquiv
#print axioms SixthHurewicz.hurewiczLinearEquiv
#check @SixthHurewicz.hurewiczLinearEquiv_natural
#print axioms SixthHurewicz.hurewiczLinearEquiv_natural

/-! ## `Shared.Proof.AlgebraicTopology.Hurewicz.SphereGenerator` -/

#check @SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective
#print axioms SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective

/-! ## `Shared.Proof.Analysis.Complex.RiemannMapping.SectorRoots` -/

#check @RiemannBoundary.cubic_sector_slack
#print axioms RiemannBoundary.cubic_sector_slack
#check @RiemannBoundary.quartic_sector_slack
#print axioms RiemannBoundary.quartic_sector_slack
#check @RiemannBoundary.principalRoot_three_upper
#print axioms RiemannBoundary.principalRoot_three_upper
#check @RiemannBoundary.quarticRootRotation
#print axioms RiemannBoundary.quarticRootRotation
#check @RiemannBoundary.quarticRootRotation_re
#print axioms RiemannBoundary.quarticRootRotation_re
#check @RiemannBoundary.quarticRootRotation_im
#print axioms RiemannBoundary.quarticRootRotation_im
#check @RiemannBoundary.norm_quarticRootRotation
#print axioms RiemannBoundary.norm_quarticRootRotation
#check @RiemannBoundary.quarticRootRotation_pow_four
#print axioms RiemannBoundary.quarticRootRotation_pow_four
#check @RiemannBoundary.rotatedPrincipalRootFour
#print axioms RiemannBoundary.rotatedPrincipalRootFour
#check @RiemannBoundary.rotatedPrincipalRootFour_pow
#print axioms RiemannBoundary.rotatedPrincipalRootFour_pow
#check @RiemannBoundary.rotatedPrincipalRootFour_zero
#print axioms RiemannBoundary.rotatedPrincipalRootFour_zero
#check @RiemannBoundary.norm_rotatedPrincipalRootFour
#print axioms RiemannBoundary.norm_rotatedPrincipalRootFour
#check @RiemannBoundary.rotatedPrincipalRootFour_re
#print axioms RiemannBoundary.rotatedPrincipalRootFour_re
#check @RiemannBoundary.rotatedPrincipalRootFour_im
#print axioms RiemannBoundary.rotatedPrincipalRootFour_im
#check @RiemannBoundary.rotatedPrincipalRootFour_re_add_im
#print axioms RiemannBoundary.rotatedPrincipalRootFour_re_add_im
#check @RiemannBoundary.rotatedPrincipalRootFour_upper
#print axioms RiemannBoundary.rotatedPrincipalRootFour_upper
#check @RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary
#print axioms RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary
#check @RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im
#print axioms RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im
#check @RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper
#print axioms RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper
#check @RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero
#print axioms RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero
#check @RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper
#print axioms RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper

/-! ## `Shared.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization` -/

#check @TriangleRiemannNormalization.discCoordinate
#print axioms TriangleRiemannNormalization.discCoordinate
#check @TriangleRiemannNormalization.discCoordinate_injective
#print axioms TriangleRiemannNormalization.discCoordinate_injective
#check @TriangleRiemannNormalization.discCoordinate_ne
#print axioms TriangleRiemannNormalization.discCoordinate_ne
#check @TriangleRiemannNormalization.discCoordinate_norm_le
#print axioms TriangleRiemannNormalization.discCoordinate_norm_le
#check @TriangleRiemannNormalization.punctureMap
#print axioms TriangleRiemannNormalization.punctureMap
#check @TriangleRiemannNormalization.punctureMap_isEmbedding
#print axioms TriangleRiemannNormalization.punctureMap_isEmbedding
#check @TriangleRiemannNormalization.punctureMap_surjective
#print axioms TriangleRiemannNormalization.punctureMap_surjective
#check @TriangleRiemannNormalization.punctureHomeomorph
#print axioms TriangleRiemannNormalization.punctureHomeomorph
#check @TriangleRiemannNormalization.normalizationHomeomorph
#print axioms TriangleRiemannNormalization.normalizationHomeomorph
#check @TriangleRiemannNormalization.normalizationHomeomorph_apply
#print axioms TriangleRiemannNormalization.normalizationHomeomorph_apply
#check @TriangleRiemannNormalization.normalizationHomeomorph_first
#print axioms TriangleRiemannNormalization.normalizationHomeomorph_first
#check @TriangleRiemannNormalization.normalizationHomeomorph_second
#print axioms TriangleRiemannNormalization.normalizationHomeomorph_second
#check @TriangleRiemannNormalization.normalizationHomeomorph_strict_iff
#print axioms TriangleRiemannNormalization.normalizationHomeomorph_strict_iff

/-! ## `Shared.Proof.Data.Int.SignedResidual` -/

#check @ThreefoldHomology.signed_residual_coordinate_zero
#print axioms ThreefoldHomology.signed_residual_coordinate_zero

/-! ## `Shared.Proof.Algebra.Group.LatticeImageCollapse` -/

#check @LatticeImageCollapse.A1
#print axioms LatticeImageCollapse.A1
#check @LatticeImageCollapse.A2
#print axioms LatticeImageCollapse.A2
#check @LatticeImageCollapse.epsilon
#print axioms LatticeImageCollapse.epsilon
#check @LatticeImageCollapse.epsilonPrime
#print axioms LatticeImageCollapse.epsilonPrime
#check @LatticeImageCollapse.gamma
#print axioms LatticeImageCollapse.gamma
#check @LatticeImageCollapse.image_eq_one_of_gamma_eq_zero
#print axioms LatticeImageCollapse.image_eq_one_of_gamma_eq_zero
#check @LatticeImageCollapse.image_eq_zpow_gamma
#print axioms LatticeImageCollapse.image_eq_zpow_gamma
#check @LatticeImageCollapse.gamma_epsilonPrime
#print axioms LatticeImageCollapse.gamma_epsilonPrime
#check @LatticeImageCollapse.image_epsilonPrime_eq
#print axioms LatticeImageCollapse.image_epsilonPrime_eq
#check @LatticeImageCollapse.image_firstBasis_eq
#print axioms LatticeImageCollapse.image_firstBasis_eq
#check @LatticeImageCollapse.A1_fixes_epsilon
#print axioms LatticeImageCollapse.A1_fixes_epsilon
#check @LatticeImageCollapse.image_epsilon_commute_first
#print axioms LatticeImageCollapse.image_epsilon_commute_first
#check @LatticeImageCollapse.A2_fixes_epsilonPrime
#print axioms LatticeImageCollapse.A2_fixes_epsilonPrime
#check @LatticeImageCollapse.image_epsilon_commute_second
#print axioms LatticeImageCollapse.image_epsilon_commute_second
