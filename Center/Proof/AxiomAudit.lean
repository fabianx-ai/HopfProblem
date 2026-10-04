/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Center.Proof.Topology.Sheaves.Cohomology.SphereTwo
import Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots
import Center.Proof.AlgebraicTopology.Hurewicz.SphereGenerator
import Center.Proof.Algebra.Group.ResidualRelations
import Center.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter

/-!
# Axiom probes for the center construction's declarations under `Center/Proof`

Compile this file directly; nothing imports it, because `#print axioms` is an evidence
command rather than library content.

`Solution.lean` probes the old proof's final theorem and `Lib/AxiomAudit.lean` the reusable
library; neither covers `Center/Proof`.  The probes below moved here verbatim from
`Hopf/Proof/AxiomAudit.lean` together with their declarations:

* the four two-sphere vanishing theorems of
  `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean`;
* the cube-root wedge reversal `RiemannBoundary.principalRoot_three_reverse_of_wedge` and the
  rotated fourth-root wedge reversal `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge`
  of `Center/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` (the latter was the last
  probe of `Hopf/Proof/AxiomAudit.lean`, now deleted).

`SixthHurewicz.exists_sphereMap_of_homologySixEquiv` of
`Center/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` had no probe before; it gets one
here.  So do `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth` and
`FundamentalGroup.VanKampen.exists_stageCharacter`, whose `Lib/AxiomAudit.lean` probes were dropped
when their files went to `Hopf/Proof` (review of 2026-10-04, F6); with them every declaration of
`Center/Proof` is probed.
-/

/-! ## `Center.Proof.Topology.Sheaves.Cohomology.SphereTwo` -/

#check @TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo

/-! ## `Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots` -/

#check RiemannBoundary.principalRoot_three_reverse_of_wedge
#print axioms RiemannBoundary.principalRoot_three_reverse_of_wedge
#check RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge
#print axioms RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge

/-! ## `Center.Proof.AlgebraicTopology.Hurewicz.SphereGenerator` -/

#check SixthHurewicz.exists_sphereMap_of_homologySixEquiv
#print axioms SixthHurewicz.exists_sphereMap_of_homologySixEquiv

/-! ## `Center.Proof.Algebra.Group.ResidualRelations` -/

#check ResidualRelations.eq_one_of_mul_eq_one_cube_fourth
#print axioms ResidualRelations.eq_one_of_mul_eq_one_cube_fourth

/-! ## `Center.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter` -/

#check FundamentalGroup.VanKampen.exists_stageCharacter
#print axioms FundamentalGroup.VanKampen.exists_stageCharacter
