/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantProductH1Comparison

/-!
# Fibre-independence in a contractible product

Restriction of a constant-sheaf H¹ class to the fibres of `S × X` is independent
of the chosen point of a contractible base `S`, under the canonical product marking.

This is the degree-one case of the statement that homotopic maps induce the same map on sheaf
cohomology with constant coefficients (Bredon, *Sheaf Theory*, II.11), obtained here from the
comparison with singular cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory ContinuousMap

namespace TopCat.ConstantProductH1

variable (S X : Type) [TopologicalSpace S] [TopologicalSpace X]
  [CompactSpace S] [T2Space S] [ContractibleSpace S]
  [CompactSpace X] [T2Space X]

omit [CompactSpace S] [T2Space S] [CompactSpace X] [T2Space X] in
/-- Any two based-fibre inclusions in a contractible product are homotopic. -/
theorem basedFibreInclusion_homotopic (s t : S) :
    (basedFibreInclusion S X s).hom.Homotopic
      (basedFibreInclusion S X t).hom := by
  change
    ((ContinuousMap.const X s).prodMk (ContinuousMap.id X)).Homotopic
      ((ContinuousMap.const X t).prodMk (ContinuousMap.id X))
  have hS := (basedContraction_homotopic S s).trans
    (basedContraction_homotopic S t).symm
  have hconst : (ContinuousMap.const X s).Homotopic (ContinuousMap.const X t) := by
    simpa using hS.comp (.refl (ContinuousMap.const X s))
  exact hconst.prodMk (.refl (ContinuousMap.id X))

/-- Pullback of native constant-sheaf H¹ to a product fibre is independent of the chosen base
point.  This is equality of the actual Ext-defined pullback maps, not merely equality after a
chosen coordinate isomorphism. -/
theorem nativePullback_basedFibreInclusion_eq
    (A : AddCommGrpCat.{0}) (s t : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) :
    TopCat.ConstantSheafCohomology.pullback
        (basedFibreInclusion S X s)
        (basedFibreInclusion_isClosedMap S X s)
        (basedFibreInclusion_finite_fibres S X s) A 1 =
      TopCat.ConstantSheafCohomology.pullback
        (basedFibreInclusion S X t)
        (basedFibreInclusion_isClosedMap S X t)
        (basedFibreInclusion_finite_fibres S X t) A 1 := by
  let _ : IsIso (HomologicalComplex.homologyMap
      (TopCat.SingularCochainSheaf.globalCochainComparison
        (TopCat.of (S × X)) A) 1) :=
    TopCat.SingularCochainSheaf.globalCochainComparison_homology_isIso_one
      (TopCat.of (S × X)) A
      (TopCat.SingularCochainSheaf.hasSmallChainEquivalences_barycentric
        (TopCat.of (S × X)))
  let _ : IsIso (HomologicalComplex.homologyMap
      (TopCat.SingularCochainSheaf.globalCochainComparison
        (TopCat.of X) A) 1) :=
    TopCat.SingularCochainSheaf.globalCochainComparison_homology_isIso_one
      (TopCat.of X) A
      (TopCat.SingularCochainSheaf.hasSmallChainEquivalences_barycentric
        (TopCat.of X))
  let cX := TopCat.SingularCochainSheaf.h1Comparison (TopCat.of X) A hX
  apply (cancel_mono cX.hom).mp
  rw [TopCat.SingularCochainSheaf.h1Comparison_naturality
      (basedFibreInclusion S X s)
      (basedFibreInclusion_isClosedMap S X s)
      (basedFibreInclusion_finite_fibres S X s) A hX hProd,
    TopCat.SingularCochainSheaf.h1Comparison_naturality
      (basedFibreInclusion S X t)
      (basedFibreInclusion_isClosedMap S X t)
      (basedFibreInclusion_finite_fibres S X t) A hX hProd,
    AlgebraicTopology.SingularCochains.homologyMap_eq_of_homotopy A
      (Classical.choice (basedFibreInclusion_homotopic S X s t)) 1]

end TopCat.ConstantProductH1
