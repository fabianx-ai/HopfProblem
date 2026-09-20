/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.BarycentricSmallChains
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.FiniteClosedH1

/-!
# The natural constant-sheaf `H¹` comparison

For a finite closed map between compact Hausdorff locally contractible spaces, the canonical
degree-one comparison from constant-sheaf cohomology to native singular cohomology commutes with
pullback.  The proof uses the current singular-cochain sheaf resolution and the barycentric
small-chain theorem.

This is a topological cohomology comparison only.

Reference: Bredon, *Sheaf Theory*, III.1.1, and Godement, *Topologie algébrique et théorie des
faisceaux*, II.5.10.1 (sheaf cohomology with constant coefficients agrees with singular
cohomology on a paracompact locally contractible space).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

/-- Constant-sheaf `H¹` is naturally isomorphic to native singular `H¹` for finite closed maps
between compact Hausdorff locally contractible spaces. -/
theorem exists_h1Comparison_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : TopCat.of X ⟶ TopCat.of Y)
    (hf : IsClosedMap f)
    (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (A : AddCommGrpCat.{0})
    (hX : LocallyContractibleSpace X)
    (hY : LocallyContractibleSpace Y) :
    ∃ (cX :
        @AddCommGrpCat.of
            (CategoryTheory.Sheaf.H.{0}
              (TopCat.ConstantSheaf.sheaf (TopCat.of X) A) 1)
            (CategoryTheory.Sheaf.cohomologyAddCommGroup
              (TopCat.ConstantSheaf.sheaf (TopCat.of X) A) 1) ≅
          (AlgebraicTopology.SingularCochains.complex X A).homology 1)
      (cY :
        @AddCommGrpCat.of
            (CategoryTheory.Sheaf.H.{0}
              (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) 1)
            (CategoryTheory.Sheaf.cohomologyAddCommGroup
              (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) 1) ≅
          (AlgebraicTopology.SingularCochains.complex Y A).homology 1),
      TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫ cX.hom =
        cY.hom ≫ HomologicalComplex.homologyMap
          (AlgebraicTopology.SingularCochains.pullback A f.hom) 1 := by
  let : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison (TopCat.of X) A) 1) :=
    globalCochainComparison_homology_isIso_one (TopCat.of X) A
      (hasSmallChainEquivalences_barycentric (TopCat.of X))
  let : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison (TopCat.of Y) A) 1) :=
    globalCochainComparison_homology_isIso_one (TopCat.of Y) A
      (hasSmallChainEquivalences_barycentric (TopCat.of Y))
  exact ⟨h1Comparison (TopCat.of X) A hX,
    h1Comparison (TopCat.of Y) A hY,
    h1Comparison_naturality f hf hfinite A hX hY⟩

end TopCat.SingularCochainSheaf
