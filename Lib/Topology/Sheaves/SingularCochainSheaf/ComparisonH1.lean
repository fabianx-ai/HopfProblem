/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnit

/-!
# Constant-sheaf cohomology and singular cohomology in degree one

For a locally contractible space `X` and an abelian group `A` the first cohomology group of the
constant sheaf `A_X` is isomorphic to the first singular cohomology group `H¹(X; A)`
(Bredon, *Sheaf Theory*, III §1; Warner, *Foundations of Differentiable Manifolds and Lie
Groups*, 5.32).  The isomorphism is obtained from the singular-cochain sheafification unit, whose
degree-one homology map is assumed invertible.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Given a locally contractible space `X` and the hypothesis, taken as an instance, that the
degree-one homology map of the singular-cochain sheafification unit `globalCochainComparison X A`
is an isomorphism, the first cohomology group of the constant sheaf `A_X` is isomorphic to the
first singular cohomology group `H¹(X; A)`.  Invertibility of that homology map is the content of
the comparison theorem (Bredon III §1) and is assumed here, not proved. -/
def h1Comparison (hLC : LocallyContractibleSpace X)
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (TopCat.ConstantSheaf.sheaf X A) 1) ≅
      (AlgebraicTopology.SingularCochains.complex X A).homology 1 :=
  constantSheafGlobalH1Iso X A hLC ≪≫
    (asIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)).symm

/-- The degree-one comparison composed with the homology map of the singular-cochain
sheafification unit is the constant-sheaf comparison isomorphism; this characterises it. -/
@[reassoc]
theorem h1Comparison_global (hLC : LocallyContractibleSpace X)
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)] :
    (h1Comparison X A hLC).hom ≫
        HomologicalComplex.homologyMap (globalCochainComparison X A) 1 =
      (constantSheafGlobalH1Iso X A hLC).hom := by
  let c := (constantSheafGlobalH1Iso X A hLC).hom
  let e := asIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)
  exact (Category.assoc c e.inv e.hom).trans
    ((congrArg (fun f => c ≫ f) e.inv_hom_id).trans (Category.comp_id c))

end TopCat.SingularCochainSheaf
