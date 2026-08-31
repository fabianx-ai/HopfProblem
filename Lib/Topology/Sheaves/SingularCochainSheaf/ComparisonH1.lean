/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnit

/-!
# The degree-one constant-sheaf/singular comparison assembly

This module isolates the final categorical assembly.  Local exactness and degree-zero acyclicity
produce the comparison with global sheafified cochains; an `IsIso` instance for the actual global
sheafification-unit homology map then produces the native singular-cohomology comparison.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The canonical degree-one comparison, assembled from the actual resolution and actual global
sheafification-unit map. -/
def h1Comparison (hLC : LocallyContractibleSpace X)
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (TopCat.ConstantSheaf.sheaf X A) 1) ≅
      (AlgebraicTopology.SingularCochains.complex X A).homology 1 :=
  constantSheafGlobalH1Iso X A hLC ≪≫
    (asIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)).symm

/-- The comparison is characterized by the actual global sheafification-unit homology map. -/
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
