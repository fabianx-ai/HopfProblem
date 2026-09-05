/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.Vanishing
public import Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonPositive

/-!
# Vanishing across the positive constant-sheaf comparison

On a locally contractible metrizable space, the canonical positive-degree comparison identifies
Ext-defined constant-sheaf cohomology with native singular cohomology.  This FREE owner records
the resulting equivalence of vanishing statements.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- Ext-defined constant-sheaf cohomology in degree `n+1` vanishes exactly when the corresponding
native singular cohomology group vanishes. -/
theorem constantSheafCohomology_subsingleton_iff_singular
    (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (hLC : LocallyContractibleSpace X) [MetrizableSpace X] (n : ℕ) :
    Subsingleton
        (CategoryTheory.Sheaf.H.{0} (TopCat.ConstantSheaf.sheaf X A) (n + 1)) ↔
      Subsingleton
        ((AlgebraicTopology.SingularCochains.complex X A).homology (n + 1)) := by
  let E := constantSheafCohomologyIsoSingular X A hLC n
  constructor
  · intro h
    let _ : Subsingleton
        (CategoryTheory.Sheaf.H.{0} (TopCat.ConstantSheaf.sheaf X A) (n + 1)) := h
    exact ((ConcreteCategory.isIso_iff_bijective E.inv).mp (by infer_instance)).1.subsingleton
  · intro h
    let _ : Subsingleton
        ((AlgebraicTopology.SingularCochains.complex X A).homology (n + 1)) := h
    exact ((ConcreteCategory.isIso_iff_bijective E.hom).mp (by infer_instance)).1.subsingleton

/-- On a contractible, locally contractible metrizable space, every positive-degree
constant-sheaf cohomology group vanishes. -/
theorem constantSheafCohomology_succ_subsingleton_of_contractible
    (X : TopCat.{0}) (A : AddCommGrpCat.{0}) [ContractibleSpace X]
    (hLC : LocallyContractibleSpace X) [MetrizableSpace X] (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H.{0} (TopCat.ConstantSheaf.sheaf X A) (n + 1)) := by
  apply (constantSheafCohomology_subsingleton_iff_singular X A hLC n).mpr
  exact AlgebraicTopology.SingularCochains.contractibleCohomology_subsingleton
    X A (n + 1) (by omega)

end TopCat.SingularCochainSheaf
