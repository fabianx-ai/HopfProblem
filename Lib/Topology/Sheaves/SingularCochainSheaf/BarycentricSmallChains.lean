/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitPredicates

/-!
# Chains small with respect to an open cover

Barycentric subdivision makes singular chains small with respect to a given open cover: the
inclusion of the subcomplex of cover-small chains into the singular chain complex is a homotopy
equivalence (Hatcher, *Algebraic Topology*, Prop. 2.21).  This module records that fact in the
form used by the comparison between constant-sheaf and singular cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- For every open cover of `X` the inclusion of the cover-small singular chains is a homotopy
equivalence onto the singular chain complex (Hatcher, Prop. 2.21). -/
theorem hasSmallChainEquivalences_barycentric (X : TopCat.{0}) :
    HasSmallChainEquivalences X := by
  intro U hxU
  have hcover : (⋃ x : X, (U x : Set X)) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  refine ⟨TopCat.SingularSmallChains.Barycentric.smallChainHomotopyEquiv
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen) hcover, ?_⟩
  rfl

end TopCat.SingularCochainSheaf
