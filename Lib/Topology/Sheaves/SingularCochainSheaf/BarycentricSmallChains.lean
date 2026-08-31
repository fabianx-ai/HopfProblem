/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitH1Criterion

/-! # Barycentric discharge of the global-unit small-chain input -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- Barycentric subdivision supplies the cover-small chain equivalences required by the global
singular-cochain sheafification-unit comparison. -/
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
