/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Homotopy.LocallyContractible

/-! # Nullhomotopic inclusions of open neighborhoods -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory TopologicalSpace Topology

namespace TopCat

universe u

/-- In a locally contractible space, every point of an open set has a smaller open neighborhood
whose inclusion into the original open set is nullhomotopic. -/
theorem exists_open_nullhomotopic_inclusion (X : TopCat.{u})
    (hLC : LocallyContractibleSpace X) (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic (((Opens.toTopCat X).map (homOfLE hVU)).hom) := by
  obtain ⟨N, hNU, hN, hnull⟩ := hLC x (U : Set X) (U.isOpen.mem_nhds hx)
  obtain ⟨V, hVN, hV, hxV⟩ := mem_nhds_iff.mp hN
  let W : Opens X := ⟨V, hV⟩
  have hWU : W ≤ U := hVN.trans hNU
  refine ⟨W, hWU, hxV, ?_⟩
  exact hnull.comp_left (ContinuousMap.inclusion hVN)

end TopCat
