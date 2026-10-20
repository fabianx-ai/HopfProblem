/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.RealizationSupport
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.SubdivisionHomotopy

/-! # Carrier preservation for the native subdivision homotopy -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set

namespace TopCat.SingularSmallChains.Barycentric

variable {X : Type} [TopologicalSpace X] {I : Type}

/-- The explicit native subdivision homotopy preserves cover-small chains for every family of
subsets. -/
theorem subdivisionHomotopy_mem_small (U : I → Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ TopCat.SingularSmallChains.submodule U n) :
    subdivisionHomotopy X k n c ∈ TopCat.SingularSmallChains.submodule U (n + 1) := by
  apply singularLinearMap_mem_of_small U n (subdivisionHomotopy X k n)
    (TopCat.SingularSmallChains.submodule U (n + 1)) c hc
  intro sigma hsigma
  rw [subdivisionHomotopy_simplex]
  exact realizedChain_mem_small U n (n + 1) sigma hsigma _

end TopCat.SingularSmallChains.Barycentric
