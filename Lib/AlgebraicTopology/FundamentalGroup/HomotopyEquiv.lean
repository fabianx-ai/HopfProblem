/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Fundamental groups and homotopy equivalences

A homotopy equivalence induces a multiplicative equivalence between the fundamental groups at
corresponding base points.  This is the vertex-group consequence of the induced equivalence of
fundamental groupoids.
-/

@[expose] public noncomputable section

set_option warningAsError true
set_option autoImplicit false

open scoped ContinuousMap

namespace FundamentalGroup

/-- The fundamental-group map induced by a homotopy equivalence is bijective. -/
theorem map_bijective_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact E.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)

/-- The multiplicative equivalence of fundamental groups induced by a homotopy equivalence. -/
def mulEquivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x) (map_bijective_of_homotopyEquiv e x)

end FundamentalGroup
