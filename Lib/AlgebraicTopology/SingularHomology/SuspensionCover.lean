/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.FundamentalGroup.VanKampen
import Lib.AlgebraicTopology.SingularHomology.SphereHomology

/-!
# The canonical two-open cover of a suspension

`SphereHomology.suspensionConeCover X x` is the `FundamentalGroup.VanKampen.TwoOpenCover`
of the unreduced suspension `Suspension X` by its north and south cones, with the middle
band as intersection. It is the cover used for van Kampen and Mayer–Vietoris arguments
on suspensions (sphere homology, suspension simply-connectedness).

This file is not a Lean `module` because `FundamentalGroup/VanKampen.lean` is not one yet;
it converts when its dependencies do.
-/

noncomputable section

/-- The canonical two-open cover of a suspension by its north and south cones; the
intersection is the middle band, which deformation retracts onto `X`. -/
def SphereHomology.suspensionConeCover (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) : FundamentalGroup.VanKampen.TwoOpenCover (Suspension X)
    where
  U := ⟨Suspension.northOpen, Suspension.northOpen_isOpen⟩
  V := ⟨Suspension.southOpen, Suspension.southOpen_isOpen⟩
  cover := Suspension.open_cover
  pathConnectedU := by
    change
      IsPathConnected
        (Suspension.northOpen : Set (Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedV := by
    change
      IsPathConnected
        (Suspension.southOpen : Set (Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := by
    change IsPathConnected (Suspension.middleBand X)
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  base := Suspension.mk ⟨1 / 2, by norm_num⟩ x
  baseU := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  baseV := by
    change (1 / 4 : ℝ) < 1 / 2
    norm_num

end
