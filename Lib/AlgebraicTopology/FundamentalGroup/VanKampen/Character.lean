/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Surjectivity

/-!
# Character-valued lifts for two-open van Kampen covers

This is the character-valued universal-property wrapper needed by finite attachment arguments.
Basepoint transport remains owned by `VanKampen.Surjectivity`; this module intentionally introduces
no competing rebasing API.
-/

@[expose] public noncomputable section

open Function Topology

namespace FundamentalGroup.VanKampen.TwoOpenCover

/-- Lift compatible chart characters to the fundamental group of a two-open union. -/
def characterLift {X G : Type*} [TopologicalSpace X] [Group G]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hcompat : D.Compatible fU fV) :
    FundamentalGroup X D.base →* G :=
  D.lift fU fV hcompat

/-- The lifted character restricts to the left-chart character. -/
theorem characterLift_comp_inclusionHomU {X G : Type*} [TopologicalSpace X] [Group G]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hcompat : D.Compatible fU fV) :
    (D.characterLift fU fV hcompat).comp D.inclusionHomU = fU :=
  D.lift_comp_inclusionU fU fV hcompat

/-- The lifted character restricts to the right-chart character. -/
theorem characterLift_comp_inclusionHomV {X G : Type*} [TopologicalSpace X] [Group G]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hcompat : D.Compatible fU fV) :
    (D.characterLift fU fV hcompat).comp D.inclusionHomV = fV :=
  D.lift_comp_inclusionV fU fV hcompat

/-- A lift is surjective when its left-chart character is surjective. -/
theorem characterLift_surjective_of_left {X G : Type*} [TopologicalSpace X] [Group G]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hcompat : D.Compatible fU fV) (hsurj : Function.Surjective fU) :
    Function.Surjective (D.characterLift fU fV hcompat) := by
  intro g
  obtain ⟨u, hu⟩ := hsurj g
  exact ⟨D.inclusionHomU u,
    (DFunLike.congr_fun (D.characterLift_comp_inclusionHomU fU fV hcompat) u).trans hu⟩

end FundamentalGroup.VanKampen.TwoOpenCover
