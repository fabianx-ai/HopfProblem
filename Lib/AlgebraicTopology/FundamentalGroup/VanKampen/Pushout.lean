/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar, Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.PathValue
public import Lib.GroupTheory.Pushout.EquivOfCocone

/-!
# The fundamental group of a two-open cover as a group pushout

This module packages the two-open-cover universal property as a `Monoid.PushoutI` equivalence. It
contains no proof-specific cover or relator data.
-/

@[expose] public noncomputable section

open Set Function Topology
open scoped ContinuousMap Interval

/-- The fundamental group of the chart `i` at the chart base point. -/
abbrev FundamentalGroup.VanKampen.Cocone.TwoOpenCover.ChartGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) :=
  FundamentalGroup (D.chart i) (D.baseChart i)

/-- The homomorphism from the overlap group into the chart group `i`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

/-- The chart homomorphism into the ambient fundamental group. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.inclusionHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

/-- Both routes from the overlap to the ambient group coincide. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.inclusionHom_comp_overlapHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) = D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

/-- The amalgamated pushout of the two chart groups over the overlap. -/
abbrev FundamentalGroup.VanKampen.Cocone.TwoOpenCover.Pushout {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :=
  Monoid.PushoutI D.overlapHom

/-- The Seifert-van Kampen isomorphism: the fundamental group of `U ∪ V` is the pushout of
`pi_1 U` and `pi_1 V` over `pi_1 (U ∩ V)` (Hatcher, Algebraic Topology, Theorem 1.20). -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutEquiv {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) : D.Pushout ≃* FundamentalGroup X D.base := by
  let ofU : D.UGroup →* D.Pushout :=
    Monoid.PushoutI.of (φ := D.overlapHom) Bool.false
  let ofV : D.VGroup →* D.Pushout :=
    Monoid.PushoutI.of (φ := D.overlapHom) Bool.true
  have compatible : D.Compatible ofU ofV :=
    (Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.false).trans
      (Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.true).symm
  let back : FundamentalGroup X D.base →* D.Pushout := D.lift ofU ofV compatible
  exact Monoid.PushoutI.equivOfCocone
    D.inclusionHom
    (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom
    back
    (fun i ↦ by
      cases i
      · exact D.lift_comp_inclusionU ofU ofV compatible
      · exact D.lift_comp_inclusionV ofU ofV compatible)
    (fun a b h ↦ D.hom_ext a b (h Bool.false) (h Bool.true))

/-- The pushout equivalence computes the inclusion on generators. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutEquiv_of {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g := by
  simp [pushoutEquiv]

/-- The inverse of the pushout equivalence sends a chart loop to its pushout generator. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutEquiv_symm_inclusionHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutEquiv.symm (D.inclusionHom i g) = Monoid.PushoutI.of i g := by
  simp [pushoutEquiv]

/-! ### The two comparison maps and the uniqueness half -/

/-- The `U` chart map into the pushout. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutOfU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) : D.UGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.false

/-- The `V` chart map into the pushout. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutOfV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) : D.VGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.true

/-- The overlap map into the pushout. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutBase {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) : D.OverlapGroup →* D.Pushout :=
  Monoid.PushoutI.base D.overlapHom

/-- The `U` pushout map factors through the overlap. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutOfU_comp_overlapHomU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.pushoutOfU.comp D.overlapHomU = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.false

/-- The `V` pushout map factors through the overlap. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutOfV_comp_overlapHomV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.pushoutOfV.comp D.overlapHomV = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.true

/-- The pushout maps are compatible on the overlap. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutOf_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.Compatible D.pushoutOfU D.pushoutOfV :=
  D.pushoutOfU_comp_overlapHomU.trans D.pushoutOfV_comp_overlapHomV.symm

/-- The map from the pushout of `pi_1 U` and `pi_1 V` over `pi_1 (U ∩ V)` to `pi_1 (U ∪ V)`
induced by the inclusions (Hatcher, Algebraic Topology, Theorem 1.20). -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.Pushout →* FundamentalGroup X D.base :=
  Monoid.PushoutI.lift D.inclusionHom (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom

/-- The pushout-to-group map computes the inclusion on generators. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutToFundamentalGroup (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  Monoid.PushoutI.lift_of _ _ _ g

/-- The pushout map composed with a chart inclusion is the chart homomorphism. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup_comp_of
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (i : Bool) :
    D.pushoutToFundamentalGroup.comp (Monoid.PushoutI.of i) = D.inclusionHom i := by
  ext g
  exact D.pushoutToFundamentalGroup_of i g

/-- The pushout map restricts to the `U` homomorphism. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup_comp_ofU
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_of Bool.false

/-- The pushout map restricts to the `V` homomorphism. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup_comp_ofV
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_of Bool.true

/-- The map from `pi_1 (U ∪ V)` to the pushout induced by sending a loop to its subdivided
product of local loops (the uniqueness half of van Kampen). -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroupToPushout {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    FundamentalGroup X D.base →* D.Pushout :=
  D.lift D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The lift to the pushout restricts to the `U` pushout map. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionU
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomU = D.pushoutOfU :=
  D.lift_comp_inclusionU D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The lift to the pushout restricts to the `V` pushout map. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionV
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomV = D.pushoutOfV :=
  D.lift_comp_inclusionV D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The two comparison maps compose to the identity on the pushout. -/
theorem
  FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup = MonoidHom.id D.Pushout := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfU =
        (MonoidHom.id D.Pushout).comp D.pushoutOfU
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofU,
      D.fundamentalGroupToPushout_comp_inclusionU, MonoidHom.id_comp]
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfV =
        (MonoidHom.id D.Pushout).comp D.pushoutOfV
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofV,
      D.fundamentalGroupToPushout_comp_inclusionV, MonoidHom.id_comp]

/-- The two comparison maps compose to the identity on the fundamental group. -/
theorem
  FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.fundamentalGroupToPushout =
      MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionU,
      D.pushoutToFundamentalGroup_comp_ofU, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionV,
      D.pushoutToFundamentalGroup_comp_ofV, MonoidHom.id_comp]
