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

abbrev FundamentalGroup.VanKampen.TwoOpenCover.ChartGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :=
  FundamentalGroup (D.chart i) (D.baseChart i)

def FundamentalGroup.VanKampen.TwoOpenCover.overlapHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_comp_overlapHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) = D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

abbrev FundamentalGroup.VanKampen.TwoOpenCover.Pushout {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  Monoid.PushoutI D.overlapHom

def FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.Pushout ≃* FundamentalGroup X D.base := by
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

@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_of {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g := by
  simp [pushoutEquiv]

@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_symm_inclusionHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutEquiv.symm (D.inclusionHom i g) = Monoid.PushoutI.of i g := by
  simp [pushoutEquiv]
