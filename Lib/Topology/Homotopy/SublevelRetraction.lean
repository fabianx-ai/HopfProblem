/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

abbrev SublevelRetraction.Positive {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) :=
  { x : X // 0 < ρ x }

abbrev SublevelRetraction.Sublevel {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (δ : ℝ) :=
  { x : X // ρ x < δ }

def SublevelRetraction.extensionFun {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (s : (unitInterval) × X) : X :=
  by classical exact if hx : 0 < ρ s.2 then (H (s.1, ⟨s.2, hx⟩)).val else s.2

theorem SublevelRetraction.extensionFun_apply_of_pos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ))
    (s : (unitInterval) × X) (hs : 0 < ρ s.2) : extensionFun ρ H s = (H (s.1, ⟨s.2, hs⟩)).val := by
  classical simp only [extensionFun, dif_pos hs]

theorem SublevelRetraction.extensionFun_apply_of_nonpos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ))
    (s : (unitInterval) × X) (hs : ρ s.2 ≤ 0) : extensionFun ρ H s = s.2 := by
  classical simp only [extensionFun, dif_neg (not_lt_of_ge hs)]

theorem SublevelRetraction.extensionFun_apply_of_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 < η) : extensionFun ρ H s = s.2 := by
  by_cases hp : 0 < ρ s.2
  · rw [extensionFun_apply_of_pos ρ H s hp, hfix s.1 ⟨s.2, hp⟩ hs]
  · exact extensionFun_apply_of_nonpos ρ H s (le_of_not_gt hp)

theorem SublevelRetraction.extensionFun_continuousOn_positive {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) :
    ContinuousOn (extensionFun ρ H) {s : (unitInterval) × X | 0 < ρ s.2} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hpair :
    Continuous
      (fun s : { s : (unitInterval) × X // 0 < ρ s.2 } =>
        (s.val.1, (⟨s.val.2, s.property⟩ : Positive ρ))) :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  exact
    (continuous_subtype_val.comp (H.continuous.comp hpair)).congr
      (fun s => (extensionFun_apply_of_pos ρ H s.val s.property).symm)

theorem SublevelRetraction.extensionFun_continuousOn_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    ContinuousOn (extensionFun ρ H) {s : (unitInterval) × X | ρ s.2 < η} :=
  continuous_snd.continuousOn.congr (fun s hs => extensionFun_apply_of_small ρ H η hfix s hs)

theorem SublevelRetraction.extensionFun_continuous {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    Continuous (extensionFun ρ H) := by
  have hρ : Continuous (fun s : (unitInterval) × X => ρ s.2) := ρ.continuous.comp continuous_snd
  have hopen : IsOpen {s : (unitInterval) × X | 0 < ρ s.2} := isOpen_lt continuous_const hρ
  have hsmall : IsOpen {s : (unitInterval) × X | ρ s.2 < η} := isOpen_lt hρ continuous_const
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : 0 < ρ s.2
  · exact (extensionFun_continuousOn_positive ρ H).continuousAt (hopen.mem_nhds hs)
  · exact
      (extensionFun_continuousOn_small ρ H η hfix).continuousAt
        (hsmall.mem_nhds ((le_of_not_gt hs).trans_lt hη))

def SublevelRetraction.extension {X : Type*} [TopologicalSpace X] (ρ : C(X, ℝ))
    (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    C((unitInterval) × X, X) :=
  ⟨extensionFun ρ H, extensionFun_continuous ρ H η hη hfix⟩

theorem SublevelRetraction.extension_apply_of_pos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : 0 < ρ s.2) :
    extension ρ H η hη hfix s = (H (s.1, ⟨s.2, hs⟩)).val :=
  extensionFun_apply_of_pos ρ H s hs

theorem SublevelRetraction.extension_apply_of_nonpos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 ≤ 0) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_nonpos ρ H s hs

theorem SublevelRetraction.extension_apply_of_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 < η) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_small ρ H η hfix s hs

theorem SublevelRetraction.extension_zero {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x) (x : X) : extension ρ H η hη hfix (0, x) = x := by
  by_cases hx : 0 < ρ x
  · exact
      (extension_apply_of_pos ρ H η hη hfix (0, x) hx).trans
        (congrArg Subtype.val (hzero ⟨x, hx⟩))
  · exact extension_apply_of_nonpos ρ H η hη hfix (0, x) (le_of_not_gt hx)

theorem SublevelRetraction.extension_radius_le {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (s : unitInterval × X) : ρ (extension ρ H η hη hfix s) ≤ ρ s.2 := by
  by_cases hs : 0 < ρ s.2
  · rw [extension_apply_of_pos ρ H η hη hfix s hs]
    exact hmono s.1 ⟨s.2, hs⟩
  · exact (congrArg ρ (extension_apply_of_nonpos ρ H η hη hfix s (le_of_not_gt hs))).le

theorem SublevelRetraction.extension_one_lt {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : X) :
    ρ (extension ρ H η hη hfix (1, x)) < δ := by
  by_cases hx : 0 < ρ x
  · rw [extension_apply_of_pos ρ H η hη hfix (1, x) hx]
    exact hone ⟨x, hx⟩
  · rw [extension_apply_of_nonpos ρ H η hη hfix (1, x) (le_of_not_gt hx)]
    exact (le_of_not_gt hx).trans_lt (hη.trans_le hηδ)

theorem SublevelRetraction.extension_stays_sublevel {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (s : unitInterval × Sublevel ρ δ) : ρ (extension ρ H η hη hfix (s.1, s.2.val)) < δ :=
  (extension_radius_le ρ H η hη hfix hmono (s.1, s.2.val)).trans_lt s.2.property

def SublevelRetraction.sublevelInclusion {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (δ : ℝ) : C(Sublevel ρ δ, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def SublevelRetraction.sublevelMap {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : C(X, Sublevel ρ δ)
    where
  toFun x := ⟨extension ρ H η hη hfix (1, x), extension_one_lt ρ H η hη hfix δ hηδ hone x⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk
      _

def SublevelRetraction.extendedHomotopy {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x) (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id X).HomotopyRel
      ((sublevelInclusion ρ δ).comp (sublevelMap ρ H η hη hfix δ hηδ hone)) {x : X | ρ x < η}
    where
  toFun := extension ρ H η hη hfix
  continuous_toFun := (extension ρ H η hη hfix).continuous
  map_zero_left := extension_zero ρ H η hη hfix hzero
  map_one_left _ := rfl
  prop' t x hx := extension_apply_of_small ρ H η hη hfix (t, x) hx

def SublevelRetraction.restrictedHomotopy {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id (Sublevel ρ δ)).HomotopyRel
      ((sublevelMap ρ H η hη hfix δ hηδ hone).comp (sublevelInclusion ρ δ))
      {x : Sublevel ρ δ | ρ x.val < η}
    where
  toFun
    s :=
    ⟨extension ρ H η hη hfix (s.1, s.2.val), extension_stays_sublevel ρ H η hη hfix hmono δ s⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    exact extension_zero ρ H η hη hfix hzero x.val
  map_one_left _ := rfl
  prop' t x
    hx := by
    apply Subtype.ext
    exact extension_apply_of_small ρ H η hη hfix (t, x.val) hx

def SublevelRetraction.sublevelHomotopyEquiv {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : X ≃ₕ Sublevel ρ δ
    where
  toFun := sublevelMap ρ H η hη hfix δ hηδ hone
  invFun := sublevelInclusion ρ δ
  left_inv := ⟨(extendedHomotopy ρ H η hη hfix hzero δ hηδ hone).toHomotopy.symm⟩
  right_inv := ⟨(restrictedHomotopy ρ H η hη hfix hzero hmono δ hηδ hone).toHomotopy.symm⟩
end Mathoverflow1973
