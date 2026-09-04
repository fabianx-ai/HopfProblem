/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import Lib.Topology.Homotopy.PuncturedCyclicCover
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The fundamental group of the punctured complex plane is cyclic

The proof uses the existing two-simply-connected-open van Kampen interface.
It is deliberately formulated as a range theorem, which is the form needed
for local monodromy calculations.

The construction is generic textbook topology: it contains no application cover, local system,
or paper-specific monodromy assertion.
-/

@[expose] public noncomputable section

set_option warningAsError true
set_option autoImplicit false

open Set Function TopologicalSpace Topology
open scoped ComplexConjugate

namespace Mathoverflow1973.PuncturedPlaneCyclic

/-- The complex plane with the origin removed. -/
def planeOpen : Opens ℂ := ⟨{z | z ≠ 0}, isOpen_ne⟩

abbrev Plane := planeOpen

instance plane_pathConnectedSpace : PathConnectedSpace Plane :=
  (unitsHomeomorphNeZero (G₀ := ℂ)).surjective.pathConnectedSpace
    (unitsHomeomorphNeZero (G₀ := ℂ)).continuous

/-- A slit plane missing the downward imaginary half-axis. -/
def upperSet : Set ℂ := {z | 0 < z.im ∨ z.re ≠ 0}

/-- A slit plane missing the upward imaginary half-axis. -/
def lowerSet : Set ℂ := {z | z.im < 0 ∨ z.re ≠ 0}

theorem upperSet_isOpen : IsOpen upperSet :=
  (isOpen_lt continuous_const Complex.continuous_im).union
    (isOpen_ne_fun Complex.continuous_re continuous_const)

theorem lowerSet_isOpen : IsOpen lowerSet :=
  (isOpen_lt Complex.continuous_im continuous_const).union
    (isOpen_ne_fun Complex.continuous_re continuous_const)

theorem upperSet_subset_punctured : upperSet ⊆ {z : ℂ | z ≠ 0} := by
  intro z hz
  rintro rfl
  simp [upperSet] at hz

theorem lowerSet_subset_punctured : lowerSet ⊆ {z : ℂ | z ≠ 0} := by
  intro z hz
  rintro rfl
  simp [lowerSet] at hz

theorem slitSets_union : upperSet ∪ lowerSet = {z : ℂ | z ≠ 0} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact upperSet_subset_punctured hz
    · exact lowerSet_subset_punctured hz
  · intro hz
    by_cases hp : 0 < z.im
    · exact Or.inl (Or.inl hp)
    by_cases hn : z.im < 0
    · exact Or.inr (Or.inl hn)
    have hi : z.im = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    apply Or.inl
    apply Or.inr
    intro hr
    apply hz
    apply Complex.ext <;> simp_all

theorem slitSets_inter : upperSet ∩ lowerSet = {z : ℂ | z.re ≠ 0} := by
  ext z
  constructor
  · rintro ⟨hp | hx, hn | hx'⟩
    · linarith
    · exact hx'
    · exact hx
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, Or.inr hx⟩

def upperBasepoint : upperSet := ⟨Complex.I, Or.inl (by simp)⟩

def upperHeightMap : C(upperSet, upperSet) where
  toFun z := ⟨(z.val.re : ℂ) + Complex.I, Or.inl (by simp)⟩
  continuous_toFun := by fun_prop

theorem upper_vertical_mem (t : unitInterval) (z : upperSet) :
    (z.val.re : ℂ) + (((1 - t.val) * z.val.im + t.val : ℝ) : ℂ) * Complex.I ∈ upperSet := by
  simp only [upperSet, Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, MulZeroClass.mul_zero, add_zero,
    zero_add, Complex.add_re, Complex.mul_re, sub_zero]
  rcases z.property with hz | hz
  · left
    by_cases ht : t.val = 1
    · simp [ht]
    · have hp : 0 < 1 - t.val :=
        sub_pos.mpr ((lt_or_eq_of_le t.property.2).resolve_right ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hp hz) t.property.1
  · exact Or.inr hz

def upperVerticalHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id upperSet) upperHeightMap where
  toFun p :=
    ⟨(p.2.val.re : ℂ) +
        (((1 - p.1.val) * p.2.val.im + p.1.val : ℝ) : ℂ) * Complex.I,
      upper_vertical_mem p.1 p.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    simp
  map_one_left z := by
    apply Subtype.ext
    simp [upperHeightMap]

def upperHorizontalHomotopy :
    ContinuousMap.Homotopy upperHeightMap
      (ContinuousMap.const upperSet upperBasepoint) where
  toFun p :=
    ⟨(((1 - p.1.val) * p.2.val.re : ℝ) : ℂ) + Complex.I, Or.inl (by simp)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    simp [upperHeightMap]
  map_one_left z := by
    apply Subtype.ext
    simp [upperBasepoint]

def upperContraction :
    ContinuousMap.Homotopy (ContinuousMap.id upperSet)
      (ContinuousMap.const upperSet upperBasepoint) :=
  upperVerticalHomotopy.trans upperHorizontalHomotopy

instance upperSet_contractibleSpace : ContractibleSpace upperSet :=
  (contractible_iff_id_nullhomotopic upperSet).mpr
    ⟨upperBasepoint, ⟨upperContraction⟩⟩

def slitConjugation : upperSet ≃ₜ lowerSet where
  toFun z := ⟨conj (z : ℂ), by simpa [upperSet, lowerSet] using z.property⟩
  invFun z := ⟨conj (z : ℂ), by simpa [upperSet, lowerSet] using z.property⟩
  left_inv z := Subtype.ext (Complex.conj_conj _)
  right_inv z := Subtype.ext (Complex.conj_conj _)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance lowerSet_contractibleSpace : ContractibleSpace lowerSet :=
  slitConjugation.symm.contractibleSpace

def upperSlit : Opens Plane :=
  ⟨{z | (z : ℂ) ∈ upperSet}, upperSet_isOpen.preimage continuous_subtype_val⟩

def lowerSlit : Opens Plane :=
  ⟨{z | (z : ℂ) ∈ lowerSet}, lowerSet_isOpen.preimage continuous_subtype_val⟩

theorem upperSlit_union_lowerSlit :
    (upperSlit : Set Plane) ∪ lowerSlit = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hz : (z : ℂ) ∈ ({w : ℂ | w ≠ 0}) := z.property
  rw [← slitSets_union] at hz
  exact hz

def upperSlitHomeomorph : upperSlit ≃ₜ upperSet where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, upperSet_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def lowerSlitHomeomorph : lowerSlit ≃ₜ lowerSet where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, lowerSet_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance upperSlit_contractibleSpace : ContractibleSpace upperSlit :=
  upperSlitHomeomorph.contractibleSpace

instance lowerSlit_contractibleSpace : ContractibleSpace lowerSlit :=
  lowerSlitHomeomorph.contractibleSpace

theorem upperSlit_simplyConnected : SimplyConnectedSpace upperSlit := inferInstance

theorem lowerSlit_simplyConnected : SimplyConnectedSpace lowerSlit := inferInstance

/-- The positive real base point. -/
def base : Plane := ⟨(1 / 2 : ℂ), by norm_num [planeOpen]⟩

/-- A point in the other component of the slit overlap. -/
def opposite : Plane := ⟨(-1 / 2 : ℂ), by norm_num [planeOpen]⟩

theorem base_mem_upper : base ∈ upperSlit := by norm_num [base, upperSlit, upperSet]

theorem base_mem_lower : base ∈ lowerSlit := by norm_num [base, lowerSlit, lowerSet]

theorem opposite_mem_upper : opposite ∈ upperSlit := by
  norm_num [opposite, upperSlit, upperSet]

theorem opposite_mem_lower : opposite ∈ lowerSlit := by
  norm_num [opposite, lowerSlit, lowerSet]

def slitCover : FundamentalGroup.VanKampen.TwoSimplyConnectedCover Plane where
  U := upperSlit
  V := lowerSlit
  cover := upperSlit_union_lowerSlit
  simplyU := upperSlit_simplyConnected
  simplyV := lowerSlit_simplyConnected
  base := base
  baseU := base_mem_upper
  baseV := base_mem_lower

def positiveOverlap : Set Plane := {z | 0 < (z : ℂ).re}

def negativeOverlap : Set Plane := {z | (z : ℂ).re < 0}

def positiveOverlapHomeomorph : positiveOverlap ≃ₜ {z : ℂ // 0 < z.re} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z :=
    ⟨⟨z.1, by
        intro h
        have hz := z.2
        rw [h] at hz
        norm_num at hz⟩,
      z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def negativeOverlapHomeomorph : negativeOverlap ≃ₜ {z : ℂ // z.re < 0} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z :=
    ⟨⟨z.1, by
        intro h
        have hz := z.2
        rw [h] at hz
        norm_num at hz⟩,
      z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem positiveOverlap_isPathConnected : IsPathConnected positiveOverlap := by
  have hamb : IsPathConnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPathConnected ⟨1, by norm_num⟩
  let _ : PathConnectedSpace {z : ℂ // 0 < z.re} :=
    isPathConnected_iff_pathConnectedSpace.mp hamb
  let _ : PathConnectedSpace positiveOverlap :=
    positiveOverlapHomeomorph.symm.surjective.pathConnectedSpace
      positiveOverlapHomeomorph.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem negativeOverlap_isPathConnected : IsPathConnected negativeOverlap := by
  have hamb : IsPathConnected {z : ℂ | z.re < 0} :=
    (convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by norm_num⟩
  let _ : PathConnectedSpace {z : ℂ // z.re < 0} :=
    isPathConnected_iff_pathConnectedSpace.mp hamb
  let _ : PathConnectedSpace negativeOverlap :=
    negativeOverlapHomeomorph.symm.surjective.pathConnectedSpace
      negativeOverlapHomeomorph.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem positiveOverlap_subset_slitOverlap :
    positiveOverlap ⊆ (upperSlit : Set Plane) ∩ lowerSlit := by
  intro z hz
  exact ⟨Or.inr hz.ne', Or.inr hz.ne'⟩

theorem negativeOverlap_subset_slitOverlap :
    negativeOverlap ⊆ (upperSlit : Set Plane) ∩ lowerSlit := by
  intro z hz
  exact ⟨Or.inr hz.ne, Or.inr hz.ne⟩

theorem overlap_has_two_components
    (y : Plane) (hyU : y ∈ slitCover.U) (hyV : y ∈ slitCover.V) :
    JoinedIn ((slitCover.U : Set Plane) ∩ slitCover.V) slitCover.base y ∨
      JoinedIn ((slitCover.U : Set Plane) ∩ slitCover.V) opposite y := by
  have hre : (y : ℂ).re ≠ 0 := by
    have h : (y : ℂ) ∈ upperSet ∩ lowerSet := ⟨hyU, hyV⟩
    rw [slitSets_inter] at h
    exact h
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · apply Or.inr
    exact
      (negativeOverlap_isPathConnected.joinedIn opposite (by norm_num [negativeOverlap, opposite])
          y hneg).mono negativeOverlap_subset_slitOverlap
  · apply Or.inl
    exact
      (positiveOverlap_isPathConnected.joinedIn base (by norm_num [positiveOverlap, base])
          y hpos).mono positiveOverlap_subset_slitOverlap

def meridianHalfCircle (t : ℝ) : ℂ :=
  circleMap 0 (1 / 2) (Real.pi * t)

theorem continuous_meridianHalfCircle : Continuous meridianHalfCircle := by
  unfold meridianHalfCircle circleMap
  fun_prop

@[simp]
theorem meridianHalfCircle_zero : meridianHalfCircle 0 = (1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap]

@[simp]
theorem meridianHalfCircle_one : meridianHalfCircle 1 = (-1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap, Complex.exp_pi_mul_I]
  ring

theorem meridianHalfCircle_im_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (meridianHalfCircle t).im := by
  rw [meridianHalfCircle, circleMap_zero_im]
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0) (by nlinarith [Real.pi_pos])

theorem meridianHalfCircle_mem_upperSet (t : unitInterval) : meridianHalfCircle t ∈ upperSet := by
  by_cases ht0 : (t : ℝ) = 0
  · rw [ht0, meridianHalfCircle_zero]
    norm_num [upperSet]
  by_cases ht1 : (t : ℝ) = 1
  · rw [ht1, meridianHalfCircle_one]
    norm_num [upperSet]
  apply Or.inl
  apply meridianHalfCircle_im_pos
  · exact lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  · exact lt_of_le_of_ne t.property.2 ht1

theorem conj_meridianHalfCircle_mem_lowerSet (t : unitInterval) :
    conj (meridianHalfCircle t) ∈ lowerSet := by
  simpa [upperSet, lowerSet] using meridianHalfCircle_mem_upperSet t

/-- The upper semicircle from the positive to the negative base point. -/
def upperPath : Path base opposite where
  toFun t :=
    ⟨meridianHalfCircle t, upperSet_subset_punctured (meridianHalfCircle_mem_upperSet t)⟩
  continuous_toFun :=
    (continuous_meridianHalfCircle.comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (by simp [base])
  target' := Subtype.ext (by simp [opposite])

/-- The lower semicircle from the positive to the negative base point. -/
def lowerPath : Path base opposite where
  toFun t :=
    ⟨conj (meridianHalfCircle t),
      lowerSet_subset_punctured (conj_meridianHalfCircle_mem_lowerSet t)⟩
  continuous_toFun :=
    (Complex.continuous_conj.comp
      (continuous_meridianHalfCircle.comp continuous_subtype_val)).subtype_mk _
  source' := Subtype.ext (by simp [base, map_ofNat])
  target' := Subtype.ext (by simp [opposite, map_ofNat])

theorem upperPath_mem (t : unitInterval) : upperPath t ∈ upperSlit :=
  meridianHalfCircle_mem_upperSet t

theorem lowerPath_mem (t : unitInterval) : lowerPath t ∈ lowerSlit :=
  conj_meridianHalfCircle_mem_lowerSet t

/-- The standard positive meridian in the punctured plane. -/
def meridian : Path base base := upperPath.trans lowerPath.symm

/-- The standard meridian generates the entire punctured-plane fundamental group. -/
theorem zpowers_meridian_eq_top :
    Subgroup.zpowers
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian)) = ⊤ := by
  have hswitch :
      slitCover.switchClass opposite opposite_mem_upper opposite_mem_lower =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian) :=
    slitCover.switchClass_eq_of_paths opposite_mem_upper opposite_mem_lower
      upperPath lowerPath upperPath_mem lowerPath_mem
  rw [← hswitch]
  exact
    slitCover.zpowers_switchClass_eq_top opposite opposite_mem_upper opposite_mem_lower
      overlap_has_two_components

/-- The image of any homomorphism out of the punctured-plane fundamental group is generated by
the image of the standard meridian. -/
theorem range_eq_zpowers_meridian {G : Type*} [Group G]
    (φ : FundamentalGroup Plane base →* G) :
    φ.range = Subgroup.zpowers
      (φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian))) := by
  rw [MonoidHom.range_eq_map, ← zpowers_meridian_eq_top, MonoidHom.map_zpowers]

/-! ## Positive-radius punctured balls -/

/-- The standard radial homeomorphism from the complex plane to a positive-radius open ball. -/
def ballHomeomorph (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ Metric.ball (0 : ℂ) r :=
  Homeomorph.unitBall.trans
    (OpenPartialHomeomorph.unitBallBall (0 : ℂ) r hr).toHomeomorphSourceTarget

@[simp]
theorem ballHomeomorph_apply_zero (r : ℝ) (hr : 0 < r) :
    (ballHomeomorph r hr 0 : ℂ) = 0 := by
  change r • ((Homeomorph.unitBall (0 : ℂ) : Metric.ball (0 : ℂ) 1) : ℂ) + 0 = 0
  rw [Homeomorph.coe_unitBall_apply_zero]
  simp

abbrev PuncturedBall (r : ℝ) := {z : Metric.ball (0 : ℂ) r // (z.1 : ℂ) ≠ 0}

/-- Radial compactification identifies the punctured plane with every positive-radius punctured
ball, preserving the origin before it is removed. -/
def puncturedBallHomeomorph (r : ℝ) (hr : 0 < r) : Plane ≃ₜ PuncturedBall r := by
  apply (ballHomeomorph r hr).subtype
  intro z
  change z ≠ 0 ↔ ((ballHomeomorph r hr z : Metric.ball (0 : ℂ) r) : ℂ) ≠ 0
  constructor
  · intro hz he
    have he' : ballHomeomorph r hr z = ballHomeomorph r hr 0 := by
      apply Subtype.ext
      rw [he, ballHomeomorph_apply_zero]
    exact hz ((ballHomeomorph r hr).injective he')
  · intro hz rfl
    exact hz (ballHomeomorph_apply_zero r hr)

/-- Every positive-radius punctured complex ball is path connected. -/
theorem puncturedBall_pathConnectedSpace (r : ℝ) (hr : 0 < r) :
    PathConnectedSpace (PuncturedBall r) :=
  (puncturedBallHomeomorph r hr).surjective.pathConnectedSpace
    (puncturedBallHomeomorph r hr).continuous

/-- Fundamental-group transport along `puncturedBallHomeomorph`. -/
def puncturedBallFundamentalGroupEquiv (r : ℝ) (hr : 0 < r) :
    FundamentalGroup Plane base ≃*
      FundamentalGroup (PuncturedBall r) (puncturedBallHomeomorph r hr base) :=
  FundamentalGroup.mulEquivOfHomotopyEquiv
    (puncturedBallHomeomorph r hr).toHomotopyEquiv base

/-- The canonical meridian class in a positive-radius punctured ball. -/
def puncturedBallMeridianClass (r : ℝ) (hr : 0 < r) :
    FundamentalGroup (PuncturedBall r) (puncturedBallHomeomorph r hr base) :=
  puncturedBallFundamentalGroupEquiv r hr
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian))

/-- Every monodromy image from a positive-radius punctured ball is generated by its canonical
meridian. -/
theorem puncturedBall_range_eq_zpowers_meridian
    {G : Type*} [Group G] (r : ℝ) (hr : 0 < r)
    (φ : FundamentalGroup (PuncturedBall r) (puncturedBallHomeomorph r hr base) →* G) :
    φ.range = Subgroup.zpowers (φ (puncturedBallMeridianClass r hr)) := by
  let e := puncturedBallFundamentalGroupEquiv r hr
  have h := range_eq_zpowers_meridian (φ.comp e.toMonoidHom)
  rw [MonoidHom.range_comp] at h
  have he : e.toMonoidHom.range = ⊤ := e.range_eq_top
  rw [he, ← MonoidHom.range_eq_map] at h
  let m : FundamentalGroup Plane base :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian)
  have heval : e.toMonoidHom m = e m := rfl
  change φ.range = Subgroup.zpowers (φ (e m))
  rw [← heval]
  exact h

/-- The image of a homomorphism from a positive-radius punctured ball, at any base point, is
cyclic. -/
theorem puncturedBall_exists_cyclic_range
    {G : Type*} [Group G] (r : ℝ) (hr : 0 < r) (x : PuncturedBall r)
    (φ : FundamentalGroup (PuncturedBall r) x →* G) :
    ∃ a : G, φ.range = Subgroup.zpowers a := by
  let _ : PathConnectedSpace (PuncturedBall r) := puncturedBall_pathConnectedSpace r hr
  let c := puncturedBallHomeomorph r hr base
  let τ : Path c x := PathConnectedSpace.somePath c x
  let e : FundamentalGroup (PuncturedBall r) c ≃* FundamentalGroup (PuncturedBall r) x :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath τ
  have h := puncturedBall_range_eq_zpowers_meridian r hr (φ.comp e.toMonoidHom)
  refine ⟨φ (e (puncturedBallMeridianClass r hr)), ?_⟩
  rw [MonoidHom.range_comp] at h
  have he : e.toMonoidHom.range = ⊤ := e.range_eq_top
  rw [he, ← MonoidHom.range_eq_map] at h
  simpa using h

end Mathoverflow1973.PuncturedPlaneCyclic
