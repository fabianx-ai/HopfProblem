/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The Morse handle: the unit-disc model of an attaching region

The local model of a Morse handle: `UnitDisk N`/`UnitDisk P` for the negative and positive
directions, the model map and its basic properties, the belt-passage coordinates used to
trace flows through the handle, and the density of regular values.

## Main definitions and results

* `MorseHandle.UnitDisk`, `MorseHandle.modelMap`, `MorseHandle.modelMap_injective` :
  the unit-disc model.
* `BeltPassage.*` : belt-passage coordinates (`time`, `upper`, `lower`, `descentFlow`).
* `RegularValues.dense_regularValues` : regular values are dense.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §1–2 (handles)
* [Allen Hatcher, *Algebraic Topology*][hatcher02], §0

## Tags

Morse handle, belt passage, regular values
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

abbrev MorseHandle.UnitDisk (V : Type*) [NormedAddCommGroup V] :=
  Metric.closedBall (0 : V) 1

def MorseHandle.modelMap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : UnitDisk N × UnitDisk P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N), ρ • (z.2 : P))

theorem MorseHandle.continuous_modelMap {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) :
    Continuous (modelMap (N := N) (P := P) ρ) := by
  have hu : Continuous (fun z : UnitDisk N × UnitDisk P => (z.1 : N)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun z : UnitDisk N × UnitDisk P => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  exact
    ((continuous_const.mul
              (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))).smul
          hu).prodMk
      (continuous_const.smul hv)

theorem MorseHandle.negative_scale_pos {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    0 < ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
  mul_pos hρ (Real.sqrt_pos.mpr (by positivity))

theorem MorseHandle.modelMap_injective {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    Function.Injective (modelMap (N := N) (P := P) ρ) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : (v : P) = (v' : P) := by
    have hh := congrArg (fun z : N × P => ρ⁻¹ • z.2) h
    simpa only [modelMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hh
  have hv' : v = v' := Subtype.ext hv
  subst v'
  have hu : (u : N) = (u' : N) := by
    have hh := congrArg (fun z : N × P => (ρ * Real.sqrt (1 + ‖(v : P)‖ ^ 2))⁻¹ • z.1) h
    simpa only [modelMap, smul_smul, inv_mul_cancel₀ (negative_scale_pos hρ (u, v)).ne',
      one_smul] using hh
  exact Prod.ext (Subtype.ext hu) rfl

theorem MorseHandle.modelMap_mem_product {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hs : Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (negative_scale_pos hρ z)]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
        mul_le_of_le_one_right (negative_scale_pos hρ z).le hu
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hs hρ.le)
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • (z.2 : P)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

theorem MorseHandle.modelMap_height {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 =
      ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) := by
  simp only [modelMap, norm_smul, Real.norm_eq_abs, abs_of_pos (negative_scale_pos hρ z),
    abs_of_pos hρ, mul_pow, Real.sq_sqrt (show 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 by positivity)]
  ring

theorem MorseHandle.modelMap_lower_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ -(ρ ^ 2) ↔ ‖(z.1 : N)‖ = 1 := by
  rw [modelMap_height hρ z]
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hu₀ := norm_nonneg (z.1 : N)
  have hpos : 0 < ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2) := mul_pos (sq_pos_of_pos hρ) (by positivity)
  constructor
  · intro h
    have hp : (ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2)) * (1 - ‖(z.1 : N)‖ ^ 2) ≤ 0 := by
      calc
        _ = ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) + ρ ^ 2 := by ring
        _ ≤ 0 := by linarith
    have hm : 1 - ‖(z.1 : N)‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hpos).mp (by simpa only [MulZeroClass.mul_zero] using hp)
    nlinarith
  · intro h
    simp only [h, one_pow, sub_self, MulZeroClass.mul_zero, zero_sub, mul_neg, mul_one, le_refl]

theorem MorseHandle.modelMap_upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ ρ ^ 2 := by
  rw [modelMap_height hρ z]
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hu₂ : 0 ≤ ‖(z.1 : N)‖ ^ 2 := sq_nonneg _
  have hfactor : 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 := by positivity
  have hsmall : (1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1 ≤ 1 := by
    nlinarith [mul_nonneg hfactor hu₂]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (sq_nonneg ρ)

def MorseHandle.beltFaceScale (r : ℝ) : ℝ :=
  Real.sqrt (1 + r ^ 2) / Real.sqrt 2

theorem MorseHandle.beltFaceScale_pos (r : ℝ) : 0 < beltFaceScale r :=
  div_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by norm_num))

theorem MorseHandle.continuous_beltFaceScale : Continuous beltFaceScale :=
  (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).div_const _

theorem MorseHandle.beltFaceScale_one : beltFaceScale 1 = 1 := by
  simp only [beltFaceScale, one_pow, one_add_one_eq_two]
  exact div_self (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem MorseHandle.beltFaceScale_monotone : MonotoneOn beltFaceScale (Set.Ici 0) := by
  intro r hr s hs hrs
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg 2)
  apply Real.sqrt_le_sqrt
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs
  linarith

theorem MorseHandle.beltFaceRadius_strictMono :
    StrictMonoOn (fun r => beltFaceScale r * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  exact
    (mul_lt_mul_of_pos_left hrs (beltFaceScale_pos r)).trans_le
      (mul_le_mul_of_nonneg_right (beltFaceScale_monotone hr hs hrs.le) hs)

def MorseHandle.beltFaceMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (u : N) :
    N :=
  beltFaceScale ‖u‖ • u

theorem MorseHandle.continuous_beltFaceMap {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Continuous (beltFaceMap (N := N)) :=
  (continuous_beltFaceScale.comp continuous_norm).smul continuous_id

theorem MorseHandle.norm_beltFaceMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (u : N) : ‖beltFaceMap u‖ = beltFaceScale ‖u‖ * ‖u‖ := by
  rw [beltFaceMap, norm_smul, Real.norm_eq_abs, abs_of_pos (beltFaceScale_pos _)]

theorem MorseHandle.beltFaceMap_zero {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    beltFaceMap (0 : N) = 0 := by simp only [beltFaceMap, smul_zero]

theorem MorseHandle.norm_beltFaceMap_lt_one_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (u : N) : ‖beltFaceMap u‖ < 1 ↔ ‖u‖ < 1 := by
  have hh := beltFaceRadius_strictMono.lt_iff_lt (norm_nonneg u) (show 0 ≤ (1 : ℝ) by norm_num)
  simpa only [beltFaceScale_one, mul_one, norm_beltFaceMap] using hh

theorem MorseHandle.beltFaceMap_mem_disk {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {u : N} (hu : ‖u‖ ≤ 1) : ‖beltFaceMap u‖ ≤ 1 := by
  rw [norm_beltFaceMap]
  have hs : beltFaceScale ‖u‖ ≤ 1 := by
    rw [← beltFaceScale_one]
    exact beltFaceScale_monotone (norm_nonneg u) (by norm_num) hu
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg u)).trans (by simpa only [one_mul])

theorem MorseHandle.beltFaceMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Function.Injective (beltFaceMap (N := N)) := by
  intro u v huv
  have hn : ‖u‖ = ‖v‖ := by
    apply beltFaceRadius_strictMono.injOn (norm_nonneg u) (norm_nonneg v)
    simpa only [norm_beltFaceMap] using congrArg Norm.norm huv
  change beltFaceScale ‖u‖ • u = beltFaceScale ‖v‖ • v at huv
  rw [hn] at huv
  exact (smul_right_injective N (beltFaceScale_pos ‖v‖).ne') huv

theorem MorseHandle.beltFaceMap_surjOn_disk {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] :
    Set.SurjOn (beltFaceMap (N := N)) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro v hv
  by_cases hvzero : v = 0
  · subst v
    exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), beltFaceMap_zero⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvzero
  have hvrange : ‖v‖ ∈ Set.Icc (beltFaceScale 0 * 0) (beltFaceScale 1 * 1) := by
    simpa only [MulZeroClass.mul_zero, beltFaceScale_one, mul_one, Set.mem_Icc] using
      And.intro hvpos.le (mem_closedBall_zero_iff.mp hv)
  obtain ⟨r, hr, hrv⟩ :=
    intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num)
      (continuous_beltFaceScale.mul continuous_id).continuousOn hvrange
  change beltFaceScale r * r = ‖v‖ at hrv
  let u : N := (r / ‖v‖) • v
  have hnorm : ‖u‖ = r := by
    change ‖(r / ‖v‖) • v‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hvpos.le),
      div_mul_cancel₀ _ hvpos.ne']
  refine ⟨u, mem_closedBall_zero_iff.mpr (hnorm ▸ hr.2), ?_⟩
  change beltFaceScale ‖u‖ • ((r / ‖v‖) • v) = v
  rw [hnorm, smul_smul, ← mul_div_assoc, hrv, div_self hvpos.ne', one_smul]

def MorseHandle.beltFaceDiskMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    UnitDisk N → UnitDisk N := fun u =>
  ⟨beltFaceMap u.val,
    mem_closedBall_zero_iff.mpr (beltFaceMap_mem_disk (mem_closedBall_zero_iff.mp u.property))⟩

theorem MorseHandle.continuous_beltFaceDiskMap {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Continuous (beltFaceDiskMap (N := N)) :=
  (continuous_beltFaceMap.comp continuous_subtype_val).subtype_mk _

theorem MorseHandle.beltFaceDiskMap_bijective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Function.Bijective (beltFaceDiskMap (N := N)) := by
  constructor
  · intro u v huv
    exact Subtype.ext (beltFaceMap_injective (congrArg Subtype.val huv))
  · intro v
    obtain ⟨u, hu, huv⟩ := beltFaceMap_surjOn_disk v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

def MorseHandle.beltFaceDiskHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] : UnitDisk N ≃ₜ UnitDisk N :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective beltFaceDiskMap beltFaceDiskMap_bijective) continuous_beltFaceDiskMap

def MorseHandle.ambientMap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖z.2‖ ^ 2)) • z.1, ρ • z.2)

def MorseHandle.ambientInverse {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2))⁻¹ • z.1, ρ⁻¹ • z.2)

theorem MorseHandle.ambientInverse_ambientMap {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientInverse ρ (ambientMap ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul,
      inv_mul_cancel₀ hscale.ne']
  · simp only [ambientInverse, ambientMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

theorem MorseHandle.ambientMap_ambientInverse {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientMap ρ (ambientInverse ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]

def MorseHandle.ambientHomeomorph {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (hρ : 0 < ρ) : (N × P) ≃ₜ (N × P) := by
  have hscale (v : P) : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  refine
    { toFun := ambientMap ρ
      invFun := ambientInverse ρ
      left_inv := ambientInverse_ambientMap hρ
      right_inv := ambientMap_ambientInverse hρ
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact
      ((continuous_const.mul
                (Real.continuous_sqrt.comp
                  (continuous_const.add (continuous_snd.norm.pow 2)))).smul
            continuous_fst).prodMk
        (continuous_const.smul continuous_snd)
  · have hv : Continuous (fun z : N × P => ρ⁻¹ • z.2) := continuous_const.smul continuous_snd
    have hc : Continuous (fun z : N × P => ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))
    exact ((hc.inv₀ (fun z => (hscale (ρ⁻¹ • z.2)).ne')).smul continuous_fst).prodMk hv

@[simp]
theorem MorseHandle.ambientHomeomorph_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (hρ : 0 < ρ) :
    ambientHomeomorph (N := N) (P := P) ρ hρ 0 = 0 := by
  change ambientMap ρ (0 : N × P) = 0
  simp only [ambientMap, Prod.fst_zero, Prod.snd_zero, smul_zero, Prod.mk_zero_zero]

theorem MorseHandle.range_modelMap_mem_nhds_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    Set.range (modelMap (N := N) (P := P) ρ) ∈ 𝓝 (0 : N × P) := by
  let e := ambientHomeomorph (N := N) (P := P) ρ hρ
  let O := Metric.ball (0 : N) 1 ×ˢ Metric.ball (0 : P) 1
  have hO : IsOpen (e '' O) := e.isOpenMap O (Metric.isOpen_ball.prod Metric.isOpen_ball)
  have hzero : (0 : N × P) ∈ e '' O := by
    refine ⟨0, ?_, ambientHomeomorph_zero ρ hρ⟩
    exact ⟨by simp, by simp⟩
  have hsub : e '' O ⊆ Set.range (modelMap (N := N) (P := P) ρ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact
      ⟨(⟨z.1, Metric.ball_subset_closedBall hz.1⟩, ⟨z.2, Metric.ball_subset_closedBall hz.2⟩),
        rfl⟩
  exact Filter.mem_of_superset (hO.mem_nhds hzero) hsub

theorem MorseHandle.inverse_scale_sq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {ρ : ℝ} (hρ : 0 < ρ) (v : P) : (ρ * Real.sqrt (1 + ‖ρ⁻¹ • v‖ ^ 2)) ^ 2 = ρ ^ 2 + ‖v‖ ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hρ)]
  field_simp

theorem MorseHandle.mem_range_modelMap_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ Set.range (modelMap ρ) ↔ ‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  let A := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hneg : ‖A⁻¹ • z.1‖ ≤ 1 ↔ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), inv_mul_le_one₀ hA, ←
      sq_le_sq₀ (norm_nonneg z.1) hA.le, hA₂]
    constructor <;> intro h <;> linarith
  have hpos : ‖ρ⁻¹ • z.2‖ ≤ 1 ↔ ‖z.2‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_le_one₀ hρ]
  constructor
  · rintro ⟨w, hw⟩
    have hi : ambientInverse ρ z = ((w.1 : N), (w.2 : P)) := by
      rw [← hw]
      exact ambientInverse_ambientMap hρ ((w.1 : N), (w.2 : P))
    have h₁ : A⁻¹ • z.1 = (w.1 : N) := congrArg Prod.fst hi
    have h₂ : ρ⁻¹ • z.2 = (w.2 : P) := congrArg Prod.snd hi
    exact
      ⟨hpos.mp (by rw [h₂]; exact mem_closedBall_zero_iff.mp w.2.2),
        hneg.mp (by rw [h₁]; exact mem_closedBall_zero_iff.mp w.1.2)⟩
  · intro hz
    refine
      ⟨(⟨A⁻¹ • z.1, mem_closedBall_zero_iff.mpr (hneg.mpr hz.2)⟩,
          ⟨ρ⁻¹ • z.2, mem_closedBall_zero_iff.mpr (hpos.mpr hz.1)⟩),
        ?_⟩
    exact ambientMap_ambientInverse hρ z

def MorseHandle.quadratic {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : N × P) : ℝ :=
  -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

def MorseHandle.descent {N P : Type*} [NormedAddCommGroup P] (z : N × P) : N × P :=
  (z.1, -z.2)

theorem MorseHandle.contDiff_descent {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] :
    ContDiff ℝ ∞ (descent (N := N) (P := P)) :=
  contDiff_fst.prodMk contDiff_snd.neg

theorem MorseHandle.fderiv_quadratic_descent {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] (z : N × P) :
    fderiv ℝ quadratic z (descent z) = -2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
  have hd :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).norm_sq.neg.add
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq
  have hd' := hd.fderiv
  change fderiv ℝ quadratic z = _ at hd'
  rw [hd']
  simp only [descent, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply,
    inner_neg_right, real_inner_self_eq_norm_sq, two_smul]
  ring

theorem MorseHandle.fderiv_quadratic_descent_neg {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] {z : N × P}
    (hz : z ≠ 0) : fderiv ℝ quadratic z (descent z) < 0 := by
  rw [fderiv_quadratic_descent]
  have hsum : 0 < ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    by_contra! h
    have hu : ‖z.1‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    have hv : ‖z.2‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    exact hz (Prod.ext (norm_eq_zero.mp hu) (norm_eq_zero.mp hv))
  nlinarith

def MorseHandle.descentFlow {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Flow ℝ (N × P)
    where
  toFun t z := (Real.exp t • z.1, Real.exp (-t) • z.2)
  cont' :=
    ((Real.continuous_exp.comp continuous_fst).smul continuous_snd.fst).prodMk
      ((Real.continuous_exp.comp continuous_fst.neg).smul continuous_snd.snd)
  map_add' s t z := by simp only [Real.exp_add, neg_add, smul_smul]
  map_zero' z := by simp

theorem MorseHandle.hasDerivAt_descentFlow {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (z : N × P) (t : ℝ) :
    HasDerivAt (fun s => descentFlow s z) (descent (descentFlow t z)) t := by
  have h₁ := (Real.hasDerivAt_exp t).smul_const z.1
  have h₂ := ((hasDerivAt_id t).neg.exp).smul_const z.2
  simpa only [descentFlow, descent, id_eq, Pi.neg_apply, mul_neg, mul_one, neg_smul] using
    h₁.prodMk h₂

theorem MorseHandle.norm_descentFlow_fst {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).1‖ = Real.exp t * ‖z.1‖ := by
  change ‖Real.exp t • z.1‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem MorseHandle.norm_descentFlow_snd {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).2‖ = Real.exp (-t) * ‖z.2‖ := by
  change ‖Real.exp (-t) • z.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t))]

theorem MorseHandle.norm_fst_le_descentFlow {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖z.1‖ ≤ ‖(descentFlow t z).1‖ := by
  rw [norm_descentFlow_fst]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr ht)

theorem MorseHandle.norm_snd_descentFlow_le {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖(descentFlow t z).2‖ ≤ ‖z.2‖ := by
  rw [norm_descentFlow_snd]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

theorem MorseHandle.mem_lower_union_handle_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ) ↔
      quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ := by
  rw [Set.mem_union, Set.mem_ofPred_eq, mem_range_modelMap_iff hρ]
  change quadratic z ≤ -(ρ ^ 2) ∨ (‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ quadratic z) ↔ _
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.1
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hq : quadratic z ≤ -(ρ ^ 2)
      · exact Or.inl hq
      · exact Or.inr ⟨h, le_of_not_ge hq⟩

def MorseHandle.beltFaceTime (r : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + r ^ 2))

theorem MorseHandle.beltFaceTime_nonneg (r : ℝ) : 0 ≤ beltFaceTime r :=
  Real.log_nonneg (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg r]))

theorem MorseHandle.exp_beltFaceTime (r : ℝ) :
    Real.exp (beltFaceTime r) = Real.sqrt (1 + r ^ 2) :=
  Real.exp_log (Real.sqrt_pos.mpr (by positivity))

def MorseHandle.beltLevelModel {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) : N × P :=
  (ρ • u, (ρ * Real.sqrt (1 + ‖u‖ ^ 2)) • v)

theorem MorseHandle.beltLevelModel_height {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (u : N)
    {v : P} (hv : ‖v‖ = 1) : quadratic (beltLevelModel ρ u v) = ρ ^ 2 := by
  have hs : 0 < Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [quadratic, beltLevelModel, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
    abs_of_pos (mul_pos hρ hs), hv, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity)]
  ring

theorem MorseHandle.descentFlow_beltFaceTime {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : UnitDisk N)
    (v : UnitDisk P) (hv : ‖v.val‖ = 1) :
    descentFlow (beltFaceTime ‖u.val‖) (beltLevelModel ρ u.val v.val) =
      modelMap ρ (beltFaceDiskMap u, v) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hu : Real.sqrt (1 + ‖u.val‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change
      Real.exp (beltFaceTime ‖u.val‖) • (ρ • u.val) =
        (ρ * Real.sqrt (1 + ‖v.val‖ ^ 2)) • (beltFaceScale ‖u.val‖ • u.val)
    rw [exp_beltFaceTime, hv, one_pow, one_add_one_eq_two, smul_smul, smul_smul]
    congr 1
    unfold beltFaceScale
    field_simp
  · change
      Real.exp (-beltFaceTime ‖u.val‖) • ((ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v.val) = ρ • v.val
    rw [Real.exp_neg, exp_beltFaceTime, smul_smul]
    congr 1
    field_simp

theorem MorseHandle.descentFlow_beltLevelModel_mem_block {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (u : UnitDisk N) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (beltFaceTime ‖u.val‖)) :
    descentFlow t (beltLevelModel ρ u.val v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hu : ‖u.val‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
  have hspos : 0 < Real.sqrt (1 + ‖u.val‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (1 + ‖u.val‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg u.val]⟩
  have he : Real.exp t ≤ Real.sqrt (1 + ‖u.val‖ ^ 2) := by
    rw [← exp_beltFaceTime]
    exact Real.exp_le_exp.mpr ht.2
  have hen : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
  constructor
  · rw [mem_closedBall_zero_iff, norm_descentFlow_fst]
    change Real.exp t * ‖ρ • u.val‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      _ ≤ Real.exp t * ρ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hρ.le hu) (Real.exp_pos t).le
      _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (he.trans hs) hρ.le
  · rw [mem_closedBall_zero_iff, norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hspos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖u.val‖ ^ 2) := mul_le_of_le_one_left (mul_pos hρ hspos).le hen
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hs hρ.le)
      _ = 2 * ρ := mul_comm _ _

theorem MorseHandle.descentFlow_neg_beltFaceTime {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : UnitDisk N)
    (v : UnitDisk P) (hv : ‖v.val‖ = 1) :
    descentFlow (-beltFaceTime ‖u.val‖) (modelMap ρ (beltFaceDiskMap u, v)) =
      beltLevelModel ρ u.val v.val := by
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add, neg_add_cancel,
    descentFlow.map_zero_apply]

theorem MorseHandle.descentFlow_positiveFace_mem_block {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : UnitDisk N) (v : UnitDisk P) (hv : ‖v.val‖ = 1) {t : ℝ}
    (ht : t ∈ Set.uIcc 0 (-beltFaceTime ‖u.val‖)) :
    descentFlow t (modelMap ρ (beltFaceDiskMap u, v)) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  rw [Set.uIcc_of_ge (neg_nonpos.mpr (beltFaceTime_nonneg ‖u.val‖))] at ht
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add]
  apply descentFlow_beltLevelModel_mem_block hρ u hv
  constructor <;> linarith [ht.1, ht.2]

def BeltPassage.time (s : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + s ^ 2) / s)

theorem BeltPassage.time_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ time s := by
  have hroot := Real.sqrt_nonneg (1 + s ^ 2)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  apply Real.log_nonneg
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem BeltPassage.exp_time {s : ℝ} (hs : 0 < s) :
    Real.exp (time s) = Real.sqrt (1 + s ^ 2) / s :=
  Real.exp_log (div_pos (Real.sqrt_pos.mpr (by positivity)) hs)

def BeltPassage.upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * s) • u, (ρ * Real.sqrt (1 + s ^ 2)) • v)

def BeltPassage.lower {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * Real.sqrt (1 + s ^ 2)) • u, (ρ * s) • v)

theorem BeltPassage.descentFlow_time {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) {s : ℝ} (hs : 0 < s) (u : N) (v : P) :
    MorseHandle.descentFlow (time s) (BeltPassage.upper ρ s u v) =
      BeltPassage.lower ρ s u v := by
  have hr : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change Real.exp (time s) • ((ρ * s) • u) = (ρ * Real.sqrt (1 + s ^ 2)) • u
    rw [exp_time hs, smul_smul]
    congr 1
    field_simp
  · change Real.exp (-time s) • ((ρ * Real.sqrt (1 + s ^ 2)) • v) = (ρ * s) • v
    rw [Real.exp_neg, exp_time hs, smul_smul]
    congr 1
    field_simp

theorem BeltPassage.descentFlow_mem_block {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hs₁ : s ≤ 1) {u : N} (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (time s)) :
    MorseHandle.descentFlow t (BeltPassage.upper ρ s u v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hpos : 0 ≤ ρ * s := (mul_pos hρ hs).le
  constructor
  · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
    change Real.exp t * ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hu, mul_one]
    calc
      _ ≤ Real.exp (time s) * (ρ * s) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) hpos
      _ = ρ * Real.sqrt (1 + s ^ 2) := by rw [exp_time hs]; field_simp
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hr hρ.le)
      _ = 2 * ρ := mul_comm _ _
  · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + s ^ 2) :=
        mul_le_of_le_one_left (mul_pos hρ hrpos).le
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1))
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hr hρ.le)
      _ = 2 * ρ := mul_comm _ _

theorem BeltPassage.contDiff_lower {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    ContDiff ℝ ∞ (fun s => BeltPassage.lower ρ s u v) :=
  ((contDiff_const.mul
            ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun _ => by positivity))).smul
        contDiff_const).prodMk
    ((contDiff_const.mul contDiff_id).smul contDiff_const)

theorem BeltPassage.lower_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    BeltPassage.lower ρ 0 u v = (ρ • u, 0) := by
  simp only [BeltPassage.lower, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one,
    mul_one, MulZeroClass.mul_zero, zero_smul]

theorem BeltPassage.upper_neg {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) :
    BeltPassage.upper ρ (-s) u v = BeltPassage.upper ρ s (-u) v := by
  simp only [BeltPassage.upper, neg_sq, mul_neg, neg_smul, smul_neg]

theorem BeltPassage.upper_height {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) {u : N} (hu : ‖u‖ = 1) {v : P}
    (hv : ‖v‖ = 1) : MorseHandle.quadratic (BeltPassage.upper ρ s u v) = ρ ^ 2 := by
  simp only [MorseHandle.quadratic, BeltPassage.upper, norm_smul, Real.norm_eq_abs,
    hu, hv, mul_one, sq_abs, mul_pow, Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]
  ring

theorem BeltPassage.contDiff_upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    ContDiff ℝ ∞ (fun s => BeltPassage.upper ρ s u v) :=
  ((contDiff_const.mul contDiff_id).smul contDiff_const).prodMk
    ((contDiff_const.mul
          ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun _ => by positivity))).smul
      contDiff_const)

theorem BeltPassage.upper_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    BeltPassage.upper ρ 0 u v = (0, ρ • v) := by
  simp only [BeltPassage.upper, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one,
    mul_one, MulZeroClass.mul_zero, zero_smul]

theorem BeltPassage.upper_mem_block {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| ≤ 1) {u : N}
    (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) :
    BeltPassage.upper ρ s u v ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_abs s, abs_nonneg s]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_mul, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hs hρ.le
    linarith
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    exact (mul_le_mul_of_nonneg_left hr hρ.le).trans_eq (mul_comm _ _)

def RegularValues.singularPoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) : Set E :=
  {x | (fderiv ℝ f x).det = 0}

def RegularValues.regularValues {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) : Set E :=
  (f '' singularPoints f)ᶜ

theorem RegularValues.mem_regularValues_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) (y : E) :
    y ∈ regularValues f ↔ ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  constructor
  · intro hy x hx hdet
    exact hy ⟨x, hdet, hx⟩
  · intro hy ⟨x, hx, hxy⟩
    exact hy x hxy hx

theorem RegularValues.bijective_iff_det_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    Function.Bijective A ↔ A.det ≠ 0 := by
  constructor
  · intro h hdet
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet) (LinearMap.ker_eq_bot.mpr h.1)
  · intro hdet
    have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hn
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
    have hi := LinearMap.ker_eq_bot.mp hker
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem RegularValues.bijective_fderiv_of_mem_regularValues {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {y : E}
    (hy : y ∈ regularValues f) {x : E} (hx : f x = y) : Function.Bijective (fderiv ℝ f x) := by
  have hdet := (mem_regularValues_iff f y).mp hy x hx
  exact (bijective_iff_det_ne_zero _).mpr hdet

theorem RegularValues.measure_singularValues_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    (hf : Differentiable ℝ f) : μ (f '' singularPoints f) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)

theorem RegularValues.dense_regularValues {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    (hf : Differentiable ℝ f) : Dense (regularValues f) := by
  have he : ∀ᵐ y ∂μ, y ∉ f '' singularPoints f := by
    rw [MeasureTheory.ae_iff]
    have hs : {y : E | ¬y ∉ f '' singularPoints f} = f '' singularPoints f := by
      ext y
      simp
    rw [hs]
    exact measure_singularValues_eq_zero μ hf
  exact μ.dense_of_ae he
end Mathoverflow1973
