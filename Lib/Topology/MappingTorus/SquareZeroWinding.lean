/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.LinearAlgebra.SquareZero
public import Lib.Topology.MappingTorus.TranslationCocycle
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Integral windings for square-zero mapping tori

A lattice-preserving square-zero endomorphism `N` and an integral vector `v` determine the
corrected winding

`a(t) = t • v - (t * (t - 1) / 2) • N v`.

Its integral deck defect makes it a translation cocycle on the quotient mapping torus. A separate
primitive integral detector proves faithfulness of the resulting integer shear family.
-/

@[expose] public section

open Set Function

noncomputable section

namespace Mathoverflow1973.MappingTorus.SquareZeroWinding

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Square-zero real-linear data preserving an integral lattice, with a chosen winding vector. -/
structure Data (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  lattice : Submodule ℤ V
  nilpotent : V →L[ℝ] V
  nilpotent_sq : nilpotent.toLinearMap * nilpotent.toLinearMap = 0
  nilpotent_mem : ∀ {x : V}, x ∈ lattice → nilpotent x ∈ lattice
  vector : V
  vector_mem : vector ∈ lattice

namespace Data

/-- The linear square-zero flow `1 + kN` at an integer parameter. -/
def linearEquiv (D : Data V) (k : ℤ) : V ≃ₗ[ℝ] V :=
  Module.End.oneAddSMulEquiv D.nilpotent.toLinearMap D.nilpotent_sq (k : ℝ)

@[simp]
theorem linearEquiv_apply (D : Data V) (k : ℤ) (x : V) :
    D.linearEquiv k x = x + (k : ℝ) • D.nilpotent x := by
  rw [linearEquiv, Module.End.oneAddSMulEquiv_apply, Module.End.oneAddSMul_apply]
  rfl

theorem linearEquiv_continuous (D : Data V) (k : ℤ) :
    Continuous (D.linearEquiv k) := by
  change Continuous (fun x : V ↦ x + (k : ℝ) • D.nilpotent x)
  fun_prop

theorem linearEquiv_symm_apply (D : Data V) (k : ℤ) (x : V) :
    (D.linearEquiv k).symm x = x + ((-k : ℤ) : ℝ) • D.nilpotent x := by
  change Module.End.oneAddSMul D.nilpotent.toLinearMap (-((k : ℤ) : ℝ)) x = _
  rw [Module.End.oneAddSMul_apply, Int.cast_neg]
  rfl

theorem linearEquiv_symm_continuous (D : Data V) (k : ℤ) :
    Continuous (D.linearEquiv k).symm := by
  have h : Continuous (fun x : V ↦ x + ((-k : ℤ) : ℝ) • D.nilpotent x) := by
    fun_prop
  convert h using 1
  funext x
  exact D.linearEquiv_symm_apply k x

theorem linearEquiv_mem_lattice (D : Data V) (k : ℤ) {x : V}
    (hx : x ∈ D.lattice) : D.linearEquiv k x ∈ D.lattice := by
  rw [D.linearEquiv_apply]
  apply D.lattice.add_mem hx
  rw [Int.cast_smul_eq_zsmul]
  exact D.lattice.smul_mem k (D.nilpotent_mem hx)

theorem linearEquiv_symm_mem_lattice (D : Data V) (k : ℤ) {x : V}
    (hx : x ∈ D.lattice) : (D.linearEquiv k).symm x ∈ D.lattice := by
  rw [D.linearEquiv_symm_apply]
  apply D.lattice.add_mem hx
  rw [Int.cast_smul_eq_zsmul]
  exact D.lattice.smul_mem (-k) (D.nilpotent_mem hx)

theorem linearEquiv_map_lattice (D : Data V) (k : ℤ) :
    D.lattice.map ((D.linearEquiv k).restrictScalars ℤ).toLinearMap = D.lattice := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact D.linearEquiv_mem_lattice k hy
  · intro hx
    refine ⟨(D.linearEquiv k).symm x, D.linearEquiv_symm_mem_lattice k hx, ?_⟩
    exact (D.linearEquiv k).apply_symm_apply x

/-- The additive quotient torus associated to the lattice. -/
abbrev Torus (D : Data V) :=
  V ⧸ D.lattice

/-- The square-zero flow induced on the quotient torus. -/
def torusLinearEquiv (D : Data V) (k : ℤ) : D.Torus ≃ₗ[ℤ] D.Torus :=
  Submodule.Quotient.equiv D.lattice D.lattice ((D.linearEquiv k).restrictScalars ℤ)
    (D.linearEquiv_map_lattice k)

/-- The additive quotient flow, bundled with its quotient-induced topology. -/
def torusContinuousAddEquiv (D : Data V) (k : ℤ) : D.Torus ≃ₜ+ D.Torus where
  __ := (D.torusLinearEquiv k).toAddEquiv
  continuous_toFun := by
    apply D.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact D.lattice.continuous_mkQ.comp (D.linearEquiv_continuous k)
  continuous_invFun := by
    apply D.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact D.lattice.continuous_mkQ.comp (D.linearEquiv_symm_continuous k)

@[simp]
theorem torusContinuousAddEquiv_mkQ (D : Data V) (k : ℤ) (x : V) :
    D.torusContinuousAddEquiv k (D.lattice.mkQ x) = D.lattice.mkQ (D.linearEquiv k x) :=
  rfl

@[simp]
theorem linearEquiv_zero_apply (D : Data V) (x : V) : D.linearEquiv 0 x = x := by
  simp [D.linearEquiv_apply]

@[simp]
theorem torusContinuousAddEquiv_zero_apply (D : Data V) (x : D.Torus) :
    D.torusContinuousAddEquiv 0 x = x := by
  obtain ⟨y, rfl⟩ := D.lattice.mkQ_surjective x
  rw [D.torusContinuousAddEquiv_mkQ, D.linearEquiv_zero_apply]

theorem linearEquiv_add_apply (D : Data V) (k l : ℤ) (x : V) :
    D.linearEquiv (k + l) x = D.linearEquiv k (D.linearEquiv l x) := by
  simpa [linearEquiv, Int.cast_add, Module.End.mul_apply] using
    DFunLike.congr_fun
      (Module.End.oneAddSMul_mul_oneAddSMul D.nilpotent_sq (k : ℝ) (l : ℝ)).symm x

theorem torusContinuousAddEquiv_add_apply (D : Data V) (k l : ℤ) (x : D.Torus) :
    D.torusContinuousAddEquiv (k + l) x =
      D.torusContinuousAddEquiv k (D.torusContinuousAddEquiv l x) := by
  obtain ⟨y, rfl⟩ := D.lattice.mkQ_surjective x
  rw [D.torusContinuousAddEquiv_mkQ, D.torusContinuousAddEquiv_mkQ,
    D.torusContinuousAddEquiv_mkQ, D.linearEquiv_add_apply]

/-- Monodromy is the unit-time additive quotient flow. -/
def monodromy (D : Data V) : D.Torus ≃ₜ+ D.Torus :=
  D.torusContinuousAddEquiv 1

theorem monodromy_zpow (D : Data V) (k : ℤ) :
    D.monodromy.toHomeomorph ^ k = (D.torusContinuousAddEquiv k).toHomeomorph := by
  let monodromyHom : Multiplicative ℤ →* (D.Torus ≃ₜ D.Torus) :=
    { toFun := fun j ↦ (D.torusContinuousAddEquiv j.toAdd).toHomeomorph
      map_one' := by
        apply Homeomorph.ext
        exact D.torusContinuousAddEquiv_zero_apply
      map_mul' := by
        intro m n
        apply Homeomorph.ext
        exact D.torusContinuousAddEquiv_add_apply m.toAdd n.toAdd }
  have h := map_zpow monodromyHom (Multiplicative.ofAdd (1 : ℤ)) k
  change (D.torusContinuousAddEquiv (((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd)).toHomeomorph =
    D.monodromy.toHomeomorph ^ k at h
  simpa using h.symm

/-- The square-zero corrected lift of the chosen integral vector. -/
def windingLift (D : Data V) (t : ℝ) : V :=
  t • D.vector - (t * (t - 1) / 2) • D.nilpotent D.vector

theorem windingLift_continuous (D : Data V) : Continuous D.windingLift := by
  unfold windingLift
  fun_prop

@[simp]
theorem windingLift_zero (D : Data V) : D.windingLift 0 = 0 := by
  simp [windingLift]

@[simp]
theorem windingLift_one (D : Data V) : D.windingLift 1 = D.vector := by
  simp [windingLift]

/-- The corrected winding has an explicitly integral defect under every deck translation. -/
theorem windingLift_add_int_sub_linearEquiv_neg (D : Data V) (t : ℝ) (n : ℤ) :
    D.windingLift (t + (n : ℝ)) - D.linearEquiv (-n) (D.windingLift t) =
      (n : ℝ) • D.vector -
        ((n * (n - 1) / 2 : ℤ) : ℝ) • D.nilpotent D.vector := by
  have castHalf :
      ((n * (n - 1) / 2 : ℤ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have consecutiveEven : Even (n * (n - 1)) := by
      rcases Int.even_or_odd n with hn | hn
      · exact hn.mul_right _
      · exact (hn.sub_odd odd_one).mul_left n
    have hdiv : (2 : ℤ) ∣ n * (n - 1) := even_iff_two_dvd.mp consecutiveEven
    rw [Int.cast_div_charZero hdiv]
    push_cast
    ring
  have nilpotentVector : D.nilpotent (D.nilpotent D.vector) = 0 := by
    simpa [Module.End.mul_apply] using DFunLike.congr_fun D.nilpotent_sq D.vector
  rw [D.linearEquiv_apply, castHalf]
  unfold windingLift
  simp only [map_sub, map_smul, nilpotentVector, smul_zero, sub_zero, Int.cast_neg]
  module

theorem windingLift_defect_mem_lattice (D : Data V) (t : ℝ) (n : ℤ) :
    D.windingLift (t + (n : ℝ)) - D.linearEquiv (-n) (D.windingLift t) ∈ D.lattice := by
  rw [D.windingLift_add_int_sub_linearEquiv_neg]
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact D.lattice.sub_mem (D.lattice.smul_mem n D.vector_mem)
    (D.lattice.smul_mem (n * (n - 1) / 2) (D.nilpotent_mem D.vector_mem))

/-- The winding path in the quotient torus. -/
def windingShift (D : Data V) (t : ℝ) : D.Torus :=
  D.lattice.mkQ (D.windingLift t)

theorem windingShift_continuous (D : Data V) : Continuous D.windingShift :=
  D.lattice.continuous_mkQ.comp D.windingLift_continuous

/-- Quotient equivariance of the corrected winding. -/
theorem windingShift_add_int (D : Data V) (t : ℝ) (n : ℤ) :
    D.windingShift (t + (n : ℝ)) =
      (D.monodromy.toHomeomorph ^ (-n)) (D.windingShift t) := by
  change D.lattice.mkQ (D.windingLift (t + (n : ℝ))) =
    (D.monodromy.toHomeomorph ^ (-n)) (D.lattice.mkQ (D.windingLift t))
  rw [D.monodromy_zpow]
  change D.lattice.mkQ (D.windingLift (t + (n : ℝ))) =
    D.torusContinuousAddEquiv (-n) (D.lattice.mkQ (D.windingLift t))
  rw [D.torusContinuousAddEquiv_mkQ]
  apply (Submodule.Quotient.eq D.lattice).mpr
  exact D.windingLift_defect_mem_lattice t n

/-- The corrected winding packaged as a reusable mapping-torus translation cocycle. -/
def translationCocycle (D : Data V) :
    Mathoverflow1973.MappingTorus.TranslationCocycle D.monodromy where
  shift := D.windingShift
  continuous_shift := D.windingShift_continuous
  shift_add_int := D.windingShift_add_int

/-- The resulting integer shear family on the square-zero mapping torus. -/
def shear (D : Data V) (ell : ℤ) :
    Mathoverflow1973.MappingTorus.Torus D.monodromy.toHomeomorph ≃ₜ
      Mathoverflow1973.MappingTorus.Torus D.monodromy.toHomeomorph :=
  D.translationCocycle.shear ell

@[simp]
theorem shear_zero (D : Data V) : D.shear 0 = Homeomorph.refl _ :=
  D.translationCocycle.shear_zero

theorem shear_add_apply (D : Data V) (m n : ℤ)
    (z : Mathoverflow1973.MappingTorus.Torus D.monodromy.toHomeomorph) :
    D.shear (m + n) z = D.shear m (D.shear n z) :=
  D.translationCocycle.shear_add_apply m n z

end Data

/-- An integral primitive detector for the winding vector, annihilating its nilpotent correction. -/
structure Detector (D : Data V) where
  functional : V →ₗ[ℝ] ℝ
  lattice_integral : ∀ {x : V}, x ∈ D.lattice → ∃ z : ℤ, functional x = (z : ℝ)
  vector_one : functional D.vector = 1
  nilpotent_vector_zero : functional (D.nilpotent D.vector) = 0

namespace Detector

variable {D : Data V}

theorem functional_windingLift (P : Detector D) (t : ℝ) :
    P.functional (D.windingLift t) = t := by
  rw [Data.windingLift, map_sub, map_smul, map_smul, P.vector_one,
    P.nilpotent_vector_zero]
  simp

/-- The primitive detector separates every nonzero multiple of the quotient winding. -/
theorem windingShift_detector_ne_zero (P : Detector D) {k : ℤ} (hk : k ≠ 0) :
    k • D.windingShift (1 / (2 * (k : ℝ))) ≠ 0 := by
  have detectorValue : (k : ℝ) * (1 / (2 * (k : ℝ))) = 1 / 2 := by
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    field_simp
  intro hzero
  have hquot :
      D.lattice.mkQ (k • D.windingLift (1 / (2 * (k : ℝ)))) = 0 := by
    rw [map_zsmul]
    exact hzero
  have hmem : k • D.windingLift (1 / (2 * (k : ℝ))) ∈ D.lattice :=
    (Submodule.Quotient.mk_eq_zero D.lattice).mp hquot
  obtain ⟨z, hz⟩ := P.lattice_integral hmem
  have hdet : P.functional (k • D.windingLift (1 / (2 * (k : ℝ)))) = 1 / 2 := by
    rw [map_zsmul, P.functional_windingLift, zsmul_eq_mul]
    exact detectorValue
  have hzhalf : (z : ℝ) = 1 / 2 := hz.symm.trans hdet
  have hcast : ((2 * z : ℤ) : ℝ) = (1 : ℝ) := by
    push_cast
    linarith
  have hint : (2 : ℤ) * z = 1 := by
    exact_mod_cast hcast
  omega

/-- A primitive integral detector makes the complete integer shear family faithful. -/
theorem shear_injective (P : Detector D) : Function.Injective D.shear := by
  intro m n hmn
  by_contra hne
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hne
  have hzero := D.translationCocycle.zsmul_shift_eq_zero_of_shear_eq hmn
    (1 / (2 * ((m - n : ℤ) : ℝ)))
  exact P.windingShift_detector_ne_zero hk hzero

end Detector

end Mathoverflow1973.MappingTorus.SquareZeroWinding
