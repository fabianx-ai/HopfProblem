/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Primitive rank-two integral cokernels

A rank-two integral matrix whose first row is primitive has cokernel linearly equivalent to the
cyclic module determined by the absolute value of its determinant. A basis-dependent form transports
the same classification to any free rank-two integral module.
-/

@[expose] public section

namespace Matrix

noncomputable section

open Module

noncomputable def quotientRangeToLin'EquivZModOfIsCoprime
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hprim : IsCoprime (A 0 0) (A 0 1)) :
    ((Fin 2 → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) ≃ₗ[ℤ] ZMod A.det.natAbs := by
  let u : ℤ := hprim.choose
  let v : ℤ := hprim.choose_spec.choose
  have hbez : u * A 0 0 + v * A 0 1 = 1 := hprim.choose_spec.choose_spec
  let q : ℤ := u * A 1 0 + v * A 1 1
  let φ : (Fin 2 → ℤ) →ₗ[ℤ] ZMod A.det.natAbs :=
    { toFun := fun z ↦ ((z 1 - q * z 0 : ℤ) : ZMod A.det.natAbs)
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  have hclass (z : Fin 2 → ℤ) :
      (A.mulVecLin z) 1 - q * (A.mulVecLin z) 0 =
        A.det * (-v * z 0 + u * z 1) := by
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q,
      Matrix.det_fin_two]
    linear_combination (-(A 1 0 * z 0 + A 1 1 * z 1)) * hbez
  have hkill (z : Fin 2 → ℤ) : φ (A.mulVecLin z) = 0 := by
    change (((A.mulVecLin z) 1 - q * (A.mulVecLin z) 0 : ℤ) : ZMod A.det.natAbs) = 0
    rw [hclass, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]
    exact dvd_mul_right _ _
  have hrange : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      exact hkill z
    · intro z hz
      rw [LinearMap.mem_ker] at hz
      change ((z 1 - q * z 0 : ℤ) : ZMod A.det.natAbs) = 0 at hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd] at hz
      obtain ⟨k, hk⟩ := hz
      refine ⟨![u * z 0 - A 0 1 * k, v * z 0 + A 0 0 * k], ?_⟩
      funext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination z 0 * hbez
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] at hk ⊢
        linear_combination -hk
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨![0, k], ?_⟩
    simp [φ]
  exact (Submodule.quotEquivOfEq _ _ hrange).trans
    (LinearMap.quotKerEquivOfSurjective φ hsurj)

noncomputable def quotientRangeToLinEquivZModOfIsCoprime
    {M : Type*} [AddCommGroup M]
    (b : Basis (Fin 2) ℤ M) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hprim : IsCoprime (A 0 0) (A 0 1)) :
    (M ⧸ LinearMap.range (Matrix.toLin b b A)) ≃ₗ[ℤ] ZMod A.det.natAbs := by
  let e := b.equivFun
  have hcomp : e.toLinearMap.comp (Matrix.toLin b b A) = A.mulVecLin.comp e.toLinearMap := by
    ext x i
    exact congr_fun (Matrix.repr_toLin b b A x) i
  have hrange : (LinearMap.range (Matrix.toLin b b A)).map e.toLinearMap =
      LinearMap.range A.mulVecLin := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, e.range, Submodule.map_top]
  exact (Submodule.Quotient.equiv _ _ e hrange).trans
    (quotientRangeToLin'EquivZModOfIsCoprime A hprim)

end


end Matrix
