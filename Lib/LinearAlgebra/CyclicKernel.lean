/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Kernel detection from a cyclic generator

The result is a small strict integer-linear helper: to prove that a linear character vanishes on a
kernel identified with `ℤ`, it suffices to evaluate it on the chosen generator.
-/

@[expose] public noncomputable section


/-- Express an element through the generator selected by a linear equivalence with `ℤ`. -/
theorem eq_equiv_smul_generator {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (x : M) :
    x = e x • e.symm 1 := by
  apply e.injective
  simp

/-- Vanishing on a cyclic kernel follows from vanishing on its displayed generator. -/
theorem ker_le_of_cyclic_generator_zero
    {M N A : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [AddCommGroup A] [Module ℤ A]
    (f : M →ₗ[ℤ] N) (χ : M →ₗ[ℤ] A)
    (e : LinearMap.ker f ≃ₗ[ℤ] ℤ)
    (hgen : χ (e.symm 1).val = 0) :
    f.ker ≤ χ.ker := by
  intro a ha
  let ka : LinearMap.ker f := ⟨a, ha⟩
  rw [LinearMap.mem_ker]
  have hshape := eq_equiv_smul_generator e ka
  have hval : a = e ka • (e.symm 1).val := by
    simpa [ka] using congrArg Subtype.val hshape
  change χ a = 0
  rw [hval, map_zsmul, hgen]
  exact zsmul_zero (e ka)
