/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Images of injective endomorphisms of finite free integral modules

An injective endomorphism of a finite free integral module has full-rank image, hence finite
cokernel.  Consequently a nonzero integral multiple of every target vector belongs to the image.
-/

@[expose] public section

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Every vector has a nonzero integral multiple in the image of an injective endomorphism of a
finite free integral module. -/
theorem exists_ne_zero_smul_mem_range_of_injective
    (f : M →ₗ[ℤ] M) (hf : Function.Injective f) (x : M) :
    ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ LinearMap.range f := by
  have hrank : Module.finrank ℤ (LinearMap.range f) = Module.finrank ℤ M :=
    LinearMap.finrank_range_of_inj hf
  let _ : Finite (M ⧸ LinearMap.range f) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range f) hrank
  let n := Nat.card (M ⧸ LinearMap.range f)
  have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hindex : (LinearMap.range f).toAddSubgroup.index = n := by
    rw [AddSubgroup.index_eq_card]
    rfl
  refine ⟨(n : ℤ), Int.ofNat_ne_zero.mpr hn, ?_⟩
  have hmemAdd : n • x ∈ (LinearMap.range f).toAddSubgroup := by
    simpa only [hindex] using
      AddSubgroup.nsmul_index_mem (LinearMap.range f).toAddSubgroup x
  have hmem : n • x ∈ LinearMap.range f := hmemAdd
  simpa only [Nat.cast_smul_eq_nsmul] using hmem

end LinearMap
