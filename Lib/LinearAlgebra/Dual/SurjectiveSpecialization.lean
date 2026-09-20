/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Duals of surjective specialization maps

This module contains only generic linear algebra. It makes no claim
about homology, cohomology, UCT, monodromy of a particular family, or an analytic specialization.

The substantial range/annihilator facts are already in Mathlib. The new residue merely rewrites
the annihilator of `range (A - 1)` as the fixed submodule of the dual action and composes the two
existing theorems.
-/

@[expose] public section

open Module

namespace LinearMap

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Taking the algebraic dual commutes with subtraction of linear maps. -/
@[simp]
theorem dualMap_sub (f g : M →ₗ[R] N) :
    (f - g).dualMap = f.dualMap - g.dualMap := by
  ext φ x
  simp

/-- The annihilator of the image of a difference is the kernel of the dual difference. -/
theorem dualAnnihilator_range_sub_eq_ker_sub_dualMap (f g : M →ₗ[R] N) :
    (range (f - g)).dualAnnihilator = ker (f.dualMap - g.dualMap) := by
  rw [← (f - g).ker_dualMap_eq_dualAnnihilator_range, dualMap_sub]

/-- The annihilator of `range (A - 1)` is exactly the fixed submodule of the dual action. -/
theorem dualAnnihilator_range_sub_id_eq_fixedSubmodule (A : M →ₗ[R] M) :
    (range (A - id)).dualAnnihilator = A.dualMap.fixedSubmodule := by
  rw [dualAnnihilator_range_sub_eq_ker_sub_dualMap, dualMap_id, fixedSubmodule_eq_ker]

/--
If a surjection has kernel `range (A - 1)`, its dual embeds with image the fixed submodule of the
dual action.

No freeness, finite-generation, PID, or field hypothesis is needed: surjectivity identifies the
target with the quotient by the kernel, and Mathlib already identifies the dual of a quotient with
the annihilator of the kernel over any commutative ring.
-/
theorem range_dualMap_eq_fixedSubmodule_of_surjective_of_ker_eq_range_sub_id
    (f : M →ₗ[R] N) (A : M →ₗ[R] M) (hf : Function.Surjective f)
    (hker : ker f = range (A - id)) :
    range f.dualMap = A.dualMap.fixedSubmodule := by
  rw [range_dualMap_eq_dualAnnihilator_ker_of_surjective f hf, hker,
    dualAnnihilator_range_sub_id_eq_fixedSubmodule]

/-- The corresponding canonical linear equivalence onto the dual fixed submodule. -/
noncomputable def dualEquivFixedSubmoduleOfSurjectiveOfKerEqRangeSubId
    (f : M →ₗ[R] N) (A : M →ₗ[R] M) (hf : Function.Surjective f)
    (hker : ker f = range (A - id)) :
    Dual R N ≃ₗ[R] A.dualMap.fixedSubmodule :=
  (LinearEquiv.ofInjective f.dualMap (dualMap_injective_of_surjective hf)).trans
    (LinearEquiv.ofEq _ _
      (range_dualMap_eq_fixedSubmodule_of_surjective_of_ker_eq_range_sub_id f A hf hker))

@[simp]
theorem dualEquivFixedSubmoduleOfSurjectiveOfKerEqRangeSubId_apply_coe
    (f : M →ₗ[R] N) (A : M →ₗ[R] M) (hf : Function.Surjective f)
    (hker : ker f = range (A - id)) (φ : Dual R N) :
    ((dualEquivFixedSubmoduleOfSurjectiveOfKerEqRangeSubId f A hf hker φ :
        A.dualMap.fixedSubmodule) : Dual R M) = f.dualMap φ := by
  rfl

section DualityTransport

variable {C D : Type*}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]

/--
Injectivity transported across any contravariant duality square. The intended later application is a
UCT naturality square, but this statement mentions only linear maps and linear equivalences.
-/
theorem injective_of_duality_naturality_of_surjective
    (f : M →ₗ[R] N) (g : D →ₗ[R] C)
    (sourceDuality : C ≃ₗ[R] Dual R M) (targetDuality : D ≃ₗ[R] Dual R N)
    (hnat : sourceDuality.toLinearMap.comp g =
      f.dualMap.comp targetDuality.toLinearMap)
    (hf : Function.Surjective f) : Function.Injective g := by
  intro x y hxy
  apply targetDuality.injective
  apply dualMap_injective_of_surjective hf
  have hx := LinearMap.congr_fun hnat x
  have hy := LinearMap.congr_fun hnat y
  change sourceDuality (g x) = f.dualMap (targetDuality x) at hx
  change sourceDuality (g y) = f.dualMap (targetDuality y) at hy
  calc
    f.dualMap (targetDuality x) = sourceDuality (g x) := hx.symm
    _ = sourceDuality (g y) := congrArg sourceDuality hxy
    _ = f.dualMap (targetDuality y) := hy

/--
The range statement transported across a contravariant duality square. It is the exact generic
output a later UCT adapter needs: in dual coordinates, the pullback image is the fixed submodule.
-/
theorem map_range_eq_fixedSubmodule_of_duality_naturality
    (f : M →ₗ[R] N) (g : D →ₗ[R] C) (A : M →ₗ[R] M)
    (sourceDuality : C ≃ₗ[R] Dual R M) (targetDuality : D ≃ₗ[R] Dual R N)
    (hnat : sourceDuality.toLinearMap.comp g =
      f.dualMap.comp targetDuality.toLinearMap)
    (hf : Function.Surjective f) (hker : ker f = range (A - id)) :
    (range g).map sourceDuality.toLinearMap = A.dualMap.fixedSubmodule := by
  calc
    (range g).map sourceDuality.toLinearMap =
        range (sourceDuality.toLinearMap.comp g) := (range_comp g sourceDuality.toLinearMap).symm
    _ = range (f.dualMap.comp targetDuality.toLinearMap) := congrArg range hnat
    _ = range f.dualMap :=
      range_comp_of_range_eq_top f.dualMap (LinearEquiv.range targetDuality)
    _ = A.dualMap.fixedSubmodule :=
      range_dualMap_eq_fixedSubmodule_of_surjective_of_ker_eq_range_sub_id f A hf hker

end DualityTransport

end LinearMap
