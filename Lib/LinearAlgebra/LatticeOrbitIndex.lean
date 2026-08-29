/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib

/-!
# Full-rank integral lattice index

This file exports the proof-independent algebraic core of V10 Lemma 6.6: the quotient by the
column lattice of a full-rank square integral matrix has cardinality equal to the absolute value
of its determinant. The separate torsor-to-orbit adapter is intentionally not asserted here.
-/

namespace Lib.LinearAlgebra.LatticeOrbitIndex

/-- The integral linear map whose image is the column lattice of `B`. -/
abbrev latticeMap {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) := Matrix.toLin' B

/-- The set of lattice cosets, equivalently the orbit set for translation by the column lattice. -/
abbrev LatticeOrbits {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) :=
  (Fin r → ℤ) ⧸ LinearMap.range (latticeMap B)

/-- A square integral matrix with nonzero determinant is injective on the integral lattice. -/
theorem latticeMap_injective {r : ℕ} {B : Matrix (Fin r) (Fin r) ℤ} (hB : B.det ≠ 0) :
    Function.Injective (latticeMap B) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  apply hB
  rw [← LinearMap.det_toLin']
  exact LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker

/-- The index of a full-rank square integral matrix is the absolute value of its determinant. -/
theorem natCard_latticeOrbits_eq_natAbs_det {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : B.det ≠ 0) : Nat.card (LatticeOrbits B) = B.det.natAbs := by
  let f := latticeMap B
  let e : (Fin r → ℤ) ≃ₗ[ℤ] LinearMap.range f :=
    LinearEquiv.ofInjective f (latticeMap_injective hB)
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range f) e
  rw [← hcard]
  congr 1
  rw [← LinearMap.det_toLin']
  congr 1

end Lib.LinearAlgebra.LatticeOrbitIndex
