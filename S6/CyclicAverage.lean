import Lib.LinearAlgebra.CyclicAverage
import S6Shortcuts

/-!
# Concrete cyclic-average certificates

This proof-owned adapter derives the concrete rational matrix certificates from the reusable
cyclic-averaging API in `Lib.LinearAlgebra.CyclicAverage`.

No assertion about the existence of a complex structure on the six-sphere is made here; the
analytic hypotheses of the proposed construction lie outside the scope of this module.
-/

open scoped BigOperators

namespace S6.CyclicAverage

open Lib.LinearAlgebra.CyclicAverage

section ConcreteCertificates

open S6Shortcuts

local instance : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
local instance : Invertible (4 : ℚ) := invertibleOfNonzero (by norm_num)

/-- The order-three matrix projector is the general cyclic average transported to endomorphisms. -/
theorem P3_toLin_eq_cyclicAverage :
    Matrix.toLinAlgEquiv' P3 = cyclicAverage 3 (Matrix.toLinAlgEquiv' A1) := by
  rw [P3_is_cyclic_average]
  simp [cyclicAverage, Finset.sum_range_succ]

/-- The order-four matrix projector is the general cyclic average transported to endomorphisms. -/
theorem P4_toLin_eq_cyclicAverage :
    Matrix.toLinAlgEquiv' P4 = cyclicAverage 4 (Matrix.toLinAlgEquiv' A2) := by
  rw [P4_is_cyclic_average]
  simp [cyclicAverage, Finset.sum_range_succ]

private theorem A1_toLin_order_three : (Matrix.toLinAlgEquiv' A1) ^ 3 = 1 := by
  simpa using congrArg Matrix.toLinAlgEquiv' A1_order_three

private theorem A2_toLin_order_four : (Matrix.toLinAlgEquiv' A2) ^ 4 = 1 := by
  simpa using congrArg Matrix.toLinAlgEquiv' A2_order_four

/-- Idempotence of `P3`, now obtained from the general averaging projector theorem. -/
theorem P3_idempotent_derived : P3 * P3 = P3 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P3_toLin_eq_cyclicAverage]
  exact cyclicAverage_idempotent A1_toLin_order_three

/-- Idempotence of `P4`, now obtained from the general averaging projector theorem. -/
theorem P4_idempotent_derived : P4 * P4 = P4 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P4_toLin_eq_cyclicAverage]
  exact cyclicAverage_idempotent A2_toLin_order_four

/-- Left fixedness of the order-three projector, derived from cyclic averaging. -/
theorem A1_mul_P3_derived : A1 * P3 = P3 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P3_toLin_eq_cyclicAverage]
  exact mul_cyclicAverage A1_toLin_order_three

/-- Right fixedness of the order-three projector, derived from cyclic averaging. -/
theorem P3_mul_A1_derived : P3 * A1 = P3 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P3_toLin_eq_cyclicAverage]
  exact cyclicAverage_mul A1_toLin_order_three

/-- Left fixedness of the order-four projector, derived from cyclic averaging. -/
theorem A2_mul_P4_derived : A2 * P4 = P4 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P4_toLin_eq_cyclicAverage]
  exact mul_cyclicAverage A2_toLin_order_four

/-- Right fixedness of the order-four projector, derived from cyclic averaging. -/
theorem P4_mul_A2_derived : P4 * A2 = P4 := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul]
  rw [P4_toLin_eq_cyclicAverage]
  exact cyclicAverage_mul A2_toLin_order_four

/-- The concrete order-three average has exactly the `A1`-fixed vectors as its range. -/
theorem range_P3_toLin :
    LinearMap.range (Matrix.toLinAlgEquiv' P3) =
      LinearMap.ker (Matrix.toLinAlgEquiv' A1 - 1) := by
  rw [P3_toLin_eq_cyclicAverage]
  exact range_cyclicAverage A1_toLin_order_three

/-- The concrete order-four average has exactly the `A2`-fixed vectors as its range. -/
theorem range_P4_toLin :
    LinearMap.range (Matrix.toLinAlgEquiv' P4) =
      LinearMap.ker (Matrix.toLinAlgEquiv' A2 - 1) := by
  rw [P4_toLin_eq_cyclicAverage]
  exact range_cyclicAverage A2_toLin_order_four

/-- Fixedness of the projected order-three seed follows from projector fixedness. -/
theorem epsilon_fixed_derived : Matrix.mulVec A1 epsilon = epsilon := by
  calc
    Matrix.mulVec A1 epsilon = Matrix.mulVec A1 (Matrix.mulVec P3 eGamma) := by
      rw [P3_projects_seed]
    _ = Matrix.mulVec (A1 * P3) eGamma := Matrix.mulVec_mulVec _ _ _
    _ = Matrix.mulVec P3 eGamma := by rw [A1_mul_P3_derived]
    _ = epsilon := P3_projects_seed

/-- Fixedness of the projected order-four seed follows from projector fixedness. -/
theorem epsilonPrime_fixed_derived : Matrix.mulVec A2 epsilonPrime = epsilonPrime := by
  calc
    Matrix.mulVec A2 epsilonPrime = Matrix.mulVec A2 (Matrix.mulVec P4 eGamma) := by
      rw [P4_projects_seed]
    _ = Matrix.mulVec (A2 * P4) eGamma := Matrix.mulVec_mulVec _ _ _
    _ = Matrix.mulVec P4 eGamma := by rw [A2_mul_P4_derived]
    _ = epsilonPrime := P4_projects_seed

/-- Evaluation at the first coordinate, as a linear observable. -/
abbrev gammaLinear : V4Q →ₗ[ℚ] ℚ := LinearMap.proj 0

private theorem gammaLinear_comp_A1 :
    gammaLinear.comp (Matrix.toLinAlgEquiv' A1) = gammaLinear := by
  ext x
  simp [gammaLinear, A1, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

private theorem gammaLinear_comp_A2 :
    gammaLinear.comp (Matrix.toLinAlgEquiv' A2) = gammaLinear := by
  ext x
  simp [gammaLinear, A2, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The first-coordinate observable survives the order-three averaging projector. -/
theorem gammaLinear_comp_P3 :
    gammaLinear.comp (Matrix.toLinAlgEquiv' P3) = gammaLinear := by
  rw [P3_toLin_eq_cyclicAverage]
  exact comp_cyclicAverage gammaLinear gammaLinear_comp_A1

/-- The first-coordinate observable survives the order-four averaging projector. -/
theorem gammaLinear_comp_P4 :
    gammaLinear.comp (Matrix.toLinAlgEquiv' P4) = gammaLinear := by
  rw [P4_toLin_eq_cyclicAverage]
  exact comp_cyclicAverage gammaLinear gammaLinear_comp_A2

/-- The projected order-three seed has observable value one, by invariant averaging. -/
theorem gamma_epsilon_derived : gammaValue epsilon = 1 := by
  have h := DFunLike.congr_fun gammaLinear_comp_P3 eGamma
  simp only [LinearMap.comp_apply, Matrix.toLinAlgEquiv'_apply] at h
  rw [P3_projects_seed] at h
  simpa [gammaLinear, gammaValue, eGamma] using h

/-- The projected order-four seed has observable value one, by invariant averaging. -/
theorem gamma_epsilonPrime_derived : gammaValue epsilonPrime = 1 := by
  have h := DFunLike.congr_fun gammaLinear_comp_P4 eGamma
  simp only [LinearMap.comp_apply, Matrix.toLinAlgEquiv'_apply] at h
  rw [P4_projects_seed] at h
  simpa [gammaLinear, gammaValue, eGamma] using h

/-- The signed first twist has observable value one. -/
theorem gamma_v1_derived : gammaValue v1 = 1 := by
  simpa [v1] using gamma_epsilon_derived

/-- The signed second twist has observable value minus one. -/
theorem gamma_v2_derived : gammaValue v2 = -1 := by
  simp [v2, gammaValue, epsilonPrime]

end ConcreteCertificates

end S6.CyclicAverage
