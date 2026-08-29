import Lib.LinearAlgebra.SquareZeroExchange
import S6Shortcuts

/-!
# Concrete square-zero exchange certificates

This proof-owned adapter derives the concrete `N`, `Q0`, and `T0` certificates from the reusable
square-zero exchange API in `Lib.LinearAlgebra.SquareZeroExchange`.

No assertion about the existence of a complex structure on the six-sphere is made here; the
analytic hypotheses of the proposed construction lie outside the scope of this module.
-/

namespace S6.SquareZeroExchange

open Lib.LinearAlgebra.SquareZeroExchange

section ConcreteCertificate

open S6Shortcuts

/-- The certified square-zero cusp matrix as a module endomorphism. -/
abbrev NEnd : Module.End ℚ V4Q := Matrix.toLin' N

/-- The certified alternating matrix as a bilinear form. -/
abbrev Q0Bilin : LinearMap.BilinForm ℚ V4Q := Matrix.toLinearMap₂' ℚ Q0

/-- The matrix exchange flow corresponding to `1 + sN`. -/
def cuspExchange (s : ℚ) : M4Q := 1 + s • N

private theorem NEnd_square_zero : NEnd * NEnd = 0 := by
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, N_square_zero]
  simp

private theorem Q0_isSkewAdjoint_N : Q0Bilin.IsSkewAdjoint NEnd := by
  rw [LinearMap.IsSkewAdjoint]
  have hmat : Matrix.IsAdjointPair Q0 Q0 N (-N) := by
    rw [Matrix.IsAdjointPair]
    have h := N_infinitesimally_preserves_Q0
    simpa [Matrix.mul_neg] using eq_neg_of_add_eq_zero_left h
  have hadj := (isAdjointPair_toLinearMap₂' (R := ℚ) Q0 Q0 N (-N)).2 hmat
  simpa using hadj

private theorem cuspExchange_toLin (s : ℚ) :
    Matrix.toLin' (cuspExchange s) = exchange NEnd s := by
  simp [cuspExchange, exchange, Module.End.one_eq_id]

/-- The abstract quadratic-term argument rederives `Nᵀ Q₀ N = 0`. -/
theorem N_quadratic_Q0_term_vanishes_derived : Matrix.transpose N * Q0 * N = 0 := by
  have hform : Q0Bilin.compl₁₂ NEnd NEnd = 0 := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.compl₁₂_apply, LinearMap.zero_apply]
    apply quadratic_term_eq_zero NEnd_square_zero Q0Bilin
    intro u v
    rw [Q0_isSkewAdjoint_N u v]
    simp
  have hmatrix := congrArg (LinearMap.toMatrix₂' ℚ) hform
  simpa using hmatrix

/-- Every rational member of the concrete cusp exchange flow preserves `Q₀`. -/
theorem cuspExchange_preserves_Q0 (s : ℚ) :
    Matrix.transpose (cuspExchange s) * Q0 * cuspExchange s = Q0 := by
  have hform :
      Q0Bilin.compl₁₂ (Matrix.toLin' (cuspExchange s))
          (Matrix.toLin' (cuspExchange s)) = Q0Bilin := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.compl₁₂_apply, cuspExchange_toLin]
    exact exchange_preserves_bilin_of_isSkewAdjoint NEnd_square_zero Q0Bilin
      Q0_isSkewAdjoint_N s x y
  have hmatrix := congrArg (LinearMap.toMatrix₂' ℚ) hform
  simpa using hmatrix

/-- The delivered cusp monodromy is the unit-time square-zero exchange. -/
theorem T0_eq_cuspExchange_one : T0 = cuspExchange 1 := by
  simpa [cuspExchange] using T0_is_I_add_N

/-- Conservation of `Q₀` by `T0`, obtained from the general square-zero flow theorem. -/
theorem T0_preserves_Q0_derived : Matrix.transpose T0 * Q0 * T0 = Q0 := by
  rw [T0_eq_cuspExchange_one]
  exact cuspExchange_preserves_Q0 1

end ConcreteCertificate

end S6.SquareZeroExchange
