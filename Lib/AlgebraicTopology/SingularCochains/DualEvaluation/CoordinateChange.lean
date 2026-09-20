import Lib.AlgebraicTopology.SingularCochains.DualEvaluation.Free

/-!
# Coordinate change for Kronecker evaluation

The dual coordinates obtained from Kronecker evaluation transform
contragrediently when the homology marking is postcomposed with an automorphism.
-/

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open AlgebraicTopology.SingularCochains
open AlgebraicTopology.SingularCochains.DualEvaluation

namespace AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT

universe v

variable (K : ChainComplex (ModuleCat.{v} ℤ) ℕ)

/-- Replacing homology coordinates `e` by `r ∘ e` precomposes the resulting dual coordinate by
`r⁻¹`: dual coordinates transform contragrediently. -/
@[simp]
theorem cohomologyEvaluationAlong_trans_apply
    {L : Type v} [AddCommGroup L] [Module ℤ L]
    (n : ℕ) (e : K.homology (n + 1) ≃ₗ[ℤ] L) (r : L ≃ₗ[ℤ] L)
    (a : (dualComplex (AddCommGrpCat.of ℤ) K).homology (n + 1)) (x : L) :
    cohomologyEvaluationAlong K n (e.trans r) a x =
      cohomologyEvaluationAlong K n e a (r.symm x) := by
  rfl

/-- Bundled dual-map form of coordinate change. -/
theorem cohomologyEvaluationAlong_trans
    {L : Type v} [AddCommGroup L] [Module ℤ L]
    (n : ℕ) (e : K.homology (n + 1) ≃ₗ[ℤ] L) (r : L ≃ₗ[ℤ] L) :
    cohomologyEvaluationAlong K n (e.trans r) =
      cohomologyEvaluationAlong K n e ≫
        AddCommGrpCat.ofHom r.symm.dualMap.toAddEquiv.toAddMonoidHom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LinearMap.ext
  intro x
  exact cohomologyEvaluationAlong_trans_apply K n e r a x

end AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT
