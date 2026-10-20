module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Positive inner products on finite-dimensional topological vector spaces

A symmetric positive definite continuous bilinear form on a finite-dimensional
Hausdorff real topological vector space induces a norm with the original topology.
Its quadratic open unit ball is therefore von Neumann bounded. The construction
uses the auxiliary inner-product norm and uniqueness of the finite-dimensional
module topology; it does not assume a preexisting norm on the space.
-/

@[expose] public section
noncomputable section
open scoped Topology

namespace ContinuousLinearMap

universe uV

/-- The quadratic open unit ball of a symmetric positive definite continuous
bilinear form on a finite-dimensional Hausdorff real topological vector space
is von Neumann bounded. This includes the zero-dimensional case (i.1/M01). -/
theorem isVonNBounded_positiveBilinear_unitBall
    {V : Type uV} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    (g : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, g v w = g w v)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) :
    Bornology.IsVonNBounded ℝ {v : V | g v v < 1} := by
  have hnonneg (v : V) : 0 ≤ g v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (hpos v hv).le
  have hdefinite (v : V) (hv : g v v = 0) : v = 0 := by
    by_contra hne
    exact (ne_of_gt (hpos v hne)) hv
  let c : InnerProductSpace.Core ℝ V :=
    { inner := fun v w => g v w
      conj_inner_symm := fun v w => hsymm w v
      re_inner_nonneg := hnonneg
      add_left := fun v w z => congrArg (fun L : V →L[ℝ] ℝ => L z) (map_add g v w)
      smul_left := fun v w r => congrArg (fun L : V →L[ℝ] ℝ => L w) (map_smul g r v)
      definite := hdefinite }
  let τoriginal : TopologicalSpace V := inferInstance
  letI : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  have hOld : τoriginal = moduleTopology ℝ V := eq_moduleTopology ℝ V
  letI : InnerProductSpace.Core ℝ V := c
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedSpace ℝ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
  letI τnew : TopologicalSpace V :=
    (inferInstance : NormedAddCommGroup V).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  have hNew : τnew = moduleTopology ℝ V := eq_moduleTopology ℝ V
  have hSame : τoriginal = τnew := hOld.trans hNew.symm
  have hBall : Bornology.IsVonNBounded ℝ (Metric.ball (0 : V) 1) :=
    NormedSpace.isVonNBounded_ball ℝ V 1
  have hNorm (v : V) : ‖v‖ = Real.sqrt (g v v) := rfl
  have hSet : {v : V | g v v < 1} = Metric.ball (0 : V) 1 := by
    ext v
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, hNorm]
    have hs : Real.sqrt (g v v) < 1 ↔ g v v < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff (y := 1) (hnonneg v))
    exact hs.symm
  have hQuadratic : Bornology.IsVonNBounded ℝ {v : V | g v v < 1} := hSet.symm ▸ hBall
  change @Bornology.IsVonNBounded ℝ V _ _ _ τoriginal {v : V | g v v < 1}
  rw [hSame]
  exact hQuadratic

end ContinuousLinearMap
