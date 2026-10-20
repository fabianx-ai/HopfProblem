module
public import Lib.Analysis.InnerProductSpace.FiniteDimensional
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth positive metrics on finite-rank real vector bundles

A smooth field of symmetric positive definite continuous bilinear forms on a
finite-rank real vector bundle determines a smooth Riemannian metric. Its
quadratic unit balls are bounded by the finite-dimensional positive-form
theorem, so the induced norms retain the original fiber topologies.
-/

@[expose] public section
noncomputable section
open scoped Bundle Manifold ContDiff Topology
namespace Bundle
universe uEB uHB uB uF uE
variable {EB : Type uEB} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
variable {HB : Type uHB} [TopologicalSpace HB]
variable {IB : ModelWithCorners ℝ EB HB}
variable {B : Type uB} [TopologicalSpace B] [ChartedSpace HB B]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ F]
variable {E : B → Type uE} [TopologicalSpace (Bundle.TotalSpace F E)]
variable [tE : ∀ b, TopologicalSpace (E b)]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [∀ b, IsTopologicalAddGroup (E b)]
variable [∀ b, ContinuousSMul ℝ (E b)] [∀ b, T2Space (E b)]
variable [FiberBundle F E] [VectorBundle ℝ F E]

/-- A smooth symmetric positive definite bilinear field on a finite-rank real
vector bundle defines a smooth Riemannian metric, with bounded quadratic unit
balls derived from finite dimension rather than assumed (i.1/i.2, M02). -/
def smoothMetricOfPositive
    (g : ∀ b, E b →L[ℝ] E b →L[ℝ] ℝ)
    (hsymm : ∀ b v w, g b v w = g b w v)
    (hpos : ∀ b v, v ≠ 0 → 0 < g b v v)
    (hsmooth : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun b => Bundle.TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))) :
    Bundle.ContMDiffRiemannianMetric IB ∞ F E :=
  { inner := g
    symm := hsymm
    pos := hpos
    isVonNBounded := fun b =>
      letI : FiniteDimensional ℝ (E b) := VectorBundle.finiteDimensional ℝ F E b
      ContinuousLinearMap.isVonNBounded_positiveBilinear_unitBall
        (g b) (hsymm b) (hpos b)
    contMDiff := hsmooth }

/-- The metric constructed from a positive smooth bilinear field has exactly
that field as its inner product (i.1/i.2, M03). -/
theorem smoothMetricOfPositive_inner
    (g : ∀ b, E b →L[ℝ] E b →L[ℝ] ℝ)
    (hsymm : ∀ b v w, g b v w = g b w v)
    (hpos : ∀ b v, v ≠ 0 → 0 < g b v v)
    (hsmooth : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun b => Bundle.TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b)))
    (b : B) (v w : E b) :
    (smoothMetricOfPositive g hsymm hpos hsmooth).inner b v w = g b v w := rfl

end Bundle
