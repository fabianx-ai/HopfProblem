/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.Mobius
import Shared.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization

/-!
# Normalization of a disc triangle and the triangle side parameter

Project material for the analytic fillings of `Hopf/Proof/LCP/AnalyticFillings.lean`: a space `K`
homeomorphic to the closed unit disc with three marked boundary points `p0, p1, pinf` (a triangle),
punctured at `pinf`, is identified with a closed half-plane by the cross ratio sending `p0 ↦ 0`,
`p1 ↦ 1`, `pinf ↦ ∞` (`TriangleRiemannNormalization.normalizationHomeomorph`), and
`RiemannMapping.triangleSideParameter` parametrizes a triangle side through a chart.
-/

open Set Function Filter Topology

noncomputable section

/-- The normalization orientation factor is nonzero. -/
theorem TriangleRiemannNormalization.normalization_orientation_ne_zero {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) ≠
      0 :=
  RiemannSphere.MobiusCircle.orientation_ne_zero h0 h1 hinf (discCoordinate_ne e h01.symm)
    (discCoordinate_ne e h1inf) (discCoordinate_ne e h0inf)

/-- The parameter along a triangle side. -/
def RiemannMapping.triangleSideParameter (e : OpenPartialHomeomorph ℂ ℂ) (a w : ℂ) : ℂ :=
  e.symm (w + e a)

/-- The side parameter at the vertex. -/
theorem RiemannMapping.triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) : triangleSideParameter e a 0 = a := by
  simp only [triangleSideParameter, zero_add, e.left_inv ha]

/-- The side parameter is continuous at the vertex. -/
theorem RiemannMapping.continuousAt_triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) : ContinuousAt (triangleSideParameter e a) 0 := by
  have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source ha))
  exact
    ContinuousAt.comp (g := e.symm) (f := fun w : ℂ => w + e a) (x := 0)
      (by simpa only [zero_add] using hi) (continuousAt_id.add_const (e a))
