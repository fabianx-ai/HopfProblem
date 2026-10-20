/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.Mobius

/-!
# Normalization of a disc triangle and the triangle side parameter

Project material for the analytic fillings of `Hopf/Proof/LCP/AnalyticFillings.lean`: a space `K`
homeomorphic to the closed unit disc with three marked boundary points `p0, p1, pinf` (a triangle),
punctured at `pinf`, is identified with a closed half-plane by the cross ratio sending `p0 ↦ 0`,
`p1 ↦ 1`, `pinf ↦ ∞` (`TriangleRiemannNormalization.normalizationHomeomorph`), and
`RiemannMapping.triangleSideParameter` parametrizes a triangle side through a chart.

Moved verbatim from `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean`: the
declarations of that file that both the old proof and the center construction use
(`Lib/reports/center-proof/RECEIPT.md`).
-/

open Set Function Filter Topology

noncomputable section

/-- The disc coordinate of a point `x` of a space `K` with a homeomorphism
`e : K ≃ₜ closedBall (0 : ℂ) 1`: the complex number `e x`, of norm at most one. -/
def TriangleRiemannNormalization.discCoordinate {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ℂ :=
  e x

/-- The disc coordinate is injective. -/
theorem TriangleRiemannNormalization.discCoordinate_injective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) : Function.Injective (discCoordinate e) := by
  intro x y he
  exact e.injective (Subtype.ext he)

/-- Distinct disc coordinates stay distinct. -/
theorem TriangleRiemannNormalization.discCoordinate_ne {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) {x y : K} (hxy : x ≠ y) :
    discCoordinate e x ≠ discCoordinate e y := fun he => hxy (discCoordinate_injective e he)

/-- The disc coordinate has norm at most one. -/
theorem TriangleRiemannNormalization.discCoordinate_norm_le {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ‖discCoordinate e x‖ ≤ 1 := by
  simpa only [discCoordinate, Metric.mem_closedBall, dist_zero_right] using (e x).property

/-- The puncture map: the homeomorphism from the punctured triangle to the punctured disc obtained by removing the basepoint direction. -/
def TriangleRiemannNormalization.punctureMap {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) (x : {x : K | x ≠ pinf}) :
    RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  ⟨discCoordinate e x, discCoordinate_norm_le e x, discCoordinate_ne e x.property⟩

/-- The puncture map is an embedding. -/
theorem TriangleRiemannNormalization.punctureMap_isEmbedding {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Topology.IsEmbedding (punctureMap e pinf) := by
  have hs :
    Topology.IsEmbedding
      (Subtype.val : RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have he : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => e (x : K)) :=
    e.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hv : Topology.IsEmbedding (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have hcomp : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => (e (x : K) : ℂ)) := hv.comp he
  exact hs.of_comp_iff.mp hcomp

/-- The puncture map is surjective. -/
theorem TriangleRiemannNormalization.punctureMap_surjective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Function.Surjective (punctureMap e pinf) := by
  intro z
  let y : Metric.closedBall (0 : ℂ) 1 :=
    ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1⟩
  have hx : e.symm y ≠ pinf := by
    intro he
    apply z.property.2
    have h := congrArg (discCoordinate e) he
    simpa only [discCoordinate, Homeomorph.apply_symm_apply] using h
  refine ⟨⟨e.symm y, hx⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) (e.apply_symm_apply y)

/-- The punctured triangle is homeomorphic to its normalization. -/
def TriangleRiemannNormalization.punctureHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    {x : K | x ≠ pinf} ≃ₜ RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  (punctureMap_isEmbedding e pinf).toHomeomorphOfSurjective (punctureMap_surjective e pinf)

/-- The normalization homeomorphism: the final affine correction placing the mapping target in Riemann-mapping normal form (Ahlfors, Complex Analysis, Ch. 6, the normalization step). -/
def TriangleRiemannNormalization.normalizationHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1) (h0inf : p0 ≠ pinf)
    (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1) (h1 : ‖discCoordinate e p1‖ = 1)
    (hinf : ‖discCoordinate e pinf‖ = 1) :
    {x : K | x ≠ pinf} ≃ₜ
      RiemannSphere.closedOrientedHalfPlane
        (RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
          (discCoordinate e pinf)) :=
  (punctureHomeomorph e pinf).trans
    (RiemannSphere.closedDiscHalfPlaneHomeomorph (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf)

/-- The normalization homeomorphism computes the disc coordinate. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_apply {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) (discCoordinate e x) := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_apply (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

/-- The normalization sends the first vertex to `0`. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_first {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p0, h0inf⟩ : ℂ) = 0 := by
  rw [normalizationHomeomorph_apply]
  exact RiemannSphere.MobiusCircle.crossRatio_at_zero _ _ _

/-- The normalization sends the second vertex to `1`. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_second {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p1, h1inf⟩ : ℂ) = 1 := by
  rw [normalizationHomeomorph_apply]
  exact
    RiemannSphere.MobiusCircle.crossRatio_at_one (discCoordinate_ne e h01.symm)
      (discCoordinate_ne e h1inf)

/-- The strict half-plane corresponds to the interior. -/
theorem TriangleRiemannNormalization.normalizationHomeomorph_strict_iff {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    0 <
        RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
            (discCoordinate e pinf) *
          (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ).im ↔
      ‖discCoordinate e x‖ < 1 := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_strict_iff (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)
