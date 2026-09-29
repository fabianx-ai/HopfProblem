module
public import Lib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
/-!
# Pointwise speed under tensor-preserving smooth maps

For the SAME positive smooth tangent metrics, differentiating a composed
curve applies the map's differential to its original velocity. The tensor
identity makes that very differential a linear isometry, hence preserves
both real and extended speed. The within version uses the same parameter
set and its unique differential, so includes one-sided velocities on
nondegenerate closed pieces. No inverse map, integrated length, global
extension across joints, or distance conclusion is asserted here.

This is the generic pointwise part of the ordinary Riemannian chain-rule
argument; finite-piece length transport is a separate later result.
-/

@[expose] public section
noncomputable section
open scoped Bundle Manifold ContDiff Topology ENNReal
namespace Manifold
universe uE uH uM uF uK uN
/-- A smooth forward tensor-preserving map preserves the real and extended
speed of a differentiable curve: the chain rule uses the SAME differential
whose inner-product identity supplies its linear isometry. -/
theorem speed_comp_of_tensorPreserving
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = G.inner x v w)
    (γ : ℝ → M) (t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
      ⟨G'.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t (1 : ℝ)‖ = ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
      ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t (1 : ℝ)‖ₑ = ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨G'.toRiemannianMetric⟩
  let A : TangentSpace I (γ t) →ₗ[ℝ] TangentSpace J (f (γ t)) :=
    (mfderiv I J f (γ t)).toLinearMap
  let L : TangentSpace I (γ t) →ₗᵢ[ℝ] TangentSpace J (f (γ t)) :=
    A.isometryOfInner (hTensor (γ t))
  have hchain := mfderiv_comp_apply t
    (hf.mdifferentiable (by simp) (γ t)) hγ (1 : ℝ)
  constructor
  · rw [hchain]
    exact L.norm_map _
  · rw [hchain]
    exact L.enorm_map _

/-- The same speed equality holds for a within velocity on the SAME parameter
set, using its unique differential. On a nondegenerate closed piece this
retains that piece's one-sided endpoint velocities, without a global extension. -/
theorem speedWithin_comp_of_tensorPreserving
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = G.inner x v w)
    (γ : ℝ → M) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
      ⟨G'.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) J (f ∘ γ) s t (1 : ℝ)‖ =
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
      ‖mfderivWithin 𝓘(ℝ, ℝ) J (f ∘ γ) s t (1 : ℝ)‖ₑ =
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨G'.toRiemannianMetric⟩
  let A : TangentSpace I (γ t) →ₗ[ℝ] TangentSpace J (f (γ t)) :=
    (mfderiv I J f (γ t)).toLinearMap
  let L : TangentSpace I (γ t) →ₗᵢ[ℝ] TangentSpace J (f (γ t)) :=
    A.isometryOfInner (hTensor (γ t))
  have hchain := congrArg (fun B => B (1 : ℝ))
    (mfderiv_comp_mfderivWithin t (hf.mdifferentiable (by simp) (γ t)) hγ hs)
  constructor
  · rw [hchain]
    exact L.norm_map _
  · rw [hchain]
    exact L.enorm_map _

end Manifold
