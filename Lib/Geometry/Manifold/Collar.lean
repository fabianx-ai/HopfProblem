/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Analysis.ODE.SmoothFlow
public import Lib.Geometry.Manifold.ChartedSpace.Transport
public import Lib.Topology.Homotopy.CylinderHEP
public import Lib.Topology.Homotopy.HandleRetraction
public import Lib.Geometry.Manifold.Morse.SublevelSets
public import Lib.Geometry.Manifold.Morse.Index
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Collars of regular levels and level transport

Collars of regular level sets, compactly supported ambient diffeomorphisms moving one level
to a nearby one, and the tubular neighbourhood of an embedded closed ball:
`CollarHeight.*`, `SupportedDiffeomorph.*` (diffeomorphisms supported in a
given open set), `DiskFraming.*`, `SmallPerturbation.*`,
`SphereCoordinates.*`, and
`exists_tubularNeighborhood_in_open_of_embedded_closedBall` — Lee Ch. 10's collar and
tubular-neighbourhood theorems in the level-transport form used by the recognition
development. (The plan's Tubular.lean is folded here; see Lib/reports/A.md.)

## Main definitions and results

* `CollarHeight.*`, `SupportedDiffeomorph.*` : collar coordinates and supported
  diffeomorphisms.
* `exists_tubularNeighborhood_in_open_of_embedded_closedBall` : the tubular
  neighbourhood theorem (specialized form).
* `RegularLevel.*` : level-diffeomorphism lemmas.

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Ch. 10 (collars and tubular
  neighbourhoods), Thm 6.24

## Tags

collar, tubular neighbourhood, supported diffeomorphism, level transport
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The normal bundle of an embedding -/

/-- The normal space of the embedding at a point. -/
abbrev NativeEuclideanEmbedding.NormalSpace {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :=
  ↥(e.normalProjection x).range

/-- The normal bundle's model space. -/
abbrev NativeEuclideanEmbedding.NormalModel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) :=
  EuclideanSpace ℝ (Fin (e.ambientDimension - Module.finrank ℝ E))

/-- The normal space is equivalent to the model. -/
noncomputable def NativeEuclideanEmbedding.normalSpaceEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) : e.NormalSpace x ≃L[ℝ] e.normalFiber x :=
  ContinuousLinearEquiv.ofEq _ _ (e.range_normalProjection x)

/-- The normal space's finite rank. -/
theorem NativeEuclideanEmbedding.finrank_normalSpace {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ (e.NormalSpace x) = e.ambientDimension - Module.finrank ℝ E := by
  have h := e.finrank_tangent_add_normal x
  rw [(e.normalSpaceEquiv x).toLinearEquiv.finrank_eq]
  omega

/-- The normal model equivalence. -/
noncomputable def NativeEuclideanEmbedding.normalModelEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) : e.NormalSpace x ≃L[ℝ] e.NormalModel :=
  (LinearEquiv.ofFinrankEq (e.NormalSpace x) e.NormalModel
      (by
        rw [e.finrank_normalSpace x]
        exact finrank_euclideanSpace_fin.symm)).toContinuousLinearEquiv

/-- The normal bundle's prebundle structure. -/
noncomputable def NativeEuclideanEmbedding.normalPrebundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    VectorPrebundle ℝ e.NormalModel e.NormalSpace :=
  ProjectionBundle.vectorPrebundle e.normalProjection e.normalProjection_idempotent
    e.normalModelEquiv e.contMDiff_normalProjection

/-- The normal prebundle is smooth. -/
instance NativeEuclideanEmbedding.normalPrebundle_isContMDiff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    e.normalPrebundle.IsContMDiff 𝓘(ℝ, E) ∞ :=
  ProjectionBundle.vectorPrebundle_isContMDiff e.normalProjection
    e.normalProjection_idempotent e.normalModelEquiv e.contMDiff_normalProjection

/-- The normal bundle of the embedding. -/
abbrev NativeEuclideanEmbedding.NormalBundle {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) :=
  Bundle.TotalSpace e.NormalModel e.NormalSpace

/-- The normal bundle's topology. -/
noncomputable instance NativeEuclideanEmbedding.normalBundleTopology {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    TopologicalSpace e.NormalBundle :=
  e.normalPrebundle.totalSpaceTopology

/-- The normal bundle as a fiber bundle. -/
noncomputable instance NativeEuclideanEmbedding.normalFiberBundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    FiberBundle e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toFiberBundle

/-- The normal bundle as a vector bundle. -/
instance NativeEuclideanEmbedding.normalVectorBundle {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    VectorBundle ℝ e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toVectorBundle

/-- The normal bundle is a smooth vector bundle. -/
instance NativeEuclideanEmbedding.normalContMDiffVectorBundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffVectorBundle ∞ e.NormalModel e.NormalSpace 𝓘(ℝ, E) :=
  e.normalPrebundle.contMDiffVectorBundle 𝓘(ℝ, E)

/-! ### Normal displacement -/

/-- A normal vector at a base point. -/
def NativeEuclideanEmbedding.normalVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (v : e.NormalBundle) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  v.2

/-- The normal vector field is smooth. -/
theorem NativeEuclideanEmbedding.contMDiff_normalVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞ e.normalVector := by
  intro z
  have hp :
    ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓘(ℝ, E)) ∞ (fun v : e.NormalBundle ↦ v.proj)
      z :=
    Bundle.contMDiffAt_proj e.NormalSpace
  have hc :
    ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) 𝓘(ℝ, e.NormalModel) ∞
      (fun v : e.NormalBundle ↦
        ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1 v.2)
      z := by
    have h :=
      (Bundle.contMDiffAt_totalSpace (IB := 𝓘(ℝ, E)) (IM := (𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel))
            (n := ∞) (f := id) (x₀ := z)).mp
        contMDiffAt_id
    exact h.2
  have hf :=
    ((ProjectionBundle.contMDiff_ambientFromCoordinates e.normalProjection
              e.normalModelEquiv e.contMDiff_normalProjection z.1).contMDiffAt.comp
          z hp).clm_apply
      hc
  have heq :
    e.normalVector =ᶠ[𝓝 z]
      (fun v : e.NormalBundle ↦
        ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv z.1
          v.1
          (ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1
            v.2)) := by
    have ho :=
      isOpen_projectionTransportDomain e.normalProjection e.contMDiff_normalProjection
        z.1
    have hn :=
      hp.continuousAt
        (ho.mem_nhds
          (mem_projectionTransportDomain e.normalProjection e.normalProjection_idempotent
            z.1))
    filter_upwards [hn] with v hv
    exact
      (congrArg Subtype.val
          (ProjectionBundle.fromCoordinates_toCoordinates e.normalProjection
            e.normalProjection_idempotent e.normalModelEquiv z.1 v.1 hv v.2)).symm
  exact heq.contMDiffAt_iff.mpr hf

/-- The ambient displacement along a normal vector. -/
def NativeEuclideanEmbedding.normalDisplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (v : e.NormalBundle) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun v.proj + e.normalVector v

/-- The normal displacement is smooth. -/
theorem NativeEuclideanEmbedding.contMDiff_normalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement :=
  (e.smooth.comp (Bundle.contMDiff_proj e.NormalSpace)).add e.contMDiff_normalVector

/-- The normal displacement of the zero vector is the base point. -/
theorem NativeEuclideanEmbedding.normalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    e.normalDisplacement (Bundle.zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
  simp [normalDisplacement, normalVector, Bundle.zeroSection]

/-- The normal displacement in a local chart. -/
noncomputable def NativeEuclideanEmbedding.localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x₀ : M) (p : M × e.NormalModel) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun p.1 +
    ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv x₀ p.1
      p.2

/-- The local normal displacement is smooth. -/
theorem NativeEuclideanEmbedding.contMDiff_localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    (x₀ : M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x₀) :=
  (e.smooth.comp contMDiff_fst).add
    (((ProjectionBundle.contMDiff_ambientFromCoordinates e.normalProjection
              e.normalModelEquiv e.contMDiff_normalProjection x₀).comp
          contMDiff_fst).clm_apply
      contMDiff_snd)

/-- The local normal displacement at zero. -/
theorem NativeEuclideanEmbedding.localNormalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x₀ x : M) :
    e.localNormalDisplacement x₀ (x, 0) = e.toFun x := by simp [localNormalDisplacement]

/-- The ambient normal coordinates at the base point. -/
theorem NativeEuclideanEmbedding.ambientNormalCoordinates_self {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) (v : e.NormalModel) :
    ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv x x v =
      ((e.normalModelEquiv x).symm v : EuclideanSpace ℝ (Fin e.ambientDimension)) := by
  change
    e.normalProjection x
        (projectionIntertwiner (e.normalProjection x) (e.normalProjection x)
          ((e.normalModelEquiv x).symm v)) =
      _
  rw [projectionIntertwiner_self _ (e.normalProjection_idempotent x)]
  exact projection_apply_range (e.normalProjection x) (e.normalProjection_idempotent x) _

/-- The tangent space splits into tangent and normal parts. -/
noncomputable def NativeEuclideanEmbedding.normalLinearSplitting {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : NativeEuclideanEmbedding E M) (x : M) :
    (TangentSpace (𝓘(ℝ, E)) x × e.NormalModel) ≃L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((ContinuousLinearEquiv.refl ℝ (TangentSpace (𝓘(ℝ, E)) x)).prodCongr
        ((e.normalModelEquiv x).symm.trans (e.normalSpaceEquiv x))).trans
    (e.tangentNormalEquiv x)

/-- The derivative of the local normal displacement at zero. -/
theorem NativeEuclideanEmbedding.mvfderiv_localNormalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (e.localNormalDisplacement x) (x, 0) =
      (e.normalLinearSplitting x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  have hd := (e.contMDiff_localNormalDisplacement x).mdifferentiable (by simp) (x, 0)
  have hprod :=
    mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, e.NormalModel)) (I'' :=
      𝓡 e.ambientDimension) (v := v) hd
  have hleft : (fun y : M ↦ e.localNormalDisplacement x (y, 0)) = e.toFun :=
    funext (e.localNormalDisplacement_zero x)
  let C : e.NormalModel →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    (e.normalProjection x).range.subtypeL.comp (e.normalModelEquiv x).symm.toContinuousLinearMap
  have hright :
    (fun y : e.NormalModel ↦ e.localNormalDisplacement x (x, y)) = (fun y ↦ e.toFun x + C y) := by
    funext y
    exact congrArg (e.toFun x + ·) (e.ambientNormalCoordinates_self x y)
  have hC :
    mfderiv 𝓘(ℝ, e.NormalModel) (𝓡 e.ambientDimension) (fun y ↦ e.toFun x + C y)
        (0 : e.NormalModel) =
      C :=
    (C.hasFDerivAt.const_add (e.toFun x)).hasMFDerivAt.mfderiv
  change
    mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        (e.localNormalDisplacement x) (x, 0) v =
      _
  rw [hprod, hleft, hright, hC]
  rfl

/-- The local normal displacement's derivative is invertible at zero. -/
theorem NativeEuclideanEmbedding.localNormalDisplacement_derivative_isInvertible
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    (mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (e.localNormalDisplacement x)
        (x, 0)).IsInvertible :=
  ⟨e.normalLinearSplitting x, (e.mvfderiv_localNormalDisplacement_zero x).symm⟩

/-- The local normal displacement computes the displacement. -/
theorem NativeEuclideanEmbedding.localNormalDisplacement_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x₀ : M) (p : M × e.NormalModel) :
    e.localNormalDisplacement x₀ p =
      e.normalDisplacement
        ⟨p.1,
          ProjectionBundle.fromCoordinates e.normalProjection e.normalModelEquiv x₀ p.1
            p.2⟩ :=
  rfl

/-- The local normal displacement is a local diffeomorphism at zero. -/
theorem NativeEuclideanEmbedding.isLocalDiffeomorphAt_localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x) (x, 0) := by
  exact
    isLocalDiffeomorphAt_of_invertible_mvfderiv (e.contMDiff_localNormalDisplacement x)
      (e.localNormalDisplacement_derivative_isInvertible x)

/-- The normal chart as a partial diffeomorphism. -/
noncomputable def NativeEuclideanEmbedding.normalChartPartialDiffeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel))
      e.NormalBundle (M × e.NormalModel) ∞
    where
  toPartialEquiv :=
    (FiberBundle.trivializationAt e.NormalModel e.NormalSpace
        x).toOpenPartialHomeomorph.toPartialEquiv
  open_source := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).open_source
  open_target := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).open_target
  contMDiffOn_toFun := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn
  contMDiffOn_invFun :=
    (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn_symm

/-- The normal chart diffeomorphism at zero. -/
theorem NativeEuclideanEmbedding.normalChartPartialDiffeomorph_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    e.normalChartPartialDiffeomorph x (Bundle.zeroSection e.NormalModel e.NormalSpace x) =
      (x, 0) := by
  change
    (x, ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x x 0) =
      (x, 0)
  rw [map_zero]

/-- Zero lies in the normal chart's source. -/
theorem NativeEuclideanEmbedding.normalChart_source_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    Bundle.zeroSection e.NormalModel e.NormalSpace x ∈
      (e.normalChartPartialDiffeomorph x).source := by
  change x ∈ projectionTransportDomain e.normalProjection x
  exact mem_projectionTransportDomain e.normalProjection e.normalProjection_idempotent x

/-- The local normal displacement computes in the chart. -/
theorem NativeEuclideanEmbedding.localNormalDisplacement_chart_apply {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M)
    (v : e.NormalBundle) (hv : v ∈ (e.normalChartPartialDiffeomorph x).source) :
    e.localNormalDisplacement x (e.normalChartPartialDiffeomorph x v) = e.normalDisplacement v := by
  have hbase : v.proj ∈ projectionTransportDomain e.normalProjection x := hv
  have hback :=
    ProjectionBundle.fromCoordinates_toCoordinates e.normalProjection
      e.normalProjection_idempotent e.normalModelEquiv x v.proj hbase v.2
  rw [e.localNormalDisplacement_eq]
  change
    e.normalDisplacement
        ⟨v.proj,
          ProjectionBundle.fromCoordinates e.normalProjection e.normalModelEquiv x v.proj
            (ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x
              v.proj v.2)⟩ =
      _
  rw [hback]

/-- The normal displacement is a local diffeomorphism at the zero section. -/
theorem NativeEuclideanEmbedding.isLocalDiffeomorphAt_normalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement (Bundle.zeroSection e.NormalModel e.NormalSpace x) := by
  obtain ⟨d, hd, heq⟩ := e.isLocalDiffeomorphAt_localNormalDisplacement x
  let c := e.normalChartPartialDiffeomorph x
  have hc : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ c.source :=
    e.normalChart_source_zero x
  have hcd : c (Bundle.zeroSection e.NormalModel e.NormalSpace x) ∈ d.source := by
    rw [e.normalChartPartialDiffeomorph_zero]
    exact hd
  refine ⟨c.trans d, ⟨hc, hcd⟩, ?_⟩
  intro v hv
  exact (e.localNormalDisplacement_chart_apply x v hv.1).symm.trans (heq hv.2)

/-! ### The tubular neighborhood -/

/-- The locus where the normal displacement is a local diffeomorphism. -/
def NativeEuclideanEmbedding.regularNormalLocus {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) : Set e.NormalBundle :=
  {v |
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement v}

/-- The regular normal locus is open. -/
theorem NativeEuclideanEmbedding.isOpen_regularNormalLocus {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) :
    IsOpen e.regularNormalLocus := by
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨φ, hv, heq⟩
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hv) (fun w hw ↦ ⟨φ, hw, heq⟩)

/-- The normal displacement is injective near the zero section. -/
theorem NativeEuclideanEmbedding.normalDisplacement_injOn_zeroSection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) :
    Set.InjOn e.normalDisplacement (Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace)) :=
  by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have hxy : e.toFun x = e.toFun y := by simpa only [e.normalDisplacement_zero] using h
  exact
    congrArg (Bundle.zeroSection e.NormalModel e.NormalSpace) (e.closedEmbedding.injective hxy)

/-- The normal displacement is locally injective at zero. -/
theorem NativeEuclideanEmbedding.normalDisplacement_locally_injective_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x : M) :
    ∃ U ∈ 𝓝 (Bundle.zeroSection e.NormalModel e.NormalSpace x),
      Set.InjOn e.normalDisplacement U := by
  obtain ⟨φ, hx, heq⟩ := e.isLocalDiffeomorphAt_normalDisplacement_zero x
  exact ⟨φ.source, φ.open_source.mem_nhds hx, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩

/-- An injective normal neighborhood of the zero section exists. -/
theorem NativeEuclideanEmbedding.exists_injective_normalNeighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    [CompactSpace M] :
    ∃ U : Set e.NormalBundle,
      IsOpen U ∧
        Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace) ⊆ U ∧
          Set.InjOn e.normalDisplacement U ∧
            IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
              e.normalDisplacement U := by
  have hc : IsCompact (Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace)) :=
    isCompact_range (Bundle.Trivialization.continuous_zeroSection ℝ)
  obtain ⟨V, hV, hsV, hInj⟩ :=
    e.normalDisplacement_injOn_zeroSection.exists_isOpen_superset hc
      (fun v _ ↦ e.contMDiff_normalDisplacement.continuous.continuousAt)
      (by rintro _ ⟨x, rfl⟩; exact e.normalDisplacement_locally_injective_zero x)
  refine
    ⟨V ∩ e.regularNormalLocus, hV.inter e.isOpen_regularNormalLocus, ?_,
      hInj.mono Set.inter_subset_left, ?_⟩
  · intro v hv
    refine ⟨hsV hv, ?_⟩
    obtain ⟨x, rfl⟩ := hv
    exact e.isLocalDiffeomorphAt_normalDisplacement_zero x
  · intro v
    exact v.property.2

/-- The normal neighborhood's image is open. -/
theorem NativeEuclideanEmbedding.isOpen_normalNeighborhood_image {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    {U : Set e.NormalBundle} (hU : IsOpen U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U) :
    IsOpen (e.normalDisplacement '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hv, rfl⟩
  rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hv]
  exact Filter.image_mem_map (hU.mem_nhds hv)

/-- The normal bundle is nonempty. -/
theorem NativeEuclideanEmbedding.normalBundle_nonempty {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [Nonempty M] : Nonempty e.NormalBundle :=
  ⟨Bundle.zeroSection e.NormalModel e.NormalSpace (Classical.choice ‹Nonempty M›)⟩

attribute [local instance] NativeEuclideanEmbedding.normalBundle_nonempty in
/-- The normal neighborhood is equivalent to its image. -/
noncomputable def NativeEuclideanEmbedding.normalNeighborhoodEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [Nonempty M] {U : Set e.NormalBundle}
    (hinj : Set.InjOn e.normalDisplacement U) :
    PartialEquiv e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  hinj.toPartialEquiv e.normalDisplacement U

attribute [local instance] NativeEuclideanEmbedding.normalBundle_nonempty in
/-- The normal neighborhood inverse is smooth. -/
theorem NativeEuclideanEmbedding.contMDiffAt_normalNeighborhood_inverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    [Nonempty M] {U : Set e.NormalBundle} (hU : IsOpen U)
    (hinj : Set.InjOn e.normalDisplacement U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U)
    {y : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hy : y ∈ (e.normalNeighborhoodEquiv hinj).target) :
    ContMDiffAt (𝓡 e.ambientDimension) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ∞
      (e.normalNeighborhoodEquiv hinj).symm y := by
  let p := e.normalNeighborhoodEquiv hinj
  have hx : p.symm y ∈ U := p.map_target hy
  obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
  have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
  have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
  have hφyx : φ.symm y = p.symm y := by
    calc
      φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
      _ = p.symm y := φ.left_inv' hφx
  have hg : ContMDiffAt (𝓡 e.ambientDimension) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ∞ φ.symm y :=
    φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
  have hNU : U ∈ 𝓝 (φ.symm y) := by
    rw [hφyx]
    exact hU.mem_nhds hx
  have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
    filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
    have hfz : e.normalDisplacement (φ.symm z) = z :=
      (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
    exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
  exact hfg.contMDiffAt_iff.mpr hg

attribute [local instance] NativeEuclideanEmbedding.normalBundle_nonempty in
/-- The normal neighborhood as a partial diffeomorphism. -/
noncomputable def NativeEuclideanEmbedding.normalNeighborhoodPartialDiffeomorph
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : NativeEuclideanEmbedding E M) [Nonempty M] {U : Set e.NormalBundle} (hU : IsOpen U)
    (hinj : Set.InjOn e.normalDisplacement U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U) :
    PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) e.NormalBundle
      (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
    where
  toPartialEquiv := e.normalNeighborhoodEquiv hinj
  open_source := hU
  open_target := e.isOpen_normalNeighborhood_image hU hloc
  contMDiffOn_toFun := e.contMDiff_normalDisplacement.contMDiffOn
  contMDiffOn_invFun := fun _ hy ↦
    (e.contMDiffAt_normalNeighborhood_inverse hU hinj hloc hy).contMDiffWithinAt

attribute [local instance] NativeEuclideanEmbedding.normalBundle_nonempty in
/-- A tubular neighborhood of the embedding exists. -/
theorem NativeEuclideanEmbedding.exists_tubularNeighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    [Nonempty M] [CompactSpace M] :
    ∃ Φ :
      PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
      Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace) ⊆ Φ.source ∧
        (Φ : e.NormalBundle → EuclideanSpace ℝ (Fin e.ambientDimension)) = e.normalDisplacement ∧
          Set.range e.toFun ⊆ Φ.target := by
  obtain ⟨U, hU, hzero, hinj, hloc⟩ := e.exists_injective_normalNeighborhood
  let Φ := e.normalNeighborhoodPartialDiffeomorph hU hinj hloc
  refine ⟨Φ, hzero, rfl, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have hy := Φ.map_source' hx
  simpa only [Φ, normalNeighborhoodPartialDiffeomorph, normalNeighborhoodEquiv,
    Set.InjOn.toPartialEquiv, Set.BijOn.toPartialEquiv, e.normalDisplacement_zero] using hy

/-- A smooth retraction onto the embedded submanifold. -/
structure NativeEuclideanEmbedding.SmoothRetraction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) where
  domain : Set (EuclideanSpace ℝ (Fin e.ambientDimension))
  open_domain : IsOpen domain
  contains : Set.range e.toFun ⊆ domain
  toFun : EuclideanSpace ℝ (Fin e.ambientDimension) → M
  smooth : ContMDiffOn (𝓡 e.ambientDimension) 𝓘(ℝ, E) ∞ toFun domain
  retract : ∀ x, toFun (e.toFun x) = x

/-- A smooth retraction exists. -/
theorem NativeEuclideanEmbedding.nonempty_smoothRetraction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    [CompactSpace M] [Nonempty M] : Nonempty e.SmoothRetraction := by
  obtain ⟨Φ, hzero, hΦ, hrange⟩ := e.exists_tubularNeighborhood
  refine
    ⟨⟨Φ.target, Φ.open_target, hrange, fun y => (Φ.symm y).proj,
        (Bundle.contMDiff_proj e.NormalSpace).comp_contMDiffOn Φ.contMDiffOn_invFun, ?_⟩⟩
  intro x
  have hx : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have heq : Φ (Bundle.zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
    rw [hΦ, e.normalDisplacement_zero]
  have hinv := Φ.left_inv' hx
  rw [heq] at hinv
  exact congrArg Bundle.TotalSpace.proj hinv

/-- The retraction's derivative composed with the embedding is the identity. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.mfderiv_retract_comp {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) (x : M) :
    (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)).comp
        (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun x) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  have hr : r.toFun ∘ e.toFun = id := funext r.retract
  have hd :=
    mfderiv_comp x
      ((r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
        (by simp))
      (e.smooth.mdifferentiableAt (by simp))
  rw [hr, mfderiv_id] at hd
  exact hd.symm

/-- The retraction differentiates the embedding to the identity. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.embedding_derivative_retract {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {x : M}
    {v : EuclideanSpace ℝ (Fin e.ambientDimension)} (hv : v ∈ e.tangentImage x) :
    (mvfderiv 𝓘(ℝ, E) e.toFun x)
        ((mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)) v) =
      v := by
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun A => A w) (r.mfderiv_retract_comp x)
  exact congrArg (mvfderiv 𝓘(ℝ, E) e.toFun x) h

/-- An embedded field is smooth. -/
theorem NativeEuclideanEmbedding.contMDiff_embeddedField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) (𝓡 e.ambientDimension) ∞ (fun x => mvfderiv 𝓘(ℝ, E) e.toFun x (V x)) := by
  have ht := (e.smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  have hp :=
    (contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓡 e.ambientDimension) (n := ∞)).comp ht
  rw [← modelWithCornersSelf_prod] at hp
  convert contDiff_snd.contMDiff.comp hp using 1 <;> rfl

/-! ### Transverse level coordinates -/

/-- The displacement of a regular level set along the flow. -/
def RegularLevel.levelDisplacement {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (z : { x : M // f x = b } × ℝ) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun z.1 + z.2 • mvfderiv 𝓘(ℝ, E) e.toFun z.1 (V z.1)

/-- The domain of transverse level coordinates. -/
def RegularLevel.transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Set ({ x : M // f x = b } × ℝ) :=
  levelDisplacement V ⁻¹' r.domain

/-- The transverse coordinates of a regular level set. -/
def RegularLevel.transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : ({ x : M // f x = b } × ℝ) → M :=
  r.toFun ∘ levelDisplacement V

/-- The transverse coordinates at time zero. -/
theorem RegularLevel.transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    transverseCoordinates r V (x, 0) = x := by
  simp only [transverseCoordinates, Function.comp_apply, levelDisplacement, zero_smul, add_zero]
  exact r.retract x

/-- Zero lies in the transverse coordinate domain. -/
theorem RegularLevel.zero_mem_transverseCoordinateDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    (x, 0) ∈ transverseCoordinateDomain r V := by
  change e.toFun x + (0 : ℝ) • _ ∈ r.domain
  simp only [zero_smul, add_zero]
  exact r.contains ⟨x, rfl⟩

/-- The level displacement is smooth. -/
theorem RegularLevel.contMDiff_levelDisplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) (𝓡 e.ambientDimension) ∞
      (levelDisplacement (e := e) (f := f) (b := b) V) := by
  let _ := chartedSpace hf hreg
  have hi :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun z : { x : M // f x = b } × ℝ => (z.1 : M)) :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst
  have hfirst := e.smooth.comp hi
  have hfield := (e.contMDiff_embeddedField hV).comp hi
  have htime :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (Prod.snd : { x : M // f x = b } × ℝ → ℝ) :=
    contMDiff_snd
  exact hfirst.add (htime.smul hfield)

/-- The transverse coordinate domain is open. -/
theorem RegularLevel.isOpen_transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    IsOpen (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact r.open_domain.preimage (contMDiff_levelDisplacement (e := e) V hf hreg hV).continuous

/-- The transverse coordinates are smooth on their domain. -/
theorem RegularLevel.contMDiffOn_transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact
    r.smooth.comp (contMDiff_levelDisplacement (e := e) V hf hreg hV).contMDiffOn (fun _ hz => hz)

/-- The transverse coordinates' derivative in time at zero. -/
theorem RegularLevel.mfderiv_transverseCoordinates_time_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0 =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (V x) := by
  let A := mvfderiv 𝓘(ℝ, E) e.toFun (x : M) (V x)
  let line : ℝ → EuclideanSpace ℝ (Fin e.ambientDimension) := fun t => e.toFun x + t • A
  have hline : HasFDerivAt line ((ContinuousLinearMap.id ℝ ℝ).smulRight A) 0 :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight A).hasFDerivAt.const_add (e.toFun x)
  have hzero : line 0 = e.toFun x := by simp [line]
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (line 0) := by
    rw [hzero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
        (by simp)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (r.toFun ∘ line) 0 = _
  rw [mfderiv_comp 0 hr hline.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, hline.fderiv,
    hzero]
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)
  change R (t • A) = t • (V x : E)
  rw [map_smul]
  congr 1
  exact congrArg (fun L => L (V x)) (r.mfderiv_retract_comp (x : M))

/-- The transverse coordinates' derivative at zero. -/
theorem RegularLevel.mfderiv_transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V) (x, 0) =
      transverseTangentMap hf hreg x (V x) := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hbase : (fun y : { x : M // f x = b } => transverseCoordinates r V (y, 0)) = Subtype.val :=
    funext (transverseCoordinates_zero r V)
  apply ContinuousLinearMap.ext
  intro w
  rw [mfderiv_prod_eq_add_apply (hs.mdifferentiableAt (by simp)), hbase,
    mfderiv_transverseCoordinates_time_zero r V x]
  rfl

/-- The transverse coordinates are a local diffeomorphism at zero. -/
theorem RegularLevel.isLocalDiffeomorphAt_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    letI := chartedSpace hf hreg
    IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (x, 0) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  have hs := contMDiffOn_transverseCoordinates r V hf hreg hV
  have hi :
    (mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V)
        (x, 0)).IsInvertible := by
    rw [mfderiv_transverseCoordinates_zero r V hf hreg hV x]
    let A := transverseTangentMap hf hreg x (V x)
    exact
      ⟨(LinearEquiv.ofBijective A.toLinearMap
            (bijective_transverseTangentMap hf hreg x (V x) hunit)).toContinuousLinearEquiv,
        rfl⟩
  exact
    isLocalDiffeomorphAt_between_manifolds
      (isOpen_transverseCoordinateDomain r V hf hreg hV)
      (zero_mem_transverseCoordinateDomain r V x) hs hi

/-- The height along the transverse coordinates differentiates to one. -/
theorem RegularLevel.hasDerivAt_height_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    HasDerivAt (fun t : ℝ => f (transverseCoordinates r V (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) 0 :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have hcurve := ((hs.comp 0 hpair).mdifferentiableAt (by simp)).hasMFDerivAt
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0) at hcurve
  rw [mfderiv_transverseCoordinates_time_zero r V x] at hcurve
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0 hcurve
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) = L := by
    rw [transverseCoordinates_zero r V x]
    rfl
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) (t • (V x : E)) =
      t • (1 : ℝ)
  exact
    (congrArg (fun T : E →L[ℝ] ℝ => T (t • (V x : E))) hd).trans
      ((L.map_smul t (V x)).trans (congrArg (fun a : ℝ => t • a) hunit))

/-- The star projection onto the orthogonal complement. -/
theorem DiskFraming.starProjection_orthogonal_inf_eq_sub {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {U V : Submodule ℝ F} (h : U ≤ V) :
    (Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection := by
  ext x
  change (Uᗮ ⊓ V).starProjection x = V.starProjection x - U.starProjection x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨?_, V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))⟩
    rw [← U.ker_starProjection]
    change U.starProjection (V.starProjection x - U.starProjection x) = 0
    rw [map_sub]
    have hc : U.starProjection (V.starProjection x) = U.starProjection x :=
      congrArg (fun A : F →L[ℝ] F => A x) (Submodule.starProjection_comp_starProjection_of_le h)
    rw [hc, Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x), sub_self]
  · have h₁ : x - V.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_right (V.sub_starProjection_mem_orthogonal x)
    have h₂ : U.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_left
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))
    convert (Uᗮ ⊓ V)ᗮ.add_mem h₁ h₂ using 1
    abel

/-! ### The disk normal bundle -/

/-- The tangent image of a disk under the embedding derivative. -/
def NativeEuclideanEmbedding.diskTangentImage {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (fderiv ℝ (e.toFun ∘ f) x).range

/-- The normal space of the disk embedding. -/
def NativeEuclideanEmbedding.diskNormalSpace {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.diskTangentImage f x)ᗮ ⊓ e.tangentImage (f x)

/-- The derivative of the composed embedding. -/
theorem NativeEuclideanEmbedding.fderiv_comp_eq {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    fderiv ℝ (e.toFun ∘ f) x =
      (mvfderiv 𝓘(ℝ, E) e.toFun (f x)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp x (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

/-- The disk tangent image is contained in the tangent space. -/
theorem NativeEuclideanEmbedding.diskTangentImage_le {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    e.diskTangentImage f x ≤ e.tangentImage (f x) := by
  rw [diskTangentImage, e.fderiv_comp_eq hf x]
  exact LinearMap.range_comp_le_range _ _

/-- The composed derivative is injective. -/
theorem NativeEuclideanEmbedding.injective_fderiv_comp {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Function.Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  rw [e.fderiv_comp_eq hf x]
  exact (e.injective_mvfderiv (f x)).comp hi

/-- The disk tangent and normal ranks sum to the dimension. -/
theorem NativeEuclideanEmbedding.finrank_diskTangent_add_normal {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) = Module.finrank ℝ E := by
  have hd : Module.finrank ℝ (e.diskTangentImage f x) = Module.finrank ℝ D :=
    LinearMap.finrank_range_of_inj (e.injective_fderiv_comp hf hi)
  calc
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) =
        Module.finrank ℝ (e.diskTangentImage f x) + Module.finrank ℝ (e.diskNormalSpace f x) :=
      congrArg (fun n => n + Module.finrank ℝ (e.diskNormalSpace f x)) hd.symm
    _ = Module.finrank ℝ (e.tangentImage (f x)) :=
      (Submodule.finrank_add_inf_finrank_orthogonal (e.diskTangentImage_le hf x))
    _ = Module.finrank ℝ E := e.finrank_tangentImage (f x)

/-- The projection onto the disk normal space. -/
def NativeEuclideanEmbedding.diskNormalProjection {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)
    (f : D → M) (x : D) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.tangentProjection (f x) - gramProjection (fderiv ℝ (e.toFun ∘ f) x)

/-- The disk normal projection computes the orthogonal component. -/
theorem NativeEuclideanEmbedding.diskNormalProjection_eq {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    (e : NativeEuclideanEmbedding E M) {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {x : D} (hi : Function.Injective (fderiv ℝ (e.toFun ∘ f) x)) :
    e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  rw [diskNormalProjection, gramProjection_eq_starProjection _ hi]
  exact (DiskFraming.starProjection_orthogonal_inf_eq_sub (e.diskTangentImage_le hf x)).symm

/-- The disk normal projection is smooth. -/
theorem NativeEuclideanEmbedding.contDiffOn_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) :
    ContDiffOn ℝ ∞ (e.diskNormalProjection f)
      {x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)} := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  have hT : ContDiff ℝ ∞ (fun x => e.tangentProjection (f x)) :=
    (e.contMDiff_tangentProjection.comp hf).contDiff
  intro x hx
  have hp : ContDiffAt ℝ ∞ (e.diskNormalProjection f) x :=
    hT.contDiffAt.sub (contMDiffAt_gramProjection hd.contMDiff.contMDiffAt hx).contDiffAt
  exact hp.contDiffWithinAt

/-- An open domain for the disk normal projection exists. -/
theorem NativeEuclideanEmbedding.exists_open_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    ∃ U : Set D,
      IsOpen U ∧
        K ⊆ U ∧
          ContDiffOn ℝ ∞ (e.diskNormalProjection f) U ∧
            ∀ x ∈ U, e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  refine
    ⟨{x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)},
      ContinuousLinearMap.isOpen_injective.preimage hd.continuous, fun x hx =>
      e.injective_fderiv_comp hf (hi x hx), e.contDiffOn_diskNormalProjection hf, ?_⟩
  exact fun _ hx => e.diskNormalProjection_eq hf hx

/-! ### Smooth range transport -/

/-- Two disks admit a smooth transport of ranges on a set. -/
structure DiskFraming.SmoothRangeTransportOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E)
    (P Q : E → F →L[ℝ] F) where
  toFun : E → F →L[ℝ] F
  neighborhood : Set E
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  smooth : ContDiffOn ℝ ∞ toFun neighborhood
  invertible : ∀ x ∈ K, (toFun x).IsInvertible
  intertwines : ∀ x ∈ K, Q x * toFun x = toFun x * P x

/-- Range transport is reflexive. -/
def DiskFraming.SmoothRangeTransportOn.refl {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E) (P : E → F →L[ℝ] F) :
    DiskFraming.SmoothRangeTransportOn K P P
    where
  toFun _ := 1
  neighborhood := Set.univ
  open_neighborhood := isOpen_univ
  contains := Set.subset_univ _
  smooth := contDiffOn_const
  invertible _ _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines _ _ := by rw [mul_one, one_mul]

/-- Range transport is transitive. -/
def DiskFraming.SmoothRangeTransportOn.trans {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q R : E → F →L[ℝ] F}
    (a : DiskFraming.SmoothRangeTransportOn K P Q)
    (b : DiskFraming.SmoothRangeTransportOn K Q R) :
    DiskFraming.SmoothRangeTransportOn K P R
    where
  toFun x := b.toFun x * a.toFun x
  neighborhood := a.neighborhood ∩ b.neighborhood
  open_neighborhood := a.open_neighborhood.inter b.open_neighborhood
  contains := fun _ hx => ⟨a.contains hx, b.contains hx⟩
  smooth := (b.smooth.mono Set.inter_subset_right).clm_comp (a.smooth.mono Set.inter_subset_left)
  invertible x hx := (b.invertible x hx).comp (a.invertible x hx)
  intertwines x
    hx := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x := (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x hx]
      _ = b.toFun x * (Q x * a.toFun x) := (mul_assoc _ _ _)
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x hx]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

/-- Range transport is symmetric. -/
def DiskFraming.SmoothRangeTransportOn.symm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    [CompleteSpace F] (a : DiskFraming.SmoothRangeTransportOn K P Q) :
    DiskFraming.SmoothRangeTransportOn K Q P
    where
  toFun x := (a.toFun x).inverse
  neighborhood := a.neighborhood ∩ {x | (a.toFun x).IsInvertible}
  open_neighborhood :=
    a.smooth.continuousOn.isOpen_inter_preimage a.open_neighborhood ContinuousLinearEquiv.isOpen
  contains := fun x hx => ⟨a.contains hx, a.invertible x hx⟩
  smooth := by
    intro x hx
    exact
      (hx.2.contDiffAt_map_inverse.comp x
          (a.smooth.contDiffAt (a.open_neighborhood.mem_nhds hx.1))).contDiffWithinAt
  invertible x hx := (a.invertible x hx).inverse
  intertwines x
    hx := by
    apply ContinuousLinearMap.ext
    intro v
    change P x ((a.toFun x).inverse v) = (a.toFun x).inverse (Q x v)
    apply (a.invertible x hx).injective
    rw [(a.invertible x hx).self_apply_inverse]
    have h := congrArg (fun L : F →L[ℝ] F => L ((a.toFun x).inverse v)) (a.intertwines x hx)
    change Q x (a.toFun x ((a.toFun x).inverse v)) = a.toFun x (P x ((a.toFun x).inverse v)) at h
    rw [(a.invertible x hx).self_apply_inverse] at h
    exact h.symm

/-- Range transport maps the range. -/
theorem DiskFraming.SmoothRangeTransportOn.map_range {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (a : DiskFraming.SmoothRangeTransportOn K P Q) (x : E) (hx : x ∈ K) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin :
    (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x hx).symm
  rw [hlin]
  exact
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (a.invertible x hx).surjective)

/-- Projections give a range transport. -/
def DiskFraming.SmoothRangeTransportOn.ofProjections {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hQ : ∀ x ∈ K, IsIdempotentElem (Q x)) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hKV : K ⊆ V) (hsP : ContDiffOn ℝ ∞ P U)
    (hsQ : ContDiffOn ℝ ∞ Q V)
    (hinv : ∀ x ∈ K, (projectionIntertwiner (P x) (Q x)).IsInvertible) :
    DiskFraming.SmoothRangeTransportOn K P Q
    where
  toFun x := projectionIntertwiner (P x) (Q x)
  neighborhood := U ∩ V
  open_neighborhood := hU.inter hV
  contains := fun _ hx => ⟨hKU hx, hKV hx⟩
  smooth :=
    ((hsQ.mono Set.inter_subset_right).clm_comp (hsP.mono Set.inter_subset_left)).add
      ((contDiffOn_const.sub (hsQ.mono Set.inter_subset_right)).clm_comp
        (contDiffOn_const.sub (hsP.mono Set.inter_subset_left)))
  invertible := hinv
  intertwines x hx := projectionIntertwiner_intertwines (P x) (Q x) (hP x hx) (hQ x hx)

/-- An open property on a compact set holds on a neighborhood. -/
theorem isOpen_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {R : X → Y → Prop} (ho : IsOpen {p : X × Y | R p.1 p.2}) :
    IsOpen {x | ∀ y, R x y} := by
  have hclosed := isClosedMap_fst_of_compactSpace _ ho.isClosed_compl
  have heq : {x | ∀ y, R x y} = (Prod.fst '' {p : X × Y | ¬R p.1 p.2})ᶜ := by
    ext x
    constructor
    · rintro h ⟨⟨x', y⟩, hn, he⟩
      change x' = x at he
      subst x'
      exact hn (h y)
    · intro h y
      by_contra hn
      exact h ⟨(x, y), hn, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

/-- The domain where a homotopy transports the range. -/
def homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (s : T) : Set T :=
  {t | ∀ x, (projectionIntertwiner (P s x) (P t x)).IsInvertible}

/-- Membership in the homotopy transport domain. -/
theorem mem_homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (hP : ∀ t x, IsIdempotentElem (P t x))
    (s : T) : s ∈ homotopyTransportDomain P s := by
  intro x
  rw [projectionIntertwiner_self _ (hP s x)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

/-- The homotopy transport domain is open. -/
theorem isOpen_continuousHomotopyTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {M T : Type*} [TopologicalSpace M] [CompactSpace M]
    [TopologicalSpace T] (P : T → M → F →L[ℝ] F) (hc : Continuous (fun p : T × M ↦ P p.1 p.2))
    (s : T) : IsOpen (homotopyTransportDomain P s) := by
  have hp : Continuous (fun p : T × M ↦ P s p.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  have hr : Continuous (fun p : T × M ↦ projectionIntertwiner (P s p.2) (P p.1 p.2)) :=
    (hc.clm_comp hp).add ((continuous_const.sub hc).clm_comp (continuous_const.sub hp))
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact isOpen_forall_compact (hi.preimage hr)

/-- The transport-on class is open. -/
theorem DiskFraming.isOpen_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  have hdom := isOpen_continuousHomotopyTransportDomain R hc t
  have ht := mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds ht)
  intro u hu
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ⟨a.trans
        (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
          (fun x hx => hu ⟨x, hx⟩))⟩

/-- The complement of the transport class is open. -/
theorem DiskFraming.isOpen_compl_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | ¬Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hdom := isOpen_continuousHomotopyTransportDomain R hc t
  have htmem := mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds htmem)
  rintro u hu ⟨a⟩
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ht
      ⟨a.trans
          (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
              (fun x hx => hu ⟨x, hx⟩)).symm⟩

/-- A homotopy gives a smooth range transport. -/
theorem DiskFraming.nonempty_smoothRangeTransportOn_of_homotopy {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) [PreconnectedSpace T]
    (s t : T) : Nonempty (SmoothRangeTransportOn K (P s) (P t)) := by
  let C : Set T := {u | Nonempty (SmoothRangeTransportOn K (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, Set.compl_ofPred, Classical.not_not] using
      (isOpen_compl_transportOnClass hK P hP hc hs s).isClosed_compl
  have hclopen : IsClopen C := ⟨hclosed, isOpen_transportOnClass hK P hP hc hs s⟩
  have hall : C = Set.univ := hclopen.eq_univ ⟨s, ⟨SmoothRangeTransportOn.refl K (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact Set.mem_univ t
  exact ht

/-- A range transport exists on a star-convex set. -/
theorem DiskFraming.nonempty_transportOn_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    Nonempty (SmoothRangeTransportOn K (fun _ => P 0) P) := by
  let Q (t : unitInterval) (x : E) := P ((t : ℝ) • x)
  have hQ : ∀ t x, x ∈ K → IsIdempotentElem (Q t x) := fun t x hx =>
    hP _ (hstar.smul_mem hx t.property.1 t.property.2)
  have hmul : Continuous (fun q : unitInterval × K => (q.1 : ℝ) • (q.2 : E)) :=
    (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun q : unitInterval × K => Q q.1 q.2.1) :=
    hs.continuousOn.comp_continuous hmul
      (fun q => hKU (hstar.smul_mem q.2.property q.1.property.1 q.1.property.2))
  have hslice : ∀ t, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ ∞ (Q t) V := by
    intro t
    let V : Set E := (fun x : E => (t : ℝ) • x) ⁻¹' U
    have hV : IsOpen V := hU.preimage (continuous_const.smul continuous_id)
    have hKV : K ⊆ V := fun x hx => hKU (hstar.smul_mem hx t.property.1 t.property.2)
    exact ⟨V, hV, hKV, hs.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => hx)⟩
  have hstart : Q 0 = fun _ => P 0 := by
    funext x
    change P ((0 : ℝ) • x) = P 0
    rw [zero_smul]
  have hend : Q 1 = P := by
    funext x
    change P ((1 : ℝ) • x) = P x
    rw [one_smul]
  simpa only [hstart, hend] using
    nonempty_smoothRangeTransportOn_of_homotopy hK Q hQ hc hslice 0 1

/-- A smooth frame exists near a star-convex set. -/
theorem DiskFraming.exists_smooth_frame_near_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : E → (P 0).range →L[ℝ] F,
            ContDiffOn ℝ ∞ A V ∧ ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨a⟩ := nonempty_transportOn_starConvex hK hstar hU hKU P hP hs
  let A (x : E) : (P 0).range →L[ℝ] F := (a.toFun x).comp (P 0).range.subtypeL
  refine
    ⟨a.neighborhood, a.open_neighborhood, a.contains, A, a.smooth.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨(a.invertible x hx).injective.comp Subtype.val_injective, ?_⟩
  change ((a.toFun x).toLinearMap.comp (P 0).range.subtype).range = (P x).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact a.map_range x hx

/-- A smooth frame exists on a neighborhood of a closed ball. -/
theorem DiskFraming.exists_smooth_frame_on_neighborhood_closedBall {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : E) 1 ⊆ U) (P : E → F →L[ℝ] F)
    (hP : ∀ x ∈ U, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        Metric.closedBall (0 : E) 1 ⊆ V ∧
          V ⊆ U ∧
            ∃ A : E → (P 0).range →L[ℝ] F,
              ContDiffOn ℝ ∞ A V ∧
                ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open hU hballU
  have hbU : Metric.closedBall (0 : E) (δ + 1) ⊆ U := by
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hthick
  have hr : 1 < δ + 1 := by linarith
  obtain ⟨W, hW, hbW, A, hA, hArange⟩ :=
    exists_smooth_frame_near_starConvex (ProperSpace.isCompact_closedBall (0 : E) (δ + 1))
      ((convex_closedBall (0 : E) (δ + 1)).starConvex (Metric.mem_closedBall_self (by linarith)))
      hU hbU P (fun x hx => hP x (hbU hx)) hs
  refine
    ⟨W ∩ Metric.ball 0 (δ + 1), hW.inter Metric.isOpen_ball, ?_, ?_, A,
      hA.mono Set.inter_subset_left, ?_⟩
  · intro x hx
    exact
      ⟨hbW (Metric.closedBall_subset_closedBall hr.le hx), Metric.closedBall_subset_ball hr hx⟩
  · exact fun _ hx => hbU (Metric.ball_subset_closedBall hx.2)
  · exact fun x hx => hArange x (Metric.ball_subset_closedBall hx.2)

/-- A smooth normal frame exists near a closed ball. -/
theorem NativeEuclideanEmbedding.exists_smooth_normalFrame_near_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        Metric.closedBall (0 : D) 1 ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ U, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x hx]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, hVU, A, hA, hAi⟩ :=
    DiskFraming.exists_smooth_frame_on_neighborhood_closedBall hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hz : (0 : D) ∈ Metric.closedBall (0 : D) 1 := Metric.mem_closedBall_self zero_le_one
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : Module.finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : Module.finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg
          (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) => Module.finrank ℝ S)
          hr).trans
      hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine
    ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap, hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hVU hx), Submodule.range_starProjection]

/-! ### Disk framings and displacement -/

/-- The splitting of the ambient space into range and normal parts. -/
def DiskFraming.normalSplitEquiv {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F) (A : Z →L[ℝ] F)
    {V : Submodule ℝ F} (hL : Function.Injective L) (hA : Function.Injective A)
    (hLV : L.range ≤ V) (hAr : A.range = L.rangeᗮ ⊓ V) : (D × Z) ≃L[ℝ] V := by
  let a : D × Z →ₗ[ℝ] F := L.toLinearMap.coprod A.toLinearMap
  have har : a.range = V := by
    rw [LinearMap.range_coprod, hAr]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLV
  have had : Disjoint L.range A.range := by
    rw [hAr]
    exact L.range.orthogonal_disjoint.mono_right inf_le_left
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ had,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hA, Submodule.prod_bot]
  let b : D × Z →ₗ[ℝ] V := a.codRestrict V (fun q => har ▸ LinearMap.mem_range_self a q)
  have hbi : Function.Injective b := fun _ _ h => hai (congrArg Subtype.val h)
  have hbs : Function.Surjective b := by
    intro v
    have hv : (v : F) ∈ a.range := har.symm ▸ v.property
    obtain ⟨q, hq⟩ := hv
    exact ⟨q, Subtype.ext hq⟩
  exact (LinearEquiv.ofBijective b ⟨hbi, hbs⟩).toContinuousLinearEquiv

/-- The tangent-plus-normal splitting of the disk embedding. -/
def NativeEuclideanEmbedding.diskTangentNormalEquiv {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (hA : Function.Injective A) (hAr : A.range = e.diskNormalSpace f x) :
    (D × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] e.tangentImage (f x) :=
  DiskFraming.normalSplitEquiv (fderiv ℝ (e.toFun ∘ f) x) A (e.injective_fderiv_comp hf hi)
    hA (e.diskTangentImage_le hf x) hAr

/-- The displacement of a framed disk along the normal frame. -/
def DiskFraming.displacement {D Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F) (p : D × Z) : F :=
  H p.1 + A p.1 p.2

/-- The displacement at zero is the disk point. -/
theorem DiskFraming.displacement_zero {D Z F : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F)
    (x : D) : displacement H A (x, 0) = H x := by simp [displacement]

/-- The displacement is smooth. -/
theorem DiskFraming.contDiffOn_displacement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {V : Set D} (hH : ContDiff ℝ ∞ H)
    (hA : ContDiffOn ℝ ∞ A V) : ContDiffOn ℝ ∞ (displacement H A) (V ×ˢ Set.univ) :=
  (hH.comp contDiff_fst).contDiffOn.add
    ((hA.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply contDiffOn_snd)

/-- The displacement's derivative at zero. -/
theorem DiskFraming.hasFDerivAt_displacement_zero {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {x : D} (hH : ContDiffAt ℝ ∞ H x)
    (hA : ContDiffAt ℝ ∞ A x) :
    HasFDerivAt (displacement H A) ((fderiv ℝ H x).coprod (A x)) (x, 0) := by
  have hfst : HasFDerivAt (Prod.fst : D × Z → D) (ContinuousLinearMap.fst ℝ D Z) (x, 0) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : D × Z → Z) (ContinuousLinearMap.snd ℝ D Z) (x, 0) :=
    hasFDerivAt_snd
  have h₁ :
    HasFDerivAt (fun p : D × Z => H p.1) ((fderiv ℝ H x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hH.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h₂ :
    HasFDerivAt (fun p : D × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hA.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h := h₁.add (h₂.clm_apply hsnd)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  change fderiv ℝ H x q.1 + (A x q.2 + (fderiv ℝ A x q.1) 0) = fderiv ℝ H x q.1 + A x q.2
  rw [map_zero, add_zero]

/-! ### Disk coordinates of a retraction -/

/-- Disk coordinates of a smooth retraction. -/
def NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) :
    D × EuclideanSpace ℝ (Fin n) → M :=
  r.toFun ∘ DiskFraming.displacement (e.toFun ∘ f) A

/-- The domain of the disk coordinates. -/
def NativeEuclideanEmbedding.SmoothRetraction.diskCoordinateDomain {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (V : Set D) : Set (D × EuclideanSpace ℝ (Fin n)) :=
  (V ×ˢ Set.univ) ∩ DiskFraming.displacement (e.toFun ∘ f) A ⁻¹' r.domain

/-- The disk coordinates at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates_zero {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) (x : D) :
    r.diskCoordinates f A (x, 0) = f x := by
  rw [diskCoordinates, Function.comp_apply, DiskFraming.displacement_zero]
  exact r.retract (f x)

/-- The disk coordinate domain is open. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isOpen_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) : IsOpen (r.diskCoordinateDomain f A V) := by
  have hc :=
    (DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).continuousOn
  exact hc.isOpen_inter_preimage (hV.prod isOpen_univ) r.open_domain

/-- Zero lies in the disk coordinate domain. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.zero_mem_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ}
    (f : D → M) (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    {V : Set D} {x : D} (hx : x ∈ V) : (x, 0) ∈ r.diskCoordinateDomain f A V := by
  refine ⟨⟨hx, Set.mem_univ _⟩, ?_⟩
  change DiskFraming.displacement (e.toFun ∘ f) A (x, 0) ∈ r.domain
  rw [DiskFraming.displacement_zero]
  exact r.contains ⟨f x, rfl⟩

/-- The disk coordinates are smooth. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_diskCoordinates
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hA : ContDiffOn ℝ ∞ A V) :
    ContMDiffOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (r.diskCoordinateDomain f A V) :=
  r.smooth.comp
    ((DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hp => hp.2)

/-- The disk coordinates' derivative at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) :
    mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A) (x, 0) =
      (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f x))).comp
        ((fderiv ℝ (e.toFun ∘ f) x).coprod (A x)) := by
  have hd :=
    DiskFraming.hasFDerivAt_displacement_zero (e.smooth.comp hf).contDiff.contDiffAt hA
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (DiskFraming.displacement (e.toFun ∘ f) A (x, 0)) := by
    rw [DiskFraming.displacement_zero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f x, rfl⟩))).mdifferentiableAt
        (by simp)
  rw [diskCoordinates, mfderiv_comp (x, 0) hr hd.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hd.fderiv, DiskFraming.displacement_zero]
  rfl

/-- The disk coordinates' derivative is invertible at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isInvertible_mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hAi : Function.Injective (A x)) (hAr : (A x).range = e.diskNormalSpace f x) :
    (mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A)
        (x, 0)).IsInvertible := by
  let L := e.diskTangentNormalEquiv hf hi (A x) hAi hAr
  let T := L.trans (e.tangentImageEquiv (f x)).symm
  refine ⟨T, ?_⟩
  apply ContinuousLinearMap.ext
  intro q
  rw [r.mfderiv_diskCoordinates_zero hf hA]
  apply e.injective_mvfderiv (f x)
  have hleft := congrArg Subtype.val ((e.tangentImageEquiv (f x)).apply_symm_apply (L q))
  exact hleft.trans (r.embedding_derivative_retract (L q).property).symm

/-- The disk coordinates are a local diffeomorphism at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isLocalDiffeomorphAt_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) {x : D} (hx : x ∈ V)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (hAi : Function.Injective (A x))
    (hAr : (A x).range = e.diskNormalSpace f x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (x, 0) :=
  isLocalDiffeomorphAt_of_contMDiffOn (r.isOpen_diskCoordinateDomain hf hV hA)
    (r.zero_mem_diskCoordinateDomain f A hx) (r.contMDiffOn_diskCoordinates hf hA)
    (r.isInvertible_mfderiv_diskCoordinates_zero hf (hA.contDiffAt (hV.mem_nhds hx)) hi hAi hAr)

/-- A positive product of closed balls inside an open set exists. -/
theorem DiskFraming.exists_pos_prod_closedBall_subset {D Z : Type*} [TopologicalSpace D]
    [NormedAddCommGroup Z] {K : Set D} {U : Set (D × Z)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ×ˢ {(0 : Z)} ⊆ U) : ∃ ε : ℝ, 0 < ε ∧ K ×ˢ Metric.closedBall (0 : Z) ε ⊆ U := by
  obtain ⟨A, B, -, hB, hKA, hzeroB, hAB⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Z))) hU hKU
  obtain ⟨ε, hε, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds (hzeroB (Set.mem_singleton (0 : Z))))
  refine ⟨ε, hε, ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  exact hAB ⟨hKA hx, hball hz⟩

/-- A disk tubular neighborhood exists. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.exists_diskTubularNeighborhood
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K V : Set D} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hA : ContDiffOn ℝ ∞ A V) (hAi : ∀ x ∈ K, Function.Injective (A x))
    (hAr : ∀ x ∈ K, (A x).range = e.diskNormalSpace f x) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (D × EuclideanSpace ℝ (Fin n))
        M ∞,
      K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Φ.source ∧
        Φ.source ⊆ r.diskCoordinateDomain f A V ∧
          (Φ : D × EuclideanSpace ℝ (Fin n) → M) = r.diskCoordinates f A := by
  have hzeroInj : Set.InjOn (r.diskCoordinates f A) (K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ hxy
    have hv0 : v = 0 := hv
    have hw0 : w = 0 := hw
    subst v
    subst w
    rw [r.diskCoordinates_zero, r.diskCoordinates_zero] at hxy
    exact Prod.ext (hinj hx hy hxy) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))},
      IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
        p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact
      r.isLocalDiffeomorphAt_diskCoordinates_zero hf hV hA (hKV hx) (hi x hx) (hAi x hx)
        (hAr x hx)
  apply
    exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (r.isOpen_diskCoordinateDomain hf hV hA)
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  have hv0 : v = 0 := hv
  subst v
  exact r.zero_mem_diskCoordinateDomain f A (hKV hx)

/-- A tubular neighborhood of an embedded closed ball exists. -/
theorem exists_tubularNeighborhood_in_open_of_embedded_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hinj : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f (Metric.closedBall (0 : D) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          Metric.closedBall (0 : D) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            (∀ x ∈ Metric.closedBall (0 : D) 1, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ := e.exists_smooth_normalFrame_near_closedBall hf hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf (ProperSpace.isCompact_closedBall 0 1) hV hKV hinj hi hA
      (fun x hx => (hframe x (hKV hx)).1) (fun x hx => (hframe x (hKV hx)).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W := fun p =>
    ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset (ProperSpace.isCompact_closedBall 0 1)
      Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x _
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

/-! ### The height collar -/

/-- A unit-height field exists near a regular level. -/
theorem RegularLevel.exists_unitHeightField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x : { x : M // f x = b }, mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1 := by
  have hband : ∀ x, f x ∈ Set.Icc b b → x ∉ ManifoldMorse.criticalPoints E f := fun x hx =>
    hreg x (le_antisymm hx.2 hx.1)
  obtain ⟨φ, W, -, -, hW, hφ, V, hV, hheight⟩ :=
    FlowConstruction.exists_regularBandField hf hband
  refine ⟨V, hV, ?_⟩
  intro x
  exact (hheight x).trans (hφ (hW (by rw [x.property]; exact ⟨le_rfl, le_rfl⟩)))

/-- A transverse collar of a regular level exists. -/
theorem RegularLevel.exists_transverseCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Φ.source ∧
            (∀ x : { x : M // f x = b }, Φ (x, 0) = x) ∧
              ∀ x : { x : M // f x = b }, HasDerivAt (fun t : ℝ => f (Φ (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Nonempty M := Nonempty.map (fun x : { x : M // f x = b } => (x : M)) inferInstance
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hunit⟩ := exists_unitHeightField hf hreg
  let K : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : Set.InjOn (transverseCoordinates r V) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [transverseCoordinates_zero r V x, transverseCoordinates_zero r V y] at hxy
    exact Prod.ext (Subtype.ext hxy) rfl
  have hloc :
    ∀ z ∈ K,
      IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V) z :=
    by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact isLocalDiffeomorphAt_transverseCoordinates_zero r V hf hreg hV x (hunit x)
  have hKD : K ⊆ transverseCoordinateDomain r V := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact zero_mem_transverseCoordinateDomain r V x
  obtain ⟨Φ, hKΦ, -, heq⟩ :=
    exists_partialDiffeomorph_near_compact hK hinj hloc
      (isOpen_transverseCoordinateDomain r V hf hreg hV) hKD
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Φ.open_source hKΦ
  refine ⟨ε, hε, Φ, hsource, ?_, ?_⟩
  · intro x
    exact (congrFun heq (x, 0)).trans (transverseCoordinates_zero r V x)
  · intro x
    have hh : (fun t : ℝ => f (Φ (x, t))) = fun t : ℝ => f (transverseCoordinates r V (x, t)) :=
      funext (fun t => congrArg f (congrFun heq (x, t)))
    rw [hh]
    exact hasDerivAt_height_transverseCoordinates_zero r V hf hreg hV x (hunit x)

/-- A height band inside an open set exists. -/
theorem RegularLevel.exists_heightBand_subset_open {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : X → ℝ} (hg : Continuous g) {a : ℝ} {U : Set X} (hU : IsOpen U)
    (hlevel : ∀ x, g x = a → x ∈ U) : ∃ δ : ℝ, 0 < δ ∧ g ⁻¹' Metric.ball a δ ⊆ U := by
  have hclosed : IsClosed (g '' Uᶜ) := (hU.isClosed_compl.isCompact.image hg).isClosed
  have ha : a ∉ g '' Uᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (hlevel x hxa)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a ha
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra hnot
  exact hball hx ⟨x, hnot, rfl⟩

/-- A height collar of a regular level exists. -/
theorem RegularLevel.exists_heightCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧ ∀ z ∈ Ψ.source, f (Ψ z) = b + z.2 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨ε, hε, Φ, hsource, hzero, hderiv⟩ := exists_transverseCollar hf hreg
  let H : { x : M // f x = b } × ℝ → ℝ := fun z => f (Φ z) - b
  have hH : ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H Φ.source :=
    (hf.comp_contMDiffOn Φ.contMDiffOn_toFun).sub contMDiff_const.contMDiffOn
  have hH0 (x : { x : M // f x = b }) : H (x, 0) = 0 := by
    change f (Φ (x, 0)) - b = 0
    rw [hzero x, x.property, sub_self]
  have hzeroSource (x : { x : M // f x = b }) : (x, 0) ∈ Φ.source :=
    hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
  have hHt (x : { x : M // f x = b }) : HasDerivAt (fun t : ℝ => H (x, t)) 1 0 :=
    (hderiv x).sub_const b
  obtain ⟨χ, hKχ, -, hχ⟩ :=
    CollarHeight.exists_heightChangeChart Φ.open_source hH hH0 hzeroSource hHt
  have hχzero (x : { x : M // f x = b }) : χ (x, 0) = (x, 0) :=
    (congrFun hχ (x, 0)).trans (CollarHeight.heightChange_zero hH0 x)
  have hχtarget (x : { x : M // f x = b }) : (x, 0) ∈ χ.target := by
    rw [← hχzero x]
    exact χ.map_source' (hKχ ⟨Set.mem_univ x, rfl⟩)
  have hχinv (x : { x : M // f x = b }) : χ.symm (x, 0) = (x, 0) := by
    have hh : χ.symm (χ (x, 0)) = (x, 0) := χ.left_inv' (hKχ ⟨Set.mem_univ x, rfl⟩)
    rwa [hχzero x] at hh
  let Ψ := χ.symm.trans Φ
  have hzeroΨ : (Set.univ : Set { x : M // f x = b }) ×ˢ {(0 : ℝ)} ⊆ Ψ.source := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hχtarget x, ?_⟩
    change χ.symm (x, 0) ∈ Φ.source
    rw [hχinv x]
    exact hzeroSource x
  obtain ⟨δ, hδ, hproduct⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Ψ.open_source hzeroΨ
  refine ⟨δ, hδ, Ψ, hproduct, ?_, ?_⟩
  · intro x
    change Φ (χ.symm (x, 0)) = x
    rw [hχinv x, hzero x]
  · intro z hz
    have hheight : H (χ.symm z) = z.2 := by
      calc
        H (χ.symm z) = (χ (χ.symm z)).2 := (congrArg Prod.snd (congrFun hχ (χ.symm z))).symm
        _ = z.2 := congrArg Prod.snd (χ.right_inv' hz.1)
    change f (Φ (χ.symm z)) = b + z.2
    change f (Φ (χ.symm z)) - b = z.2 at hheight
    linarith

/-- A height collar with a prescribed band exists. -/
theorem RegularLevel.exists_heightCollar_with_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧
              (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) ∧ f ⁻¹' Metric.ball b ε ⊆ Ψ.target := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight⟩ := exists_heightCollar hf hreg
  have hlevel : ∀ x, f x = b → x ∈ Ψ.target := by
    intro x hx
    let y : { x : M // f x = b } := ⟨x, hx⟩
    have hmem : Ψ (y, 0) ∈ Ψ.target :=
      Ψ.map_source' (hsource ⟨Set.mem_univ y, Metric.mem_closedBall_self hε.le⟩)
    have hy : Ψ (y, 0) = x := hzero y
    exact hy ▸ hmem
  obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous Ψ.open_target hlevel
  refine ⟨Min.min ε δ, lt_min hε hδ, Ψ, ?_, hzero, hheight, ?_⟩
  · exact fun z hz => hsource ⟨hz.1, Metric.closedBall_subset_closedBall (min_le_left ε δ) hz.2⟩
  · exact fun x hx => hband (Metric.ball_subset_ball (min_le_right ε δ) hx)

/-! ### Small perturbations of the identity -/

/-- The identity plus a small map is injective. -/
theorem SmallPerturbation.injective_id_add {E : Type*} [NormedAddCommGroup E] {u : E → E}
    {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) : Function.Injective (fun x => x + u x) :=
  (AntilipschitzWith.id.add_lipschitzWith hu (by simpa only [inv_one] using hk)).injective

/-- The identity plus a small map is surjective. -/
theorem SmallPerturbation.surjective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Surjective (fun x => x + u x) := by
  intro y
  have hlip : LipschitzWith k (fun x => y - u x) := by
    simpa only [zero_add] using (LipschitzWith.const y).sub hu
  have hc : ContractingWith k (fun x => y - u x) := ⟨hk, hlip⟩
  let x := ContractingWith.fixedPoint (fun x => y - u x) hc
  refine ⟨x, ?_⟩
  have hx : y - u x = x := hc.fixedPoint_isFixedPt.eq
  exact eq_sub_iff_add_eq.mp hx.symm

/-- The identity plus a small map is bijective. -/
theorem SmallPerturbation.bijective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Bijective (fun x => x + u x) :=
  ⟨injective_id_add hu hk, surjective_id_add hu hk⟩

/-- The identity plus a small map has invertible derivative. -/
theorem SmallPerturbation.isInvertible_fderiv_id_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) (x : E) :
    (fderiv ℝ (fun y => y + u y) x).IsInvertible := by
  have hn : ‖fderiv ℝ u x‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hu).trans_lt (show (k : ℝ) < 1 from hk)
  have hnn : ‖fderiv ℝ u x‖₊ < 1 := hn
  have hi : Function.Injective (ContinuousLinearMap.id ℝ E + fderiv ℝ u x) :=
    injective_id_add (fderiv ℝ u x).lipschitz hnn
  have hd : fderiv ℝ (fun y => y + u y) x = ContinuousLinearMap.id ℝ E + fderiv ℝ u x :=
    ((hasFDerivAt_id x).add (hs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  let L :=
    (LinearEquiv.ofInjectiveEndo (ContinuousLinearMap.id ℝ E + fderiv ℝ u x).toLinearMap
        hi).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- The identity plus a small map is a diffeomorphism. -/
def SmallPerturbation.diffeomorphIdAdd {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := by
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => x + u x) := by
    intro x
    apply
      isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_id.add hs).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_id_add hs hu hk x
  exact hloc.diffeomorphOfBijective (bijective_id_add hu hk)

/-- A scaled constant is Lipschitz. -/
theorem SmallPerturbation.lipschitzWith_smul_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {β : E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (a : E) :
    LipschitzWith (k * ‖a‖₊) (fun x => β x • a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β x • a) (β y • a) = ‖β x - β y‖ * ‖a‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul]
    _ ≤ ((k : ℝ) * Dist.dist x y) * ‖a‖ :=
      (mul_le_mul_of_nonneg_right (hβ.dist_le_mul x y) (norm_nonneg a))
    _ = (k * ‖a‖₊ : ℝ≥0) * Dist.dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- The bump translation diffeomorphism. -/
def SmallPerturbation.bumpTranslation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β) (hβ : LipschitzWith k β)
    (a : E) (ha : k * ‖a‖₊ < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphIdAdd (hs.smul contDiff_const) (lipschitzWith_smul_const hβ a) ha

/-- The bump translation computes the shifted point. -/
theorem SmallPerturbation.bumpTranslation_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) (x : E) :
    bumpTranslation hs hβ a ha x = x + β x • a := by
  have h : bumpTranslation hs hβ a ha x = x + β x • a := rfl
  exact h

/-- The bump translation is the identity where the bump vanishes. -/
theorem SmallPerturbation.bumpTranslation_eq_of_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) {x : E} (hx : β x = 0) :
    bumpTranslation hs hβ a ha x = x := by rw [bumpTranslation_apply, hx, zero_smul, add_zero]

/-- A radius for which the bump translation exists. -/
theorem SmallPerturbation.exists_radius_bumpTranslation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} (hs : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
              (∀ x, d x = x + β x • a) ∧ ∀ x ∉ tsupport β, d x = x := by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hreal : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hreal
  refine ⟨bumpTranslation hs hk a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport β hne)

/-! ### Supported diffeomorphisms -/

/-- A diffeomorphism fixed outside a set maps it to itself. -/
theorem SupportedDiffeomorph.mapsTo_of_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : Set.MapsTo d S S := by
  intro x hx
  by_contra hdx
  have heq : d x = x := d.injective (hfix (d x) hdx)
  exact hdx (heq.symm ▸ hx)

/-- The inverse is fixed outside the support. -/
theorem SupportedDiffeomorph.inverse_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : ∀ x ∉ S, d.symm x = x := by
  intro x hx
  apply d.injective
  rw [d.apply_symm_apply, hfix x hx]

/-- The extension of a chart-supported diffeomorphism to the manifold. -/
def SupportedDiffeomorph.extendMap {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) (y : Y) : Y := by classical exact if y ∈ Φ.target then Φ (f (Φ.symm y)) else y

/-- The extension computes the chart diffeomorphism inside the chart. -/
theorem SupportedDiffeomorph.extendMap_of_mem {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) {y : Y} (hy : y ∈ Φ.target) : extendMap Φ f y = Φ (f (Φ.symm y)) := by
  simp only [extendMap, hy, if_pos]

/-- The extension is the identity outside the chart. -/
theorem SupportedDiffeomorph.extendMap_of_notMem {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) (f : X → X) {y : Y} (hy : y ∉ Φ.target) :
    extendMap Φ f y = y := by simp only [extendMap, hy, if_false]

/-- The extension of the identity is the identity. -/
theorem SupportedDiffeomorph.extendMap_id {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (y : Y) : extendMap Φ id y = y := by
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ id hy]
    exact Φ.right_inv' hy
  · exact extendMap_of_notMem Φ id hy

/-- The extension computes in the chart. -/
theorem SupportedDiffeomorph.extendMap_chart {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) {x : X} (hx : x ∈ Φ.source) : extendMap Φ f (Φ x) = Φ (f x) := by
  rw [extendMap_of_mem Φ f (Φ.map_source' hx)]
  exact congrArg (fun z => Φ (f z)) (Φ.left_inv' hx)

/-- The extension lands in the target. -/
theorem SupportedDiffeomorph.extendMap_mem_target {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {f : X → X} (hf : Set.MapsTo f Φ.source Φ.source) {y : Y}
    (hy : y ∈ Φ.target) : extendMap Φ f y ∈ Φ.target := by
  rw [extendMap_of_mem Φ f hy]
  exact Φ.map_source' (hf (Φ.map_target' hy))

/-- The extension left-inverts on the source. -/
theorem SupportedDiffeomorph.extendMap_leftInverse {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) (d : X ≃ X) (hd : Set.MapsTo d Φ.source Φ.source) :
    Function.LeftInverse (extendMap Φ d.symm) (extendMap Φ d) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ d.symm (extendMap_mem_target Φ hd hy), extendMap_of_mem Φ d hy]
    change Φ (d.symm (Φ.invFun (Φ (d (Φ.invFun y))))) = y
    rw [Φ.left_inv' (hd (Φ.map_target' hy)), d.symm_apply_apply]
    exact Φ.right_inv' hy
  · rw [extendMap_of_notMem Φ d hy, extendMap_of_notMem Φ d.symm hy]

/-- The extension is the identity off the image. -/
theorem SupportedDiffeomorph.extendMap_eq_of_notMem_image {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {f : X → X} {K : Set X} (hfix : ∀ x ∉ K, f x = x) {y : Y}
    (hy : y ∉ Φ '' K) : extendMap Φ f y = y := by
  by_cases hyt : y ∈ Φ.target
  · have hback : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [extendMap_of_mem Φ f hyt, hfix _ hback]
    exact Φ.right_inv' hyt
  · exact extendMap_of_notMem Φ f hyt

/-- The extension maps the source to the target. -/
theorem SupportedDiffeomorph.mapsTo_source {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (d : X ≃ X) {K : Set X} (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) :
    Set.MapsTo d Φ.source Φ.source :=
  mapsTo_of_fixed_outside d (fun x hx => hfix x (fun hk => hx (hKΦ hk)))

/-- The extension is smooth. -/
theorem SupportedDiffeomorph.contMDiff_extendMap {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] {f : X → X} (hf : ContMDiff I I ∞ f)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, f x = x)
    (hsource : Set.MapsTo f Φ.source Φ.source) : ContMDiff J J ∞ (extendMap Φ f) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hback := Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource (Φ.map_target' hy)))
    have hs := hforward.comp y (hf.contMDiffAt.comp y hback)
    apply hs.congr_of_eventuallyEq
    filter_upwards [Φ.open_target.mem_nhds hy] with z hz
    exact extendMap_of_mem Φ f hz
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    apply (contMDiffAt_id : ContMDiffAt J J ∞ id y).congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds hnot] with z hz
    exact extendMap_eq_of_notMem_image Φ hfix hz

/-- The extension as a diffeomorphism. -/
def SupportedDiffeomorph.extension {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, d x = x) : Diffeomorph J J Y Y ∞ := by
  have hdi : ∀ x ∉ K, d.symm x = x := inverse_fixed_outside d.toEquiv hfix
  have hdS : Set.MapsTo d Φ.source Φ.source := mapsTo_source Φ d.toEquiv hKΦ hfix
  have hdiS : Set.MapsTo d.symm Φ.source Φ.source := mapsTo_source Φ d.symm.toEquiv hKΦ hdi
  exact
    { toFun := extendMap Φ d
      invFun := extendMap Φ d.symm
      left_inv := extendMap_leftInverse Φ d.toEquiv hdS
      right_inv := extendMap_leftInverse Φ d.symm.toEquiv hdiS
      contMDiff_toFun := contMDiff_extendMap Φ d.contMDiff hK hKΦ hfix hdS
      contMDiff_invFun := contMDiff_extendMap Φ d.symm.contMDiff hK hKΦ hdi hdiS }

/-- The extension computes in the chart. -/
theorem SupportedDiffeomorph.extension_chart {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, d x = x) {x : X} (hx : x ∈ Φ.source) :
    extension Φ d hK hKΦ hfix (Φ x) = Φ (d x) :=
  extendMap_chart Φ d hx

/-- The extension is the identity off the image. -/
theorem SupportedDiffeomorph.extension_eq_of_notMem_image {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) {y : Y} (hy : y ∉ Φ '' K) :
    extension Φ d hK hKΦ hfix y = y :=
  extendMap_eq_of_notMem_image Φ hfix hy

/-- The extension is the identity off the target. -/
theorem SupportedDiffeomorph.extension_eq_of_notMem_target {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) {y : Y}
    (hy : y ∉ Φ.target) : extension Φ d hK hKΦ hfix y = y :=
  extendMap_of_notMem Φ d hy

/-! ### Ambient transport of level sets -/

/-- A large height difference gives the shift inequality. -/
theorem RegularLevel.le_shift_iff_of_abs_sub_ge {u b t ε : ℝ} (ht : |t| < ε)
    (hu : ε ≤ |u - b|) : u ≤ b + t ↔ u ≤ b := by
  by_cases hbelow : u ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hbelow)] at hu
    exact ⟨fun _ => hbelow, fun _ => by linarith [(abs_lt.mp ht).1]⟩
  · have habove : b ≤ u := le_of_not_ge hbelow
    rw [abs_of_nonneg (sub_nonneg.mpr habove)] at hu
    constructor <;> intro hh <;> exfalso <;> linarith [(abs_lt.mp ht).2]

/-- A height collar gives an ambient transport between levels. -/
theorem RegularLevel.exists_ambientTransport_of_heightCollar {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) (ε : ℝ) (hε : 0 < ε) :
    letI := chartedSpace hf hreg
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
      ((Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source) →
        (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) →
          (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) →
            (f ⁻¹' Metric.ball b ε ⊆ Ψ.target) →
              ∃ δ : ℝ,
                0 < δ ∧
                  δ ≤ ε ∧
                    ∃ K : Set M,
                      IsCompact K ∧
                        K ⊆ Ψ.target ∧
                          ∀ t : ℝ,
                            |t| < δ →
                              ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                                (∀ y, y ∉ K → D y = y) ∧
                                  (∀ x : { x : M // f x = b }, D x = Ψ (x, t)) ∧
                                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro Ψ hsource hzero hheight hband
  obtain ⟨β, hβ, hsupp, W, -, hW, -, hβW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {(0 : ℝ)}) (U :=
      Metric.ball (0 : ℝ) ε) isClosed_singleton Metric.isOpen_ball
      (by
        simpa only [Set.singleton_subset_iff] using
          (Metric.mem_ball_self hε : (0 : ℝ) ∈ Metric.ball 0 ε))
  have hβ0 : β 0 = 1 := hβW (hW (Set.mem_singleton 0))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset (isClosed_tsupport β)
      (hsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨η, hη, htranslations⟩ :=
    SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let C : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ tsupport β
  have hC : IsCompact C := isCompact_univ.prod hcompact
  have hCsource : C ⊆ Ψ.source := fun z hz =>
    hsource ⟨hz.1, Metric.ball_subset_closedBall (hsupp hz.2)⟩
  let K : Set M := Ψ '' C
  have hK : IsCompact K :=
    hC.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hKtarget : K ⊆ Ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Ψ.map_source' (hCsource hz)
  refine ⟨Min.min ε η, lt_min hε hη, min_le_left ε η, K, hK, hKtarget, ?_⟩
  intro t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left ε η)
  have htη : ‖t‖ < η := by
    simpa only [Real.norm_eq_abs] using lt_of_lt_of_le ht (min_le_right ε η)
  obtain ⟨d, hd, hdfix⟩ := htranslations t htη
  have hd0 : d 0 = t := by
    rw [hd 0, hβ0]
    simp
  have hdfar (s : ℝ) (hs : ε ≤ s) : d s = s := by
    apply hdfix
    intro hsupps
    have hball : |s| < ε := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsupp hsupps
    rw [abs_of_nonneg (hε.le.trans hs)] at hball
    exact (not_lt_of_ge hs) hball
  have hdmono : StrictMono d := by
    rcases d.contMDiff.continuous.strictMono_of_inj d.injective with hm | ha
    · exact hm
    · have hh := ha (show ε < ε + 1 by linarith)
      rw [hdfar ε le_rfl, hdfar (ε + 1) (by linarith)] at hh
      linarith
  let P := (Diffeomorph.refl 𝓘(ℝ, Model E) { x : M // f x = b } ∞).prodCongr d
  have hPfix : ∀ z, z ∉ C → P z = z := by
    intro z hz
    have hzβ : z.2 ∉ tsupport β := fun hh => hz ⟨Set.mem_univ z.1, hh⟩
    exact Prod.ext rfl (hdfix z.2 hzβ)
  let D := SupportedDiffeomorph.extension Ψ P hC hCsource hPfix
  have hpoint (x : { x : M // f x = b }) : D x = Ψ (x, t) := by
    have hx0 : (x, 0) ∈ Ψ.source := hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
    have hP0 : P (x, 0) = (x, t) := by exact Prod.ext rfl hd0
    have hh := SupportedDiffeomorph.extension_chart Ψ P hC hCsource hPfix hx0
    change D (Ψ (x, 0)) = Ψ (P (x, 0)) at hh
    rwa [hzero x, hP0] at hh
  refine ⟨D, ?_, hpoint, ?_, ?_⟩
  · intro y hy
    exact SupportedDiffeomorph.extension_eq_of_notMem_image Ψ P hC hCsource hPfix hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z : { x : M // f x = b } := ⟨x, hx⟩
      have hDx : D x = Ψ (z, t) := hpoint z
      change f (D x) = b + t
      rw [hDx]
      exact
        hheight (z, t)
          (hsource
            ⟨Set.mem_univ z, by
              simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using htε.le⟩)
    · intro hy
      have hy' : f y = b + t := hy
      have hyTarget : y ∈ Ψ.target := by
        apply hband
        change Dist.dist (f y) b < ε
        simpa only [hy', Real.dist_eq, add_sub_cancel_left] using htε
      have hback := Ψ.map_target' hyTarget
      have hright : Ψ (Ψ.symm y) = y := Ψ.right_inv' hyTarget
      have htime : (Ψ.symm y).2 = t := by
        have hh := hheight (Ψ.symm y) hback
        rw [hright, hy'] at hh
        linarith
      refine ⟨((Ψ.symm y).1 : M), (Ψ.symm y).1.property, ?_⟩
      have hpair : ((Ψ.symm y).1, t) = Ψ.symm y := Prod.ext rfl htime.symm
      exact (hpoint (Ψ.symm y).1).trans ((congrArg Ψ hpair).trans hright)
  · have hsublevel (y : M) : f (D y) ≤ b + t ↔ f y ≤ b := by
      by_cases hy : y ∈ Ψ.target
      · let z := Ψ.symm y
        have hz : z ∈ Ψ.source := Ψ.map_target' hy
        have hPz : P z ∈ Ψ.source :=
          SupportedDiffeomorph.mapsTo_source Ψ P.toEquiv hCsource hPfix hz
        have hDy : D y = Ψ (P z) := SupportedDiffeomorph.extendMap_of_mem Ψ P hy
        have hfy : f y = b + z.2 := by
          have hh := hheight z hz
          have hzy : Ψ z = y := Ψ.right_inv' hy
          rwa [hzy] at hh
        have hfd : f (D y) = b + d z.2 := by
          rw [hDy]
          exact hheight (P z) hPz
        have horder : d z.2 ≤ t ↔ z.2 ≤ 0 := by
          rw [← hd0]
          exact hdmono.le_iff_le
        rw [hfd, hfy]
        constructor
        · intro hh
          have hz0 := horder.mp (by linarith)
          linarith
        · intro hh
          have hdz := horder.mpr (by linarith)
          linarith
      · have hDy : D y = y :=
          SupportedDiffeomorph.extension_eq_of_notMem_target Ψ P hC hCsource hPfix hy
        rw [hDy]
        have hfar : ε ≤ |f y - b| := by
          apply le_of_not_gt
          intro hh
          apply hy
          apply hband
          change Dist.dist (f y) b < ε
          simpa only [Metric.mem_ball, Real.dist_eq] using hh
        exact le_shift_iff_of_abs_sub_ge htε hfar
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hsublevel x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := D.surjective y
      exact ⟨x, (hsublevel x).mp hy, rfl⟩

/-- Nearby ambient levels are diffeomorphic when nonempty. -/
theorem RegularLevel.exists_nearby_ambient_level_diffeomorphs_of_nonempty {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
  obtain ⟨δ, hδ, -, K, hK, -, htransport⟩ :=
    exists_ambientTransport_of_heightCollar hf hreg ε hε Ψ hsource hzero hheight hband
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht
  obtain ⟨D, hfix, -, hlevel, hsublevel⟩ := htransport t ht
  exact ⟨D, hfix, hlevel, hsublevel⟩

/-- Nearby ambient levels are diffeomorphic. -/
theorem RegularLevel.exists_nearby_ambient_level_diffeomorphs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  classical
  by_cases hb : Nonempty { x : M // f x = b }
  · let _ := hb
    exact exists_nearby_ambient_level_diffeomorphs_of_nonempty hf hreg
  · have hlevel : ∀ x, f x = b → x ∈ (∅ : Set M) := fun x hx => (hb ⟨⟨x, hx⟩⟩).elim
    obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous isOpen_empty hlevel
    refine ⟨δ, hδ, ∅, isCompact_empty, ?_⟩
    intro t ht
    refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, fun _ _ => rfl, ?_, ?_⟩
    · change id '' {x : M | f x = b} = {x : M | f x = b + t}
      rw [Set.image_id]
      ext x
      constructor
      · intro hx
        exact (hb ⟨⟨x, hx⟩⟩).elim
      · intro hx
        have hball : x ∈ f ⁻¹' Metric.ball b δ := by
          change Dist.dist (f x) b < δ
          simpa only [show f x = b + t from hx, Real.dist_eq, add_sub_cancel_left] using ht
        exact (hband hball).elim
    · change id '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t}
      rw [Set.image_id]
      ext x
      have hfar : δ ≤ |f x - b| := by
        apply le_of_not_gt
        intro hh
        apply hband
        change Dist.dist (f x) b < δ
        simpa only [Real.dist_eq] using hh
      exact (le_shift_iff_of_abs_sub_ge ht hfar).symm

/-! ### Ambient equivalence of levels -/

/-- Two levels are ambiently equivalent if a transport diffeomorphism exists. -/
def RegularLevel.AmbientEquivalent {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a b : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
    D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b}

/-- Ambient equivalence is reflexive. -/
theorem RegularLevel.ambientEquivalent_refl {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a : ℝ) :
    AmbientEquivalent (E := E) f a a := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, ?_, ?_⟩ <;> exact Set.image_id _

/-- Ambient equivalence is symmetric. -/
theorem RegularLevel.ambientEquivalent_symm {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b : ℝ}
    (h : AmbientEquivalent (E := E) f a b) : AmbientEquivalent (E := E) f b a := by
  obtain ⟨D, hlevel, hsublevel⟩ := h
  have hreverse (S T : Set M) (hST : D '' S = T) : D.symm '' T = S := by
    rw [← hST, Set.image_image]
    have heq : (fun x : M => D.symm (D x)) = id := funext D.symm_apply_apply
    rw [heq, Set.image_id]
  exact ⟨D.symm, hreverse _ _ hlevel, hreverse _ _ hsublevel⟩

/-- Ambient equivalence is transitive. -/
theorem RegularLevel.ambientEquivalent_trans {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b c : ℝ}
    (hab : AmbientEquivalent (E := E) f a b) (hbc : AmbientEquivalent (E := E) f b c) :
    AmbientEquivalent (E := E) f a c := by
  obtain ⟨e, he, he'⟩ := hab
  obtain ⟨d, hd, hd'⟩ := hbc
  refine ⟨e.trans d, ?_, ?_⟩
  · change (fun x => d (e x)) '' {x : M | f x = a} = {x : M | f x = c}
    rw [← Set.image_image, he, hd]
  · change (fun x => d (e x)) '' {x : M | f x ≤ a} = {x : M | f x ≤ c}
    rw [← Set.image_image, he', hd']

/-- An ambient transport across a regular band exists. -/
theorem RegularLevel.exists_ambient_regularBand_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} := by
  classical
  let B := Set.Icc a b
  let left : B := ⟨a, ⟨le_rfl, hab⟩⟩
  let right : B := ⟨b, ⟨hab, le_rfl⟩⟩
  let reg (t : B) : ∀ x, f x = (t : ℝ) → x ∉ ManifoldMorse.criticalPoints E f := fun x hx =>
    hband x (hx ▸ t.property)
  let P : B → Prop := fun t => AmbientEquivalent (E := E) f a (t : ℝ)
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    obtain ⟨δ, hδ, K, -, htransport⟩ := exists_nearby_ambient_level_diffeomorphs hf (reg t)
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hdist : |(s : ℝ) - (t : ℝ)| < δ := by
      change Dist.dist (s : ℝ) (t : ℝ) < δ at hs
      simpa only [Real.dist_eq] using hs
    obtain ⟨D, -, hlevel, hsublevel⟩ := htransport ((s : ℝ) - (t : ℝ)) hdist
    have hts : AmbientEquivalent (E := E) f (t : ℝ) (s : ℝ) := by
      have heq : (t : ℝ) + ((s : ℝ) - (t : ℝ)) = (s : ℝ) := by ring
      refine ⟨D, ?_, ?_⟩
      · simpa only [heq] using hlevel
      · simpa only [heq] using hsublevel
    apply propext
    constructor
    · intro hs
      exact ambientEquivalent_trans hs (ambientEquivalent_symm hts)
    · intro ht
      exact ambientEquivalent_trans ht hts
  let _ : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hconstant : P left = P right := hlocal.apply_eq_of_preconnectedSpace left right
  have hleft : P left := ambientEquivalent_refl f a
  have hright : P right := hconstant ▸ hleft
  exact hright

/-- Ambiently equivalent levels are diffeomorphic. -/
theorem RegularLevel.exists_levelDiffeomorph_of_ambient {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b}) :
    letI := chartedSpace hf ha
    letI := chartedSpace hf hb
    ∃ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞,
      ∀ x, (e x : M) = D x := by
  let _ := chartedSpace hf ha
  let _ := chartedSpace hf hb
  have hiff (x : M) : f x = a ↔ f (D x) = b := by
    constructor
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := ⟨x, hx, rfl⟩
      rwa [hlevel] at hh
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := by rw [hlevel]; exact hx
      obtain ⟨z, hz, hzx⟩ := hh
      exact D.injective hzx ▸ hz
  let e := D.toHomeomorph.subtype (p := fun x => f x = a) (q := fun x => f x = b) hiff
  have he : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e :=
    (contMDiff_iff_inclusion hf hb 𝓘(ℝ, Model E) e).mpr
      (D.contMDiff.comp (RegularLevel.contMDiff_inclusion hf ha))
  have hei : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e.symm :=
    (contMDiff_iff_inclusion hf ha 𝓘(ℝ, Model E) e.symm).mpr
      (D.symm.contMDiff.comp (RegularLevel.contMDiff_inclusion hf hb))
  let F : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞ :=
    { e.toEquiv with
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact ⟨F, fun _ => rfl⟩

/-- Sphere coordinates induced by a linear isometry. -/
def SphereCoordinates.ofLinearIsometry {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] {n : ℕ}
    [Fact (Module.finrank ℝ N = n + 1)] [Fact (Module.finrank ℝ P = n + 1)] (L : N ≃ₗᵢ[ℝ] P) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : N) 1) (Metric.sphere (0 : P) 1) ∞ := by
  have hforward (x : Metric.sphere (0 : N) 1) : L (x : N) ∈ Metric.sphere (0 : P) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.norm_map] using x.property
  have hinverse (y : Metric.sphere (0 : P) 1) : L.symm (y : P) ∈ Metric.sphere (0 : N) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.symm.norm_map] using y.property
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, P) ∞ (fun x : Metric.sphere (0 : N) 1 => L (x : N)) :=
    L.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  have hi : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (fun y : Metric.sphere (0 : P) 1 => L.symm (y : P)) :=
    L.symm.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  exact
    { toFun := fun x => ⟨L x, hforward x⟩
      invFun := fun y => ⟨L.symm y, hinverse y⟩
      left_inv := fun x => Subtype.ext (L.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (L.apply_symm_apply y)
      contMDiff_toFun := hs.codRestrict_sphere hforward
      contMDiff_invFun := hi.codRestrict_sphere hinverse }
end Mathoverflow1973
