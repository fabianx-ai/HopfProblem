/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle

/-!
# Tubular neighbourhoods of a compact manifold embedded in Euclidean space

For a smooth closed embedding `e : M → ℝᴺ` (`NativeEuclideanEmbedding E M`) the normal spaces
`e.NormalSpace x = range (e.normalProjection x)` form a smooth vector bundle `e.NormalBundle` over
`M`, and the map `e.normalDisplacement : (x, v) ↦ e x + v` from its total space to `ℝᴺ` is a
local diffeomorphism at every point of the zero section. For compact `M` it restricts to a
diffeomorphism from an open neighbourhood of the zero section onto an open neighbourhood of
`e(M)`: the tubular neighbourhood theorem (Lee, *Introduction to Smooth Manifolds*, Thm 6.24, for
compact `M`). Composing the inverse with the bundle projection gives a smooth retraction of a
neighbourhood of `e(M)` onto `M` (Lee, Prop. 6.25), packaged as
`NativeEuclideanEmbedding.SmoothRetraction`.

## Main definitions and results

* `NativeEuclideanEmbedding.NormalBundle`, `normalPrebundle`, `normalContMDiffVectorBundle` : the
  normal bundle of the embedding as a smooth vector bundle.
* `NativeEuclideanEmbedding.normalDisplacement` and
  `isLocalDiffeomorphAt_normalDisplacement_zero` : the map `(x, v) ↦ e x + v` and its
  invertibility along the zero section.
* `NativeEuclideanEmbedding.exists_tubularNeighborhood` : the tubular neighbourhood theorem.
* `NativeEuclideanEmbedding.SmoothRetraction`, `nonempty_smoothRetraction` : a smooth retraction
  of an open neighbourhood of `e(M)` onto `M`.
* `DiskFraming.exists_pos_prod_closedBall_subset` : an open set containing `K × {0}`, `K`
  compact, contains `K × closedBall 0 ε` for some `ε > 0` (tube lemma).

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Thm 6.24, Prop. 6.25

## Tags

tubular neighbourhood, normal bundle, smooth retraction
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

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
  obtain ⟨d, hd, heq⟩ := (e.isLocalDiffeomorphAt_localNormalDisplacement x).exists_partialDiffeomorph
  let c := e.normalChartPartialDiffeomorph x
  have hc : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ c.source :=
    e.normalChart_source_zero x
  have hcd : c (Bundle.zeroSection e.NormalModel e.NormalSpace x) ∈ d.source := by
    rw [e.normalChartPartialDiffeomorph_zero]
    exact hd
  refine IsLocalDiffeomorphAt.of_eqOn (c.trans d) ⟨hc, hcd⟩ ?_
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
  intro v hv'
  obtain ⟨φ, hv, heq⟩ := IsLocalDiffeomorphAt.exists_partialDiffeomorph hv'
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hv)
    (fun w hw ↦ IsLocalDiffeomorphAt.of_eqOn φ hw heq)

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
  obtain ⟨φ, hx, heq⟩ := (e.isLocalDiffeomorphAt_normalDisplacement_zero x).exists_partialDiffeomorph
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
  obtain ⟨φ, hφx, heq⟩ := (hloc ⟨p.symm y, hx⟩).exists_partialDiffeomorph
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

/-! ### A tube lemma for closed balls -/

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
