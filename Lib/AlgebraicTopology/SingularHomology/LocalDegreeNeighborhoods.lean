/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.Geometry.Manifold.Morse.MinimalSystem
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb

/-!
# Neighborhood data for local degrees

Boundary and neighborhood data for local-degree computations (`LocalDegree.NeighborhoodData`,
`LocalDegree.SeparatedNeighborhoods`, `LocalDegree.NativeNeighborhood`), punctured balls inside
charts (`ChartPuncturedBall`), chart transitions of native parametrizations
(`NativeChartTransition`) and the linear sphere action lemmas used to compare normalized maps.

Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see
`Lib/reports/integration-4/spheretop-moves.md` for the per-declaration receipt.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

def PuncturedBall.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    C(Space E R, Metric.sphere (0 : E) 1) :=
  PuncturedRadial.toSphere.comp (toPunctured R)

theorem LocalDegree.exists_native_boundaryData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (BoundaryData (f ∘ NativeParametrization.centered (D := E) x) L
            ((NativeParametrization.centered (D := E) x).source ∩
              NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  let A : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c 0
  have hAi : A.IsInvertible := by
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)).IsInvertible
    rw [hcx]
    exact hA
  have hCi : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (PartialChart.bijective_mfderiv c hc0)).toContinuousLinearEquiv,
      rfl⟩
  have hder : HasFDerivAt (f ∘ c) (A.comp C) 0 :=
    ((hcf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0
        (hc.mdifferentiableAt (by simp)).hasMFDerivAt).hasFDerivAt
  obtain ⟨L, hL⟩ := hAi.comp hCi
  have hdL : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := hL.symm ▸ hder
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hdL.fderiv.symm, ?_⟩
  apply nonempty_boundaryData_of_contDiffAt L hdL _ hs hcomp
  change f (c 0) = 0
  rw [hcx]
  exact hzero

structure LocalDegree.NeighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F)
    (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  center_zero : f 0 = 0
  ball_subset : Metric.closedBall 0 radius ⊆ s
  continuous : ContinuousOn f (Metric.closedBall 0 radius)
  remainder_bound : ∀ x ∈ Metric.closedBall 0 radius, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖

theorem LocalDegree.nonempty_neighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  obtain ⟨b⟩ :=
    nonempty_boundaryData L hf hzero (Filter.inter_mem hs (Metric.ball_mem_nhds 0 hε))
      (hc.mono Set.inter_subset_left)
  have hbs : Metric.closedBall (0 : E) b.radius ⊆ s := b.ball_subset.trans Set.inter_subset_left
  exact
    ⟨⟨b.radius, b.radius_pos, hzero, hbs, hc.mono hbs, fun x hx => hεb x (b.ball_subset hx).2⟩⟩

theorem LocalDegree.nonempty_neighborhoodData_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (L : E ≃L[ℝ] F) {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨d⟩ :=
    nonempty_neighborhoodData L hf hzero (Filter.inter_mem hs ht)
      (htc.mono Set.inter_subset_right)
  exact ⟨{ d with ball_subset := d.ball_subset.trans Set.inter_subset_left }⟩

theorem LocalDegree.NeighborhoodData.image_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : LocalDegree.NeighborhoodData f L s) {x : E}
    (hx : x ∈ Metric.closedBall 0 d.radius) (hx0 : x ≠ 0) : f x ≠ 0 :=
  LocalDegree.image_ne_zero L hx0 (d.remainder_bound x hx)

def LocalDegree.NeighborhoodData.innerBoundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : LocalDegree.NeighborhoodData f L s) :
    LocalDegree.BoundaryData f L s := by
  have hr : 0 < d.radius / 2 := half_pos d.radius_pos
  have hballs : Metric.closedBall (0 : E) (d.radius / 2) ⊆ Metric.closedBall 0 d.radius :=
    Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le)
  have hparam (u : Metric.sphere (0 : E) 1) :
    (d.radius / 2) • (u : E) ∈ Metric.closedBall (0 : E) d.radius := by
    rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul (d.radius / 2) hr u]
    exact half_le_self d.radius_pos.le
  refine ⟨d.radius / 2, hr, hballs.trans d.ball_subset, ?_, ?_⟩
  · exact d.continuous.comp_continuous (continuous_const.smul continuous_subtype_val) hparam
  · exact fun u => d.remainder_bound _ (hparam u)

theorem LocalDegree.NeighborhoodData.innerBoundary_radius {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : LocalDegree.NeighborhoodData f L s) :
    d.innerBoundary.radius = d.radius / 2 :=
  rfl

theorem LocalDegree.NeighborhoodData.innerBoundary_mem_ball {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : LocalDegree.NeighborhoodData f L s)
    (u : Metric.sphere (0 : E) 1) :
    d.innerBoundary.radius • (u : E) ∈ Metric.ball (0 : E) d.radius := by
  rw [mem_ball_zero_iff, LocalDegree.norm_radius_smul _ d.innerBoundary.radius_pos,
    innerBoundary_radius]
  exact half_lt_self d.radius_pos

theorem LocalDegree.exists_native_neighborhoodData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
            ((NativeParametrization.centered (D := E) x).source ∩
              NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  obtain ⟨L, hL, _⟩ := exists_native_boundaryData x hf hzero hA W hW
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  have hd : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := by
    rw [hL]
    exact (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hL, nonempty_neighborhoodData_of_contDiffAt L hd ?_ hs hcomp⟩
  change f (c 0) = 0
  rw [hcx]
  exact hzero

def ChartPuncturedBall.openSet {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  c '' Metric.ball (0 : E) R

def ChartPuncturedBall.puncturedSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  {c 0}ᶜ ∩ openSet c R

theorem ChartPuncturedBall.zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : (0 : E) ∈ c.source :=
  hs (by simpa using hR.le)

theorem ChartPuncturedBall.ball_subset_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ⊆ c.source :=
  Metric.ball_subset_closedBall.trans hs

theorem ChartPuncturedBall.isOpen_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : IsOpen (openSet c R) :=
  c.isOpen_image_of_subset_source Metric.isOpen_ball (ball_subset_source c R hs)

theorem ChartPuncturedBall.center_mem_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R) :
    c 0 ∈ openSet c R :=
  Set.mem_image_of_mem c (by simpa using hR)

def ChartPuncturedBall.ballHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ≃ₜ openSet c R :=
  c.homeomorphOfImageSubsetSource (ball_subset_source c R hs) rfl

theorem ChartPuncturedBall.image_puncturedBall {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    c '' {x : E | x ≠ 0 ∧ ‖x‖ < R} = puncturedSet c R := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hxR⟩, rfl⟩
    have hx : x ∈ Metric.ball (0 : E) R := mem_ball_zero_iff.mpr hxR
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    change c x ≠ c 0
    exact fun h => hx0 (c.injOn (ball_subset_source c R hs hx) (zero_mem_source c R hR hs) h)
  · rintro ⟨hy0, x, hxR, rfl⟩
    refine ⟨x, ⟨?_, mem_ball_zero_iff.mp hxR⟩, rfl⟩
    intro hx0
    subst x
    exact hy0 rfl

def ChartPuncturedBall.puncturedHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    PuncturedBall.Space E R ≃ₜ puncturedSet c R :=
  c.homeomorphOfImageSubsetSource
    (fun _ hx => ball_subset_source c R hs (mem_ball_zero_iff.mpr hx.2))
    (image_puncturedBall c R hR hs)

def LocalDegree.NativeNeighborhood.openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Set M :=
  ChartPuncturedBall.openSet
    (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius

theorem LocalDegree.NativeNeighborhood.closedBall_subset_source {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.closedBall (0 : E) d.radius ⊆ (NativeParametrization.centered x).source :=
  d.ball_subset.trans Set.inter_subset_left

theorem LocalDegree.NativeNeighborhood.isOpen_openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    IsOpen (openSet x d) :=
  ChartPuncturedBall.isOpen_openSet
    (NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
    (closedBall_subset_source x d)

theorem LocalDegree.NativeNeighborhood.center_mem_openSet {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    x ∈ openSet x d := by
  have h :=
    ChartPuncturedBall.center_mem_openSet
      (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius
      d.radius_pos
  change NativeParametrization.centered x (0 : E) ∈ openSet x d at h
  rwa [NativeParametrization.centered_zero] at h

theorem LocalDegree.NativeNeighborhood.openSet_subset {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    openSet x d ⊆ W := by
  rintro y ⟨u, hu, rfl⟩
  exact (d.ball_subset (Metric.ball_subset_closedBall hu)).2

def LocalDegree.NativeNeighborhood.puncturedHomeomorph {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    PuncturedBall.Space E d.radius ≃ₜ ↥({ x }ᶜ ∩ openSet x d) :=
  (ChartPuncturedBall.puncturedHomeomorph
        (NativeParametrization.centered x).toOpenPartialHomeomorph d.radius d.radius_pos
        (closedBall_subset_source x d)).trans
    (Homeomorph.setCongr
      (by
        change {NativeParametrization.centered x (0 : E)}ᶜ ∩ openSet x d = _
        rw [NativeParametrization.centered_zero]))

structure LocalDegree.SeparatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (P : Set M) (f : M → F) (W : Set M) where
  linear : P → E ≃L[ℝ] F
  derivative_eq :
    ∀ x : P,
      (linear x).toContinuousLinearMap =
        fderiv ℝ (f ∘ NativeParametrization.centered (D := E) (x : M)) 0
  data :
    ∀ x : P,
      NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) (linear x)
        ((NativeParametrization.centered (D := E) (x : M)).source ∩
          NativeParametrization.centered (D := E) (x : M) ⁻¹' W)
  disjoint : Pairwise (Disjoint on (fun x : P => NativeNeighborhood.openSet (x : M) (data x)))

theorem LocalDegree.nonempty_separatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {P : Set M}
    {f : M → F} {W : Set M} (hP : P.Finite) (hf : ∀ x ∈ P, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hz : ∀ x ∈ P, f x = 0) (hA : ∀ x ∈ P, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (hW : ∀ x ∈ P, W ∈ 𝓝 x) : Nonempty (SeparatedNeighborhoods E P f W) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hP.t2_separation
  have hex (x : P) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap =
          fderiv ℝ (f ∘ NativeParametrization.centered (D := E) (x : M)) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) L
            ((NativeParametrization.centered (D := E) (x : M)).source ∩
              NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x))) :=
    exists_native_neighborhoodData (x : M) (hf x x.property) (hz x x.property) (hA x x.property)
      (W ∩ U x) (Filter.inter_mem (hW x x.property) ((hU x).2.mem_nhds (hU x).1))
  choose L hL hD using hex
  let D (x : P) :
    NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) (L x)
      ((NativeParametrization.centered (D := E) (x : M)).source ∩
        NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x)) :=
    Classical.choice (hD x)
  let D' (x : P) :
    NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) (L x)
      ((NativeParametrization.centered (D := E) (x : M)).source ∩
        NativeParametrization.centered (D := E) (x : M) ⁻¹' W) :=
    { D x with ball_subset := fun u hu => ⟨((D x).ball_subset hu).1, ((D x).ball_subset hu).2.1⟩ }
  refine ⟨⟨L, hL, D', ?_⟩⟩
  intro x y hxy
  change
    Disjoint (NativeNeighborhood.openSet (x : M) (D x)) (NativeNeighborhood.openSet (y : M) (D y))
  apply (hdisj x.property y.property (fun h => hxy (Subtype.ext h))).mono
  · exact (NativeNeighborhood.openSet_subset (x : M) (D x)).trans Set.inter_subset_right
  · exact (NativeNeighborhood.openSet_subset (y : M) (D y)).trans Set.inter_subset_right

def LocalDegree.SeparatedNeighborhoods.neighborhood {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) : Set M :=
  LocalDegree.NativeNeighborhood.openSet (x : M) (D.data x)

theorem LocalDegree.SeparatedNeighborhoods.isOpen_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    IsOpen (D.neighborhood x) :=
  LocalDegree.NativeNeighborhood.isOpen_openSet (x : M) (D.data x)

theorem LocalDegree.SeparatedNeighborhoods.center_mem_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (x : M) ∈ D.neighborhood x :=
  LocalDegree.NativeNeighborhood.center_mem_openSet (x : M) (D.data x)

theorem LocalDegree.SeparatedNeighborhoods.neighborhood_subset {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    D.neighborhood x ⊆ W :=
  LocalDegree.NativeNeighborhood.openSet_subset (x : M) (D.data x)

theorem LocalDegree.SeparatedNeighborhoods.pairwise_disjoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) :
    Pairwise (Disjoint on D.neighborhood) :=
  D.disjoint

theorem LocalDegree.SeparatedNeighborhoods.points_inter_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    P ∩ D.neighborhood x = {(x : M)} := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    change y = (x : M)
    by_contra hne
    let z : P := ⟨y, hyP⟩
    have hxz : x ≠ z := fun h => hne (congrArg Subtype.val h).symm
    exact Set.disjoint_left.mp (D.pairwise_disjoint hxz) hy (D.center_mem_neighborhood z)
  · rintro rfl
    exact ⟨x.property, D.center_mem_neighborhood x⟩

theorem LocalDegree.SeparatedNeighborhoods.overlap_eq {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Pᶜ ∩ D.neighborhood x = {(x : M)}ᶜ ∩ D.neighborhood x := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    refine ⟨?_, hy⟩
    rintro rfl
    exact hyP x.property
  · rintro ⟨hyx, hy⟩
    refine ⟨?_, hy⟩
    intro hyP
    have h : y ∈ P ∩ D.neighborhood x := ⟨hyP, hy⟩
    rw [D.points_inter_neighborhood x] at h
    exact hyx h

theorem LocalDegree.SeparatedNeighborhoods.open_cover {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : LocalDegree.SeparatedNeighborhoods E P f W) :
    Pᶜ ∪ (⋃ x : P, D.neighborhood x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ P
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, D.center_mem_neighborhood ⟨y, hy⟩⟩)
  · exact Or.inl hy

def LocalDegree.NeighborhoodData.puncturedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : LocalDegree.NeighborhoodData f L s) :
    C(PuncturedBall.Space E d.radius, PuncturedRadial.Space F) :=
  ⟨fun x => ⟨f x.val, d.image_ne_zero (mem_closedBall_zero_iff.mpr x.property.2.le) x.property.1⟩,
    (d.continuous.comp_continuous continuous_subtype_val
          (fun x => mem_closedBall_zero_iff.mpr x.property.2.le)).subtype_mk
      _⟩

def LocalDegree.NativeNeighborhood.overlapMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    C(↥({ x }ᶜ ∩ openSet x d), PuncturedRadial.Space F) :=
  d.puncturedMap.comp (puncturedHomeomorph x d).symm.toHomotopyEquiv.toFun

theorem LocalDegree.NativeNeighborhood.overlapMap_coe {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (y : ↥({ x }ᶜ ∩ openSet x d)) : (overlapMap x d y).val = f y.val := by
  have h := congrArg Subtype.val ((puncturedHomeomorph x d).apply_symm_apply y)
  change
    NativeParametrization.centered x ((puncturedHomeomorph x d).symm y).val = y.val at h
  exact congrArg f h

def LocalDegree.SeparatedNeighborhoods.overlapMap {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), PuncturedRadial.Space F) :=
  (LocalDegree.NativeNeighborhood.overlapMap (x : M) (D.data x)).comp
    (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

theorem LocalDegree.SeparatedNeighborhoods.overlapMap_coe {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (y : ↥(Pᶜ ∩ D.neighborhood x)) : (D.overlapMap x y).val = f y.val :=
  LocalDegree.NativeNeighborhood.overlapMap_coe (x : M) (D.data x) _

theorem SublevelDisk.contractibleSpace {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    {n : ℕ} (d : SublevelDisk n f a) : ContractibleSpace { x : M // f x ≤ a } := by
  let : ContractibleSpace (Hemisphere.Ball n) :=
    (convex_closedBall (0 : Hemisphere.Ambient n) 1).contractibleSpace ⟨0, by simp⟩
  exact d.homeomorph.symm.contractibleSpace

theorem SublevelDisk.homology_subsingleton {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} {n : ℕ} (d : SublevelDisk n f a) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology { x : M // f x ≤ a } k) := by
  let := d.contractibleSpace
  exact SingularHomology.contractible_homology_subsingleton _ k hk

theorem LinearSphereAction.sphereMap_comp {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : Function.Injective A)
    (hB : Function.Injective B) :
    (sphereMap B hB).comp (sphereMap A hA) = sphereMap (B.comp A) (hB.comp hA) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (B (‖A x.val‖⁻¹ • A x.val)) = NormedSpace.normalize (B (A x.val))
  rw [map_smul]
  exact
    NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (puncturedMap A hA x).property)) _

theorem LinearSphereAction.sphereMap_trans {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E ≃L[ℝ] F) (B : F ≃L[ℝ] G) :
    sphereMap (A.trans B).toContinuousLinearMap (A.trans B).injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap A.toContinuousLinearMap A.injective) :=
  (sphereMap_comp A.toContinuousLinearMap B.toContinuousLinearMap A.injective B.injective).symm

theorem LinearSphereAction.normalized_linearSphereMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) (r : ℝ)
    (hr : 0 < r) :
    PuncturedRadial.toSphere.comp (LocalDegree.linearSphereMap A r hr) =
      sphereMap A.toContinuousLinearMap A.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (A (r • x.val)) = NormedSpace.normalize (A x.val)
  rw [map_smul, NormedSpace.normalize_smul_of_pos hr]

theorem LinearSphereAction.sphereMap_relative {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E ≃L[ℝ] F) :
    sphereMap A.toContinuousLinearMap A.injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap (A.trans B.symm).toContinuousLinearMap (A.trans B.symm).injective) := by
  rw [← sphereMap_trans]
  have heq : (A.trans B.symm).trans B = A := by
    ext x
    exact B.apply_symm_apply (A x)
  rw [heq]

theorem LocalDegree.NativeNeighborhood.singlePoint_cover {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    { x }ᶜ ∪ openSet x d = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases h : y = x
  · subst y
    exact Or.inr (center_mem_openSet x d)
  · exact Or.inl h

theorem LocalDegree.NativeNeighborhood.openSet_contractible {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    ContractibleSpace (openSet x d) := by
  let : ContractibleSpace (Metric.ball (0 : E) d.radius) :=
    (convex_ball (0 : E) d.radius).contractibleSpace ⟨0, by simpa using d.radius_pos⟩
  exact
    (ChartPuncturedBall.ballHomeomorph
        (NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
        (closedBall_subset_source x d)).symm.contractibleSpace

theorem NativeParametrization.centered_symm_self {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) :
    (centered (D := E) x).symm x = 0 := by
  have h := (centered (D := E) x).left_inv' (zero_mem_centered_source x)
  rwa [centered_zero] at h

def NativeChartTransition.chart {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  ((NativeParametrization.centered (D := E) x).trans e.toPartialDiffeomorph).trans
    (NativeParametrization.centered (D := E) y).symm

theorem NativeChartTransition.chart_apply {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (u : E) :
    chart x y e u =
      (NativeParametrization.centered (D := E) y).symm
        (e (NativeParametrization.centered (D := E) x u)) :=
  rfl

theorem NativeChartTransition.zero_mem_source {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : (0 : E) ∈ (chart x y e).source := by
  change
    (0 ∈ (NativeParametrization.centered (D := E) x).source ∧
        NativeParametrization.centered (D := E) x 0 ∈ (Set.univ : Set M)) ∧
      e (NativeParametrization.centered (D := E) x 0) ∈
        (NativeParametrization.centered (D := E) y).target
  refine ⟨⟨NativeParametrization.zero_mem_centered_source x, Set.mem_univ _⟩, ?_⟩
  rw [NativeParametrization.centered_zero, he]
  exact NativeParametrization.mem_centered_target y

theorem NativeChartTransition.chart_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : chart x y e (0 : E) = 0 := by
  rw [chart_apply, NativeParametrization.centered_zero, he,
    NativeParametrization.centered_symm_self]

theorem NativeChartTransition.contDiffAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    ContDiffAt ℝ ∞ (chart x y e) (0 : E) :=
  ((chart x y e).contMDiffOn_toFun.contMDiffAt
      ((chart x y e).open_source.mem_nhds (zero_mem_source x y e he))).contDiffAt

theorem NativeChartTransition.bijective_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    Function.Bijective (fderiv ℝ (chart x y e) (0 : E)) := by
  have h := PartialChart.bijective_mfderiv (chart x y e) (zero_mem_source x y e he)
  rwa [mfderiv_eq_fderiv] at h

def NativeChartTransition.linear {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (fderiv ℝ (chart x y e) (0 : E)).toLinearMap
      (bijective_derivative x y e he)).toContinuousLinearEquiv

theorem NativeChartTransition.linear_eq_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    (linear x y e he).toContinuousLinearMap = fderiv ℝ (chart x y e) (0 : E) :=
  rfl

theorem NativeChartTransition.hasFDerivAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    HasFDerivAt (chart x y e) (linear x y e he).toContinuousLinearMap 0 := by
  rw [linear_eq_derivative]
  exact ((contDiffAt_chart x y e he).differentiableAt (by simp)).hasFDerivAt

theorem NativeChartTransition.nonempty_neighborhoodData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] (W : Set M)
    (hW : W ∈ 𝓝 x) :
    Nonempty
      (LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        (linear x y e he)
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hc : ContinuousAt c (0 : E) :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc (hcx.symm ▸ hW))
  exact
    LocalDegree.nonempty_neighborhoodData_of_contDiffAt (linear x y e he)
      (hasFDerivAt_chart x y e he) (chart_zero x y e he) hs (contDiffAt_chart x y e he)

theorem LinearSphereAction.homology_relative_sign {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (A B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign (A.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) a := by
  rw [sphereMap_relative A B, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, homology_eq_sign_smul]
  exact map_zsmul _ _ _

theorem LocalDegree.PointTransition.maps_point_complement {M : Type} [TopologicalSpace M]
    (e : M ≃ₜ M) (x y : M) (he : e x = y) : Set.MapsTo e { x }ᶜ { y }ᶜ := by
  intro z hz h
  exact hz (e.injective (h.trans he.symm))

def LocalDegree.NeighborhoodData.restrictRadius {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : LocalDegree.NeighborhoodData f L s) (r : ℝ) (hr : 0 < r)
    (hrR : r ≤ d.radius) : LocalDegree.NeighborhoodData f L s
    where
  radius := r
  radius_pos := hr
  center_zero := d.center_zero
  ball_subset := (Metric.closedBall_subset_closedBall hrR).trans d.ball_subset
  continuous := d.continuous.mono (Metric.closedBall_subset_closedBall hrR)
  remainder_bound x hx := d.remainder_bound x (Metric.closedBall_subset_closedBall hrR hx)

theorem LocalDegree.NativeNeighborhood.identity_center {M : Type}
    [TopologicalSpace M] (x : M) : (Homeomorph.refl M) x = x :=
  rfl

theorem LocalDegree.NativeNeighborhood.openSet_restrictRadius_subset {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    openSet x (d.restrictRadius r hr hrR) ⊆ openSet x d := by
  change
    (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph '' Metric.ball 0 r ⊆
      (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph ''
        Metric.ball 0 d.radius
  exact Set.image_mono (Metric.ball_subset_ball hrR)

theorem LocalDegree.NativeNeighborhood.mapsTo_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    Set.MapsTo (Homeomorph.refl M) (openSet x (d.restrictRadius r hr hrR)) (openSet x d) :=
  openSet_restrictRadius_subset x d r hr hrR

end
