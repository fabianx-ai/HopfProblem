/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Combinatorics.IndexDisorder
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
import Lib.Algebra.Module.IntegerPresentation
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.Geometry.Manifold.Morse.RearrangementAmbient
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.OrderedCancellation
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.BeltCancellation

/-!
# Surgery collapse

Homology of Morse surgery windows through one-point collapse of handle cores: punctured-ball
deformations and belt-tube meridians (`PuncturedBall.deformation`,
`MorseCancellation.nativeBeltTube_homotopic_meridian`), the embedded-cell attachment long exact
sequence (`EmbeddedCellAttachment.cell_exact_at_old`), collapse maps of attached cells and handles
(`DiskOnePointCollapse.collapse`, `ClosedHandleCore.collapseMap`,
`ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`),
the one-point cover of a sphere point (`OnePointCover.punctureHomeomorph`, `SpherePoint.pointDiffeomorph`),
adapted-window level transport (`AdaptedWindows.exists_middle_block_realization`) and the index-two
basis and middle presentation of a surgery window (`ManifoldMorse.SurgeryWindows.indexTwoBasis`,
`ManifoldMorse.SurgeryWindows.middlePresentation`, `ManifoldMorse.SurgeryWindows.middleMatrix`).

Moved verbatim from `Hopf/SphereTopology.lean` (base `b78cfee8`, second pass); see
`Lib/reports/integration-4/spheretop-moves.md` for the per-declaration receipt.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap


noncomputable section

theorem PuncturedBall.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (u : Metric.sphere (0 : E) 1) :
    toSphere R (fromSphere R r hr hrR u) = u :=
  PuncturedRadial.toSphere_fromSphere r hr u

def PuncturedBall.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R r hr hrR).comp (toSphere R))
    where
  toFun
    q :=
    ⟨blendVector R r q, PuncturedRadial.blendVector_ne_zero r hr (q.1, toPunctured R q.2),
      norm_blendVector_lt R r hr hrR q.1 q.2⟩
  continuous_toFun := (continuous_blendVector R r).subtype_mk _
  map_zero_left
    x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured]
  map_one_left
    x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      PuncturedRadial.toSphere, RadialExtension.direction, div_eq_mul_inv, smul_smul]

def PuncturedBall.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) : Metric.sphere (0 : E) 1 ≃ₕ Space E R
    where
  toFun := fromSphere R r hr hrR
  invFun := toSphere R
  left_inv := by
    have h :
      (toSphere (E := E) R).comp (fromSphere R r hr hrR) =
        ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R r hr hrR)
    rw [h]
  right_inv := ⟨(deformation R r hr hrR).symm⟩

theorem MorseCancellation.nativeBeltTube_homotopic_meridian {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) {X : Type} [TopologicalSpace X]
    (a : C(X, Metric.sphere (0 : d.chart.PositiveCoordinates) 1))
    (b : C(X, PuncturedBall.Space d.chart.NegativeCoordinates 1))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (ha : a.Homotopic (ContinuousMap.const _ v)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ((nativeBeltTubeInComplement d).comp (a.prodMk b)).Homotopic
      ((nativeBeltTubeMeridian d v r hr hr1).comp ((PuncturedBall.toSphere 1).comp b)) := by
  let c := (PuncturedBall.toSphere 1).comp b
  let b' := (PuncturedBall.fromSphere 1 r hr hr1).comp c
  have hb : b.Homotopic b' := by
    have H := (PuncturedBall.deformation 1 r hr hr1).compContinuousMap b
    exact ⟨H⟩
  have hpair := ha.prodMk hb
  have hh := (ContinuousMap.Homotopic.refl (nativeBeltTubeInComplement d)).comp hpair
  have heq :
    (nativeBeltTubeInComplement d).comp ((ContinuousMap.const _ v).prodMk b') =
      (nativeBeltTubeMeridian d v r hr hr1).comp c := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [heq] at hh
  exact hh

theorem MorseCancellation.nativeBeltTubeMeridian_eq {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (S : AdaptedWindows E f)
    (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    nativeBeltTubeMeridian (S.data q) v r hr hr1 =
      nativeUpperMeridianInComplement S q v ⟨r, hr.le, hr1.le⟩ hr := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm
        ((MorseHandle.ambientMap (S.data q).radius (v.val, r • u.val)).swap) =
      (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius r u.val v.val)
  congr 1
  simp only [MorseHandle.ambientMap, BeltPassage.upper, Prod.swap, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one, smul_smul]

theorem MorseCancellation.beltBallBoundary_homotopic_meridian {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne).Homotopic
      ((nativeBeltTubeMeridian d (beltBallCoordinates d ε F (parameterBallCenter ε hε)).1 r hr
            hr1).comp
        ((PuncturedBall.toSphere 1).comp (beltBallBoundaryNormal d ε hε F hsmall hne))) := by
  let a := ContinuousMap.fst.comp (beltBallCoordinates d ε F)
  have ha := parameterBall_boundary_nullhomotopic ε hε a
  exact
    nativeBeltTube_homotopic_meridian d (a.comp (parameterBallBoundary ε hε))
      (beltBallBoundaryNormal d ε hε F hsmall hne) (a (parameterBallCenter ε hε)) ha r hr hr1

theorem MorseCancellation.normal_boundary_homotopic_native_meridian {E M A : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (d : ManifoldMorse.MorseSurgeryData E f p) (g : A → d.UpperLevel)
    {L : A ≃L[ℝ] d.chart.NegativeCoordinates} {s : Set A}
    (b : LocalDegree.BoundaryData (d.beltNormal ∘ g) L s) (hc : ContinuousOn g s)
    (hdomain : ∀ z ∈ s, g z ∈ d.beltNormalDomain)
    (hsmall : ∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (g z)‖ < 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)),
      (∀ u, (J u).val = g (b.radius • u.val)) ∧
        ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
          J.Homotopic ((nativeBeltTubeMeridian d v r hr hr1).comp b.normalizedMap) := by
  let F : C(Metric.closedBall (0 : A) b.radius, d.chart.beltTarget d.radius) :=
    { toFun := fun z => ⟨g z.val, hdomain z.val (b.ball_subset z.property)⟩
      continuous_toFun :=
        (hc.comp_continuous continuous_subtype_val (fun z => b.ball_subset z.property)).subtype_mk
          _ }
  have hsmallF : ∀ z, ‖(beltBallCoordinates d b.radius F z).2‖ < 1 := by
    intro z
    rw [beltBallCoordinates_normal]
    exact hsmall z.val (b.ball_subset z.property)
  have hne :
    ∀ u,
      (beltBallCoordinates d b.radius F (parameterBallBoundary b.radius b.radius_pos u)).2 ≠ 0 := by
    intro u
    rw [beltBallCoordinates_normal]
    exact smul_ne_zero (inv_ne_zero d.radius_pos.ne') (b.map u).property
  let J := beltBallBoundaryInComplement d b.radius b.radius_pos F hsmallF hne
  have hJ : ∀ u, (J u).val = g (b.radius • u.val) := by
    intro u
    exact beltBallBoundaryInComplement_coe d b.radius b.radius_pos F hsmallF hne u
  let v := (beltBallCoordinates d b.radius F (parameterBallCenter b.radius b.radius_pos)).1
  have hH := beltBallBoundary_homotopic_meridian d b.radius b.radius_pos F hsmallF hne r hr hr1
  have heq :
    (PuncturedBall.toSphere 1).comp
        (beltBallBoundaryNormal d b.radius b.radius_pos F hsmallF hne) =
      b.normalizedMap := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact beltBallBoundary_normalized_coe d b.radius b.radius_pos F hsmallF hne u
  rw [heq] at hH
  exact ⟨J, hJ, v, hH⟩

theorem AdaptedWindows.exists_embedded_level_transport {E M G H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold J ∞ X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (γ : C(X, { x : M // f x = a })) (x₀ : X) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) →
            ∃ D :
              PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                { x : M // f x = a } { x : M // f x = b } ∞,
              D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
                D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
                  ∃ Γ : C(X, { x : M // f x = b }),
                    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
                      Function.Injective Γ ∧
                        (∀ z,
                            Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
                          (∀ z, D (γ z) = Γ z) ∧
                            (∀ z, D.symm (Γ z) = γ z) ∧
                              ∀ z, ∃ t : ℝ, S.flow t (γ z).val = (Γ z).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  change
    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) → _
  intro hγ hγi hγd hreach
  obtain ⟨t, ht⟩ := hreach x₀
  let zb : { x : M // f x = b } := ⟨S.flow t (γ x₀).val, ht⟩
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf ha hb (γ x₀) zb
  have hmaps (z : X) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hDγ : ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hmaps z))).comp z hγ.contMDiffAt
  let Γ : C(X, { x : M // f x = b }) := ⟨D ∘ γ, hDγ.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro x y hxy
    exact hγi (D.toPartialEquiv.injOn (hmaps x) (hmaps y) hxy)
  have hΓd : ∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hmaps z)) (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hmaps z)).1.comp (hγd z)
  refine ⟨D, hsource, htarget, Γ, hDγ, hΓi, hΓd, fun _ => rfl, ?_, ?_⟩
  · intro z
    exact D.left_inv' (hmaps z)
  · intro z
    exact horbit (γ z) (hmaps z)

theorem MorseCancellation.transverse_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {γ : Circle → N}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (B : D →L[ℝ] G) (z : Hemisphere.Sphere 1)
    (htrans :
      Function.Surjective
        ((mfderiv (𝓡 1) J γ (standardCircleParametrization z) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
          B)) :
    Function.Surjective
      ((mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
        B) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (standardCircleParametrization z)
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) standardCircleParametrization z
  have hP : Function.Surjective P :=
    (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).surjective
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  change Function.Surjective ((L.comp P).coprod B)
  exact surjective_coprod_comp_left L B P hP htrans

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_attaching_circle_lower_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := RegularLevel.chartedSpace hf ha
    ∃ e :
      Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1)
        (Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D :
        PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).LowerLevel { y : M // f y = a } ∞,
        D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
          D.target =
              {y |
                y.val ∈
                  FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
            ∃ Γ : C(Hemisphere.Sphere 1, { y : M // f y = a }),
              ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
                Function.Injective Γ ∧
                  (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
                    (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
                      (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
                        ∀ z,
                          ∃ t : ℝ,
                            S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val :=
  by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 1
  let γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf 1).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf 1).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf 1 (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere 1) :
    (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (MorseCancellation.standardCircleParametrization.symm (1 : Circle)) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.realize_one_handle_minimum_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (p r :
      ManifoldMorse.criticalPoints E f),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                MorseCancellation.nativeMorseIndex E f p = 0 ∧
                  MorseCancellation.nativeMorseIndex E f r = 0 ∧
                    p ≠ r ∧
                      f p < S.toSurgeryWindows.lower q ∧
                        f r < S.toSurgeryWindows.lower q ∧
                          (∀ x : (S.data q).LowerLevel,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
                                x ∈ Set.range (S.data q).surgery.attachingSphere) ∧
                            Filter.Tendsto
                                (fun t => G t ((S.data q).surgery.attachingSphere u).val)
                                Filter.atTop (𝓝 p.val) ∧
                              Filter.Tendsto
                                  (fun t => G t ((S.data q).surgery.attachingSphere v).val)
                                  Filter.atTop (𝓝 r.val) ∧
                                (∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                                    Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 p.val) ∨
                                      Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 r.val)) ∧
                                  ∀ j : ManifoldMorse.criticalPoints E f,
                                    j ≠ q →
                                      j ≠ p →
                                        j ≠ r →
                                          ∀ x,
                                            ¬(Filter.Tendsto (fun t => G t x) Filter.atBot
                                                  (𝓝 q.val) ∧
                                                Filter.Tendsto (fun t => G t x) Filter.atTop
                                                  (𝓝 j.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, hall⟩ :=
    S.place_one_handle_in_distinct_minimum_basins hf q hone u v hnot
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, hρ, hρbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 p.val) ∨
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 r.val) :=
    (hall w).imp ((hforward _ p.val).mpr) ((hforward _ r.val).mpr)
  refine
    ⟨V, G, p, r, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hp, hr, hpr,
      hpq, hrq, hbq, (hforward _ p.val).mpr hpu, (hforward _ r.val).mpr hrv, hends, ?_⟩
  intro j hjq hjp hjr x hx
  have hmono :=
    FlowConstruction.antitone_flow_height hf G hG (fun y hy => (hzero y).mpr (S.zero y hy))
      hdesc x
  have hforwardHeight := hf.continuous.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuous.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f q :=
    (hmono.le_of_tendsto hforwardHeight 0).trans (hmono.ge_of_tendsto hbackwardHeight 0)
  have hjq' : f j < f q :=
    lt_of_le_of_ne hle (fun h => hjq (Subtype.ext (S.distinct j.property q.property h)))
  have hjlow : f j < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper j).trans (S.separated j q hjq')
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
      (S.toSurgeryWindows.lower_lt_value q) hjlow
  let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
  have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
  have hzj : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 j.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff G t x j.val).mpr hx.2
  obtain ⟨w, hw⟩ := (hbq z).mp hzq
  have hh := hends w
  rw [hw] at hh
  rcases hh with hp' | hr'
  · exact hjp (Subtype.ext (tendsto_nhds_unique hzj hp'))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzj hr'))

theorem AdaptedWindows.exists_native_family_level_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) (α : ι → X → { x : M // f x = a }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            (∀ j x, (α j x).val ∈ FlowCancellation.levelBasin S.flow f b) →
              ∃ β : ι → X → { x : M // f x = b },
                (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                  (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                    (∀ j x,
                        Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                      Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  dsimp only
  intro hα hαinj hαimm hpair hreach
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf ha hb za zb
  have hsrc (j : ι) (x : X) : α j x ∈ P.source := by
    rw [hsource]
    exact hreach j x
  let β : ι → X → { x : M // f x = b } := fun j => P ∘ α j
  have hβ (j : ι) : ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j) := by
    intro x
    exact
      (P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))).comp x
        (hα j).contMDiffAt
  have hinj (j : ι) : Function.Injective (β j) := by
    intro x y hxy
    exact hαinj j (P.toPartialEquiv.injOn (hsrc j x) (hsrc j y) hxy)
  refine
    ⟨β, hβ, fun j => (hβ j).continuous.isClosedEmbedding (hinj j), ?_, ?_, fun j x =>
      horbit (α j x) (hsrc j x)⟩
  · intro j x
    have hP := P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))
    change Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (P ∘ α j) x)
    rw [mfderiv_comp x (hP.mdifferentiableAt (by simp)) ((hα j).mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv P (hsrc j x)).injective.comp (hαimm j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hiz hjz
    obtain ⟨x, hx⟩ := hiz
    obtain ⟨y, hy⟩ := hjz
    have heq : α i x = α j y := P.toPartialEquiv.injOn (hsrc i x) (hsrc j y) (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨y, heq.symm⟩

theorem AdaptedWindows.exists_middle_family_descent {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 3)
    (α : ι → (Hemisphere.Sphere 2) → (S.data p).UpperLevel) {P : Set (S.data p).UpperLevel}
    (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ β : ι → (Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                                  (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (β j x).val) ∧
                                    ∀ j x q,
                                      Filter.Tendsto (fun t => T.flow t (β j x).val) Filter.atBot
                                          (𝓝 q) ↔
                                        Filter.Tendsto (fun t => S.flow t (α j x).val)
                                          Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hs := (S.data p).chart.finrank_negative_add_positive
      have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
      omega⟩
  dsimp only
  intro hα hαinj hαimm hpair
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) <
      Module.finrank ℝ (RegularLevel.Model E) := by simp [RegularLevel.Model, hdim]
  obtain ⟨D, K, hK, -, ⟨A⟩, havoid⟩ :=
    MorseRearrangement.exists_whole_family_avoidance α hα ((S.data p).belt_smooth hf 2)
      hdim' hP hαP
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp []⟩
  let u :=
    SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2 x₀
  let v :=
    SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected⟩ :=
    S.exists_relative_level_surgery_system hf hm (S.data p).upper_regular
      ((S.data p).surgery.beltSphere v) ε hε D K P hK A
  have hreach (j : ι) (x : (Hemisphere.Sphere 2)) :
    (α j x).val ∈ FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
    apply S.reaches_old_lower_of_belt_avoidance T hf p D hforward (α j x)
    intro hx
    exact Set.disjoint_left.mp (havoid j) ⟨x, rfl⟩ hx
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    T.exists_native_family_level_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u) α hα hαinj hαimm
      hpair hreach
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j x q
  obtain ⟨t, ht⟩ := horbit j x
  rw [← ht]
  exact (MorseCancellation.flow_time_atBot_limit_iff T.flow t (α j x).val q).trans (hback (α j x) q)

theorem AdaptedWindows.exists_native_attaching_lower_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ Γ : C(Hemisphere.Sphere n, { y : M // f y = a }),
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
        Topology.IsClosedEmbedding Γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
            (∀ z,
                ∃ t : ℝ,
                  S.flow t
                      ((S.data p).surgery.attachingSphere
                          (SphereCoordinates.standardParametrization
                            (S.data p).chart.NegativeCoordinates n z)).val =
                    (Γ z).val) ∧
              ∀ y : { x : M // f x = a },
                y ∈ Set.range Γ ↔
                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n
  let γ : C(Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf n).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf n).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf n).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf n (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere n) :
    (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  let x₀ : Hemisphere.Sphere n := Hemisphere.point Bool.true ⟨0, by simp []⟩
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ x₀ hγ hγi hγd hreach
  refine ⟨Γ, hΓ, hΓ.continuous.isClosedEmbedding hΓi, hΓd, hflow, ?_⟩
  intro y
  exact S.transported_attaching_range_iff hf p ha e e.surjective Γ hflow y

theorem AdaptedWindows.exists_middle_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) (n : ℕ)
    (α : Fin n → (Hemisphere.Sphere 2) → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (Γ j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (Γ j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (Γ j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) ∧
                                  (∀ x,
                                      ∃ t : ℝ,
                                        T.flow t
                                            (MorseCancellation.nativeIndexThreeAttachingSphere T p hp
                                                x).val =
                                          (Γ 0 x).val) ∧
                                    (∀ y : (S.data p).LowerLevel,
                                        y ∈ Set.range (Γ 0) ↔
                                          Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot
                                            (𝓝 p.val)) ∧
                                      (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (Γ j.succ x).val) ∧
                                        (∀ j x q,
                                            Filter.Tendsto (fun t => T.flow t (Γ j.succ x).val)
                                                Filter.atBot (𝓝 q) ↔
                                              Filter.Tendsto (fun t => S.flow t (α j x).val)
                                                Filter.atBot (𝓝 q)) ∧
                                          ∀ j q,
                                            S.toSurgeryWindows.upper p < f q →
                                              (∀ x : (S.data p).UpperLevel,
                                                  x ∈ Set.range (α j) ↔
                                                    Filter.Tendsto (fun t => S.flow t x.val)
                                                      Filter.atBot (𝓝 q)) →
                                                ∀ y : (S.data p).LowerLevel,
                                                  y ∈ Set.range (Γ j.succ) ↔
                                                    Filter.Tendsto (fun t => T.flow t y.val)
                                                      Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  dsimp only
  intro hα hαinj hαimm hpair
  obtain
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, hlabels⟩ :=
    S.exists_middle_family_descent hf hm hdim p hp α hP hαP ε hε hα hαinj hαimm hpair
  let _ : Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (T.data p).chart).symm.trans hp⟩
  have hgap (q : ManifoldMorse.criticalPoints E f) (hqp : f q < f p) :
    f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper q).trans (S.separated q p hqp)
  obtain ⟨γ, hγ, hγe, hγi, hγflow, hγrange⟩ :=
    T.exists_native_attaching_lower_cut hf p 2 (S.data p).lower_regular
      (S.toSurgeryWindows.lower_lt_value p) hgap
  have hdisj (j : Fin n) : Disjoint (Set.range γ) (Set.range (β j)) := by
    apply Set.disjoint_left.mpr
    intro z hzγ hzβ
    obtain ⟨x, hx⟩ := hzβ
    have hb := (hγrange z).mp hzγ
    rw [← hx] at hb
    exact S.not_backward_basin_on_upper_level hf p (α j x) ((hlabels j x p.val).mp hb)
  let Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data p).LowerLevel := Fin.cases γ β
  have hΓpair : Pairwise (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact hβpair (fun h => hij (congrArg Fin.succ h))
  refine
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, Γ, ?_, ?_, ?_, hΓpair, hγflow, hγrange,
      horbit, hlabels, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hγ
    | succ j => exact hβ j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγe
    | succ j => exact hβe j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγi
    | succ j => exact hβi j
  · intro j q hq hfull
    apply
      T.transported_backward_basin_image hf
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
        (S.data p).lower_regular q hq (α j) (β j)
    · intro x
      exact (hfull x).trans (hback x q).symm
    · exact horbit j

theorem AdaptedWindows.exists_regular_band_family_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) (α : ι → X → { x : M // f x = a }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ β : ι → X → { x : M // f x = b },
              (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                  (∀ j x,
                      Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                    Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                        ∀ j q,
                          a < f q →
                            (∀ x : { y : M // f y = a },
                                x ∈ Set.range (α j) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) →
                              ∀ y : { x : M // f x = b },
                                y ∈ Set.range (β j) ↔
                                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨t, ht⟩ := S.reaches_lower_in_regular_band hf hab ha hgap za
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb za ⟨S.flow t za.val, ht⟩ α hα hαinj hαimm
      hpair (fun j x => S.reaches_lower_in_regular_band hf hab ha hgap (α j x))
  refine ⟨β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j q hq hfull
  exact S.transported_backward_basin_image hf hab hb q hq (α j) (β j) hfull (horbit j)

theorem AdaptedWindows.exists_regular_band_middle_basin_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → (Hemisphere.Sphere 2) → { x : M // f x = a })
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ β : Fin n → (Hemisphere.Sphere 2) → { x : M // f x = b },
      MorseCancellation.IsNativeMiddleBasinFamily S hf hb p β ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs (fun j => (he j).injective)
      hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩, hflow⟩

theorem AdaptedWindows.exists_middle_basin_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (q : ManifoldMorse.criticalPoints E f)
    (hq : MorseCancellation.nativeMorseIndex E f q = 3) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → (Hemisphere.Sphere 2) → (S.data q).UpperLevel)
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p α)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
        (∀ r, (T.data r).radius < ε r) ∧
          (∀ r ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
            ∃ Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data q).LowerLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular (Fin.cases q p)
                Γ := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair, -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_middle_family_step hf hm hdim q hq n α isClosed_empty (fun j => Set.disjoint_empty _)
      ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

theorem AdaptedWindows.exists_middle_block_realization {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (n : ℕ) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (horder : StrictMono (fun j => f (p j))) (habove : ∀ j, c < f (p j))
    (hblock :
      ∀ j (q : ManifoldMorse.criticalPoints E f), c < f q → f q ≤ f (p j) → q ∈ Set.range p)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    ∃ T : AdaptedWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
        (∀ q, (T.data q).radius < ε q) ∧
          (∀ q ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
            ∃ α : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = c },
              MorseCancellation.IsNativeMiddleBasinFamily T hf hc p α := by
  induction n generalizing S c ε with
  |
    zero =>
    obtain ⟨T, hfield, -, hcharts, hradii⟩ :=
      MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
        S.integral S.zero S.descent (fun q => (S.data q).chart) S.critical_model_germ ε hε
    refine ⟨T, hcharts, hradii, ?_, (fun j => Fin.elim0 j), ?_⟩
    · intro q hq
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · exact
        ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j⟩
  | succ n ih =>
    let a := S.toSurgeryWindows.upper (p 0)
    have hpa : f (p 0) < a := S.toSurgeryWindows.value_lt_upper (p 0)
    have htail (j : Fin n) : a < f (p j.succ) :=
      (S.separated (p 0) (p j.succ) (horder (Fin.succ_pos j))).trans
        (S.toSurgeryWindows.lower_lt_value (p j.succ))
    have htailblock (j : Fin n) (q : ManifoldMorse.criticalPoints E f) (haq : a < f q)
      (hqj : f q ≤ f (p j.succ)) : q ∈ Set.range (fun i : Fin n => p i.succ) := by
      obtain ⟨i, hi⟩ := hblock j.succ q ((habove 0).trans (hpa.trans haq)) hqj
      cases i using Fin.cases with
      | zero => exact (not_lt_of_ge haq.le (hi ▸ hpa)).elim
      | succ i => exact ⟨i, hi⟩
    let δ := Real.sqrt (f (p 0) - c)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (sub_pos.mpr (habove 0))
    let η : ManifoldMorse.criticalPoints E f → ℝ := fun q =>
      Min.min (ε q) (Min.min (S.data q).radius δ)
    have hη (q : ManifoldMorse.criticalPoints E f) : 0 < η q :=
      lt_min (hε q) (lt_min (S.data q).radius_pos hδ)
    obtain ⟨T, hchartsT, hradiiT, hgermsT, α, hα⟩ :=
      ih S (S.data (p 0)).upper_regular (fun j => p j.succ) (fun j => hp j.succ)
        (fun i j hij => horder (Fin.succ_lt_succ_iff.mpr hij)) htail htailblock η hη
    have hradius : (T.data (p 0)).radius < (S.data (p 0)).radius :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hradδ : (T.data (p 0)).radius < δ :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hupper : T.toSurgeryWindows.upper (p 0) < a := by
      have hh :=
        mul_pos (sub_pos.mpr hradius)
          (add_pos (S.data (p 0)).radius_pos (T.data (p 0)).radius_pos)
      change f (p 0) + (T.data (p 0)).radius ^ 2 < f (p 0) + (S.data (p 0)).radius ^ 2
      nlinarith
    have hlower : c < T.toSurgeryWindows.lower (p 0) := by
      have hh := mul_pos (sub_pos.mpr hradδ) (add_pos hδ (T.data (p 0)).radius_pos)
      have hs : δ ^ 2 = f (p 0) - c := Real.sq_sqrt (sub_pos.mpr (habove 0)).le
      change c < f (p 0) - (T.data (p 0)).radius ^ 2
      nlinarith
    have hgapUpper :
      ∀ q ∈ ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc (T.toSurgeryWindows.upper (p 0)) a := by
      intro q hq hh
      have heq :=
        S.isolated (p 0) q hq
          ⟨((S.toSurgeryWindows.lower_lt_value (p 0)).trans
                  (T.toSurgeryWindows.value_lt_upper (p 0))).le.trans
              hh.1,
            hh.2⟩
      rw [heq] at hh
      exact not_le_of_gt (T.toSurgeryWindows.value_lt_upper (p 0)) hh.1
    let _ : Fact (Module.finrank ℝ (S.data (p 0)).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hs := (S.data (p 0)).chart.finrank_negative_add_positive
        have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p 0)).chart).symm.trans (hp 0)
        omega⟩
    let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
    let v :=
      SphereCoordinates.standardParametrization (S.data (p 0)).chart.PositiveCoordinates 2
        x₀
    obtain ⟨β, hβ, -⟩ :=
      T.exists_regular_band_middle_basin_family hf hupper (S.data (p 0)).upper_regular
        (T.data (p 0)).upper_regular hgapUpper ((S.data (p 0)).surgery.beltSphere v)
        (fun j => p j.succ) htail α hα
    obtain ⟨U, hchartsU, hradiiU, hgermsU, Γ, hΓ⟩ :=
      T.exists_middle_basin_family_step hf hm hdim (p 0) (hp 0) (fun j => p j.succ)
        (fun j => hupper.trans (htail j)) β hβ ε hε
    have hp_cases : Fin.cases (p 0) (fun j => p j.succ) = p := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hp_cases] at hΓ
    have hbelow (q : ManifoldMorse.criticalPoints E f) (hqp : f q < f (p 0)) : f q < c := by
      by_contra h
      have hcq : c < f q :=
        lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (fun heq => hc q.val heq q.property))
      obtain ⟨j, hj⟩ := hblock 0 q hcq hqp.le
      have hh := horder.monotone (Fin.zero_le j)
      rw [hj] at hh
      exact not_lt_of_ge hh hqp
    have hgapLower :
      ∀ q ∈ ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc c (T.toSurgeryWindows.lower (p 0)) := by
      intro q hq hh
      exact
        not_le_of_gt (hbelow ⟨q, hq⟩ (hh.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p 0))))
          hh.1
    obtain ⟨Ω, hΩ, -⟩ :=
      U.exists_regular_band_middle_basin_family hf hlower (T.data (p 0)).lower_regular hc
        hgapLower (MorseCancellation.nativeIndexThreeAttachingSphere T (p 0) (hp 0) x₀) p
        (fun j =>
          (T.toSurgeryWindows.lower_lt_value (p 0)).trans_le (horder.monotone (Fin.zero_le j)))
        Γ hΓ
    refine ⟨U, fun q => (hchartsU q).trans (hchartsT q), hradiiU, ?_, Ω, hΩ⟩
    intro q hq
    filter_upwards [hgermsU q hq, hgermsT q hq] with y hyU hyT
    exact hyU.trans hyT

theorem MorseCancellation.unique_connection_of_distinct_minimum_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : Continuous f) (G : Flow ℝ M)
    (p r q : ManifoldMorse.criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hpr : p ≠ r) (hp : f p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
        (𝓝 q.val) ∧
      ∀ x,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val) →
            ∃ t, G t ((S.data q).surgery.attachingSphere u).val = x := by
  have hdim : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := by
    intro h
    apply hpr
    apply Subtype.ext
    exact tendsto_nhds_unique (h ▸ hu) hv
  have hbu :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
      (𝓝 q.val) :=
    (hback _).mpr (Set.mem_range_self u)
  have hsingle (x : (S.data q).LowerLevel)
    (hb : Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val))
    (hp' : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val)) :
    x = (S.data q).surgery.attachingSphere u := by
    obtain ⟨w, hw⟩ := (hback x).mp hb
    rcases Metric.unitSphere_eq_two_points_of_finrank_eq_one hdim u v huv w with h | h
    · exact (congrArg (S.data q).surgery.attachingSphere h).symm.trans hw |>.symm
    · have hx : (S.data q).surgery.attachingSphere v = x := h ▸ hw
      have hrv : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val) := hx ▸ hv
      exact False.elim (hpr (Subtype.ext (tendsto_nhds_unique hp' hrv)))
  have h :=
    FlowSuspension.unique_connection_of_level_basin_intersection G G hf
      (S.lower_lt_value q) hp id (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      ((S.data q).surgery.attachingSphere u) hbu hu hsingle
  exact ⟨h.1, h.2.2⟩

def EmbeddedCellAttachment.overlapHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(D.oldNeighborhood ∩ D.diskPatch)) k :=
  SingularHomology.homotopyEquivHomologyEquiv D.overlapSphereEquiv k

def EmbeddedCellAttachment.cellConnectingMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (D.overlapHomologyEquiv k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k)

theorem EmbeddedCellAttachment.coverLeft_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    (D.oldHomologyEquiv k).symm
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k a)).1 =
      D.attachingHomologyMap k a := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap D.oldRetraction k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          k (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap D.attachingSphere k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) k
        a =
      _
  rw [D.overlapOldMap_comp_sphere]

theorem EmbeddedCellAttachment.coverLeft_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
        (D.overlapHomologyEquiv k a) =
      (D.oldHomologyEquiv k (D.attachingHomologyMap k a), 0) := by
  let := D.diskPatch_homology_subsingleton k hk
  apply Prod.ext
  · exact (D.oldHomologyEquiv k).symm_apply_eq.mp (D.coverLeft_old k a)
  · exact Subsingleton.elim _ _

theorem EmbeddedCellAttachment.cellConnecting_eq_zero_iff {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    D.cellConnectingMap k a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
          D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k a =
        0 := by
  change (D.overlapHomologyEquiv k).symm _ = 0 ↔ _ = 0
  constructor
  · intro h
    exact (D.overlapHomologyEquiv k).symm.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem EmbeddedCellAttachment.cell_exact_at_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.attachingHomologyMap k) = LinearMap.ker (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch k)
        (D.overlapHomologyEquiv k s)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k s)) =
        0 at hzero
    rw [D.coverLeft_formula k hk, D.coverRight_old] at hzero
    exact hzero
  · intro ha
    have hpair :
      (D.oldHomologyEquiv k a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
            (D.oldHomologyEquiv k a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover k] at hpair
    obtain ⟨c, hc⟩ := hpair
    refine ⟨(D.overlapHomologyEquiv k).symm c, ?_⟩
    have hc' :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm c)) =
        (D.oldHomologyEquiv k a, 0) := by
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    rw [D.coverLeft_formula k hk] at hc'
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        hc'
    exact (D.oldHomologyEquiv k).injective heq

theorem EmbeddedCellAttachment.cell_exact_at_ambient {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    LinearMap.range (D.oldHomologyMap (k + 1)) = LinearMap.ker (D.cellConnectingMap k) := by
  rw [← D.range_coverRight (k + 1) (Nat.succ_ne_zero k),
    SingularMayerVietoris.exact_at_ambient D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover k]
  ext a
  exact (D.cellConnecting_eq_zero_iff k a).symm

theorem EmbeddedCellAttachment.mem_range_cellConnecting {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    a ∈ LinearMap.range (D.cellConnectingMap k) ↔
      D.overlapHomologyEquiv k a ∈
        LinearMap.range
          (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
            D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change _ = D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm _)
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (D.overlapHomologyEquiv k).symm _ = a
    rw [hx, LinearEquiv.symm_apply_apply]

theorem EmbeddedCellAttachment.coverLeft_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k a) =
        0 ↔
      D.attachingHomologyMap k a = 0 := by
  rw [D.coverLeft_formula k hk]
  constructor
  · intro h
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        h
    exact (D.oldHomologyEquiv k).injective (heq.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]
    rfl

theorem EmbeddedCellAttachment.cell_exact_at_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.cellConnectingMap k) = LinearMap.ker (D.attachingHomologyMap k) := by
  ext a
  rw [D.mem_range_cellConnecting k,
    SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  exact D.coverLeft_eq_zero_iff k hk a

theorem EmbeddedCellAttachment.cellConnecting_zero_apply {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)]
    (a : SingularMayerVietoris.SingularHomology X 1) : D.cellConnectingMap 0 a = 0 := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  have hc :
    D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a) ∈
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    rw [←
      SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
        D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0]
    exact (D.mem_range_cellConnecting 0 _).mp ⟨a, rfl⟩
  change
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a)) =
      0 at hc
  have h := congrArg Prod.snd hc
  rw [SingularMayerVietoris.leftHomologyMap_apply] at h
  have hz : SingularMayerVietoris.singularHomologyMap q 0 (D.cellConnectingMap 0 a) = 0 := by
    rw [SingularHomology.singularHomologyMap_comp]
    exact neg_eq_zero.mp h
  apply SphereHomology.singularHomologyMap_zero_injective q
  exact hz.trans (map_zero _).symm

theorem MorseCancellation.cell_oldHomologyMap_zero_injective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Injective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpair :
    (D.oldHomologyEquiv 0 a, 0) ∈
      LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.oldHomologyEquiv 0 a, 0) =
        0
    rw [D.coverRight_old]
    exact ha
  rw [←
    SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover 0] at hpair
  obtain ⟨c, hc⟩ := hpair
  have hq :
    SingularMayerVietoris.singularHomologyMap q 0 ((D.overlapHomologyEquiv 0).symm c) = 0 := by
    have h := congrArg Prod.snd hc
    rw [SingularMayerVietoris.leftHomologyMap_apply] at h
    rw [SingularHomology.singularHomologyMap_comp]
    change
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
          (D.overlapHomologyEquiv 0 ((D.overlapHomologyEquiv 0).symm c)) =
        0
    rw [LinearEquiv.apply_symm_apply]
    exact neg_eq_zero.mp h
  have hz : (D.overlapHomologyEquiv 0).symm c = 0 :=
    SphereHomology.singularHomologyMap_zero_injective q (hq.trans (map_zero _).symm)
  have hc0 : c = 0 := by
    apply (D.overlapHomologyEquiv 0).symm.injective
    exact hz.trans (map_zero _).symm
  rw [hc0, map_zero] at hc
  apply (D.oldHomologyEquiv 0).injective
  exact (congrArg Prod.fst hc).symm.trans (map_zero _).symm

theorem MorseCancellation.cell_oldHomologyMap_zero_surjective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Surjective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  intro a
  obtain ⟨⟨b, c⟩, hbc⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover a
  obtain ⟨z, hz⟩ := SphereHomology.singularHomologyMap_zero_surjective q c
  let v := D.overlapHomologyEquiv 0 z
  have hv :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
        v =
      c := by
    rw [SingularHomology.singularHomologyMap_comp] at hz
    exact hz
  have hzero :=
    LinearMap.congr_fun
      (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) v
  change
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0 v) =
      0 at hzero
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.rightHomologyMap_apply,
    map_neg, hv] at hzero
  have hrel :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) 0
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          0 v) =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.diskPatch) 0 c := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hzero
  refine
    ⟨(D.oldHomologyEquiv 0).symm
        (b +
          SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.inclusion Set.inter_subset_left) 0 v),
      ?_⟩
  rw [← D.coverRight_old, LinearEquiv.apply_symm_apply,
    SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero, map_add, hrel]
  exact hbc

theorem MorseCancellation.cell_oldHomologyMap_zero_bijective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Bijective (D.oldHomologyMap 0) :=
  ⟨cell_oldHomologyMap_zero_injective D, cell_oldHomologyMap_zero_surjective D⟩

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (d.coreCellPresentation hf).old k :=
  SingularHomology.homeomorphHomologyEquiv (d.cellOldHomeomorph hf) k

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularHomology.homotopyEquivHomologyEquiv (d.coreUnionHomotopyEquiv hf) k

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.morseConnectingMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k :=
  ((d.coreCellPresentation hf).cellConnectingMap k).comp
    (d.cellTotalHomologyEquiv hf (k + 1)).symm.toLinearMap

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :
    (d.coreCellPresentation hf).attachingHomologyMap k a =
      d.cellOldHomologyEquiv hf k (d.coreBoundaryHomologyMap k a) := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).attachingSphere k a =
      SingularMayerVietoris.singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k a)
  rw [d.coreCell_attaching_eq, SingularHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.cellOldHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) :
    d.cellTotalHomologyEquiv hf k
        ((d.coreCellPresentation hf).oldHomologyMap k (d.cellOldHomologyEquiv hf k a)) =
      d.lowerRealizationHomologyMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (d.coreCellPresentation hf).old) k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.morseConnecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) (k + 1)) :
    d.morseConnectingMap hf k (d.cellTotalHomologyEquiv hf (k + 1) a) =
      (d.coreCellPresentation hf).cellConnectingMap k a := by
  change
    (d.coreCellPresentation hf).cellConnectingMap k
        ((d.cellTotalHomologyEquiv hf (k + 1)).symm (d.cellTotalHomologyEquiv hf (k + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.coreBoundaryHomologyMap k) =
      LinearMap.ker (d.lowerRealizationHomologyMap k) := by
  refine
    HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf k).symm (d.cellTotalHomologyEquiv hf k)
      ((d.coreCellPresentation hf).attachingHomologyMap k)
      ((d.coreCellPresentation hf).oldHomologyMap k) (d.coreBoundaryHomologyMap k)
      (d.lowerRealizationHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have h := d.cellOldHomology_compare hf k ((d.cellOldHomologyEquiv hf k).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) =
      LinearMap.ker (d.morseConnectingMap hf k) := by
  refine
    HomologyTransport.exact_of_equivalences (d.cellOldHomologyEquiv hf (k + 1)).symm
      (d.cellTotalHomologyEquiv hf (k + 1)) (LinearEquiv.refl ℤ _)
      ((d.coreCellPresentation hf).oldHomologyMap (k + 1))
      ((d.coreCellPresentation hf).cellConnectingMap k) (d.lowerRealizationHomologyMap (k + 1))
      (d.morseConnectingMap hf k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_ambient k)
  · intro a
    have h := d.cellOldHomology_compare hf (k + 1) ((d.cellOldHomologyEquiv hf (k + 1)).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact d.morseConnecting_compare hf k

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.morseConnectingMap hf k) = LinearMap.ker (d.coreBoundaryHomologyMap k) := by
  refine
    HomologyTransport.exact_of_equivalences (d.cellTotalHomologyEquiv hf (k + 1))
      (LinearEquiv.refl ℤ _) (d.cellOldHomologyEquiv hf k).symm
      ((d.coreCellPresentation hf).cellConnectingMap k)
      ((d.coreCellPresentation hf).attachingHomologyMap k) (d.morseConnectingMap hf k)
      (d.coreBoundaryHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_sphere k hk)
  · exact d.morseConnecting_compare hf k
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)]
    [Subsingleton
        (SingularMayerVietoris.SingularHomology
          (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  have hall :
    ∀ a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k, a = 0 :=
    by
    intro a
    have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_lower hf k hk] at ha
    obtain ⟨s, hs⟩ := ha
    have hs0 : s = 0 := Subsingleton.elim _ _
    rw [hs0, map_zero] at hs
    exact hs.symm
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

theorem ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :
    d.morseConnectingMap hf 0 a = 0 := by
  let := d.attachingSphere_pathConnected hindex
  exact (d.coreCellPresentation hf).cellConnecting_zero_apply _

theorem ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Surjective (d.lowerRealizationHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 0) :=
    d.morseConnecting_zero_apply hf hindex a
  rw [← d.morse_exact_at_upper hf 0] at ha
  exact ha

theorem ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :=
  (d.lowerRealization_one_surjective hf hindex).subsingleton

theorem MorseCancellation.native_lowerRealization_zero_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Bijective (d.lowerRealizationHomologyMap 0) := by
  let := d.attachingSphere_pathConnected hindex
  have hi := cell_oldHomologyMap_zero_bijective (d.coreCellPresentation hf)
  have heq :
    d.lowerRealizationHomologyMap 0 =
      (d.cellTotalHomologyEquiv hf 0).toLinearMap.comp
        (((d.coreCellPresentation hf).oldHomologyMap 0).comp
          (d.cellOldHomologyEquiv hf 0).toLinearMap) := by
    ext a
    exact (d.cellOldHomology_compare hf 0 a).symm
  rw [heq]
  exact
    (d.cellTotalHomologyEquiv hf 0).bijective.comp
      (hi.comp (d.cellOldHomologyEquiv hf 0).bijective)

theorem MorseCancellation.native_lower_pathConnected_of_upper {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let := d.attachingSphere_pathConnected hindex
  let : Nonempty { z : M // f z ≤ f p - d.radius ^ 2 } :=
    ⟨d.coreBoundaryMap (Classical.arbitrary (Metric.sphere (0 : d.chart.NegativeCoordinates) 1))⟩
  exact
    pathConnectedSpace_of_homologyZero_injective d.realizedLowerInclusion
      (native_lowerRealization_zero_bijective d hf hindex).1

theorem MorseCancellation.native_zero_handle_lower_isEmpty {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    IsEmpty { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : Subsingleton d.chart.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ d.chart.NegativeCoordinates).mp hindex
  let : IsEmpty (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
    ⟨fun v => by
      have h := mem_sphere_zero_iff_norm.mp v.property
      rw [Subsingleton.elim v.val 0, norm_zero] at h
      norm_num at h⟩
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  have he := cell_old_empty_of_empty_boundary (d.coreCellPresentation hf)
  refine ⟨fun x => ?_⟩
  have hx := (d.cellOldHomeomorph hf x).property
  exact (Set.eq_empty_iff_forall_notMem.mp he) _ hx

theorem SublevelDisk.circle_nullhomotopies {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (d : SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = a }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Hemisphere.Sphere n ≃ₜ { x : M // f x = a } := d.boundaryHomeomorph
  let forward : C(Hemisphere.Sphere n, { x : M // f x = a }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = a }, Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val →
            Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
            ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : SublevelDisk 6 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 5) (by norm_num)
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow :
        ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel),
          ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
        FlowConstruction.circle_nullhomotopies_regular_level hf
          (S.ordered_windows _ _ hlt).le (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with htwo | hthree
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 1 + 1) :=
          ⟨htwo⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 1 (by norm_num) (by omega)
            hlow
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) :=
          ⟨hthree⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2 (by norm_num) (by omega)
            hlow
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact
    FlowConstruction.circle_nullhomotopies_regular_level hf
      (S.ordered_windows _ _ hprevj).le
      (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
      (hupper (j.val - 1) hprev hprevj)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (p : ManifoldMorse.criticalPoints E f)
    (hpindex : nativeMorseIndex E f p = 2) (hzero : nativeMorseCount E f 0 = 1)
    (hone : nativeMorseCount E f 1 = 0)
    (horder :
      ∀ r : ManifoldMorse.criticalPoints E f, f r < f p → nativeMorseIndex E f r ≤ 2) :
    ∀ γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨j, rfl⟩ := S.point.surjective p
  have hn : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  have hpnotfirst : S.point j ≠ S.first hn := by
    intro hpfirst
    have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
      (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
    rw [hpfirst] at hpindex
    omega
  have hj : 0 < j.val := by
    by_contra hj
    have hj0 : j.val = 0 := by omega
    have heq : S.point j = S.first hn := congrArg S.point (Fin.ext hj0)
    exact hpnotfirst heq
  have hmiddle (i : Fin S.count) (hi : 0 < i.val) (hij : i.val < j.val) :
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 := by
    have hvalues : f (S.point i) < f (S.point j) := S.point_strictMono (show i < j from hij)
    have hle := horder (S.point i) hvalues
    have hne0 : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hindex
      have heq : (S.point i).val = (S.first hn).val :=
        native_index_zero_point_unique S hf hn hzero _ (S.point i).property hindex
      have heq' : S.point i = S.point ⟨0, hn⟩ := Subtype.ext heq
      have hival := congrArg Fin.val (S.point.injective heq')
      change i.val = 0 at hival
      omega
    have hne1 := native_index_one_excluded S hone _ (S.point i).property
    have hindex : nativeMorseIndex E f (S.point i) = 2 := by omega
    exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point i)).chart).symm.trans hindex)
  exact S.lower_circle_nullhomotopies_of_middle_indices hf hdim j hj hmiddle

def MorseCancellation.cellDiskBoundaryHomologyMap {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.diskPatch 0 :=
  SingularMayerVietoris.singularHomologyMap
    ((ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun) 0

theorem MorseCancellation.cell_oldHomologyMap_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (a : SingularMayerVietoris.SingularHomology D.old 0) :
    D.oldHomologyMap 0 a = 0 ↔
      ∃ z : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0,
        D.attachingHomologyMap 0 z = a ∧ cellDiskBoundaryHomologyMap D z = 0 := by
  constructor
  · intro ha
    have hp :
      (D.oldHomologyEquiv 0 a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.oldHomologyEquiv 0 a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover 0] at hp
    obtain ⟨c, hc⟩ := hp
    let z := (D.overlapHomologyEquiv 0).symm c
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      dsimp [z]
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    refine ⟨z, ?_, ?_⟩
    · rw [← D.coverLeft_old, hL, LinearEquiv.symm_apply_apply]
    · have hs := congrArg Prod.snd hL
      rw [SingularMayerVietoris.leftHomologyMap_apply] at hs
      change SingularMayerVietoris.singularHomologyMap _ 0 z = 0
      rw [SingularHomology.singularHomologyMap_comp]
      exact neg_eq_zero.mp hs
  · rintro ⟨z, hza, hz⟩
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      apply Prod.ext
      · exact (D.oldHomologyEquiv 0).symm_apply_eq.mp ((D.coverLeft_old 0 z).trans hza)
      · rw [SingularMayerVietoris.leftHomologyMap_apply]
        rw [cellDiskBoundaryHomologyMap, SingularHomology.singularHomologyMap_comp] at hz
        exact neg_eq_zero.mpr hz
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0)
        (D.overlapHomologyEquiv 0 z)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.overlapHomologyEquiv 0 z)) =
        0 at hzero
    rw [hL, D.coverRight_old] at hzero
    exact hzero

theorem MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    Function.Injective (D.oldHomologyMap 0) := by
  let c : C(D.diskPatch, D.old) := ContinuousMap.const _ p
  have heq :
    D.attachingHomologyMap 0 =
      (SingularMayerVietoris.singularHomologyMap c 0).comp (cellDiskBoundaryHomologyMap D) := by
    apply homologyZero_linearMap_ext
    intro u
    change
      SingularMayerVietoris.singularHomologyMap D.attachingSphere 0
          (SingularHomology.pointClass u) =
        SingularMayerVietoris.singularHomologyMap c 0
          (SingularMayerVietoris.singularHomologyMap _ 0 (SingularHomology.pointClass u))
    rw [SingularHomology.singularHomologyMap_pointClass,
      SingularHomology.singularHomologyMap_pointClass,
      SingularHomology.singularHomologyMap_pointClass]
    exact (pointClass_eq_iff_joined _ _).mpr (hcomponent u)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨z, hza, hz⟩ := (cell_oldHomologyMap_zero_iff D a).mp ha
  rw [← hza, heq, LinearMap.comp_apply, hz, map_zero]

theorem MorseCancellation.cell_old_pathConnected_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) [PathConnectedSpace X] (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) : PathConnectedSpace D.old := by
  let : Nonempty D.old := ⟨p⟩
  exact
    pathConnectedSpace_of_homologyZero_injective (SingularMayerVietoris.subtypeInclusion D.old)
      (cell_oldHomologyMap_injective_of_attaching_component D p hcomponent)

theorem MorseCancellation.native_lower_pathConnected_of_attaching_component {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (a : { z : M // f z ≤ f p - d.radius ^ 2 }) (hcomponent : ∀ u, Joined (d.coreBoundaryMap u) a)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    cell_old_pathConnected_of_attaching_component (d.coreCellPresentation hf)
      (d.cellOldHomeomorph hf a)
      (fun u => by
        rw [d.coreCell_attaching_eq]
        exact (hcomponent u).map (d.cellOldHomeomorph hf).continuous)
  exact pathConnectedSpace_of_homotopyEquiv (d.cellOldHomeomorph hf).toHomotopyEquiv

theorem MorseCancellation.native_attaching_component_of_pairwise_joined {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hjoined : ∀ u v, Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v)) :
    ∃ a : { z : M // f z ≤ f p - d.radius ^ 2 }, ∀ u, Joined (d.coreBoundaryMap u) a := by
  let : Nontrivial d.chart.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : d.chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨d.coreBoundaryMap ⟨v, hv⟩, fun u => hjoined u ⟨v, hv⟩⟩

theorem MorseCancellation.native_minimum_count_one_of_one_handle_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcomponents :
      ∀ p : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f p = 1 →
          ∃ a : { z : M // f z ≤ f p - (S.data p).radius ^ 2 },
            ∀ u, Joined ((S.data p).coreBoundaryMap u) a) :
    nativeMorseCount E f 0 = 1 := by
  classical
  have hn := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have htail (i : Fin S.count) (hji : j.val < i.val)
    (hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) }) :
    PathConnectedSpace { x : M // f x ≤ S.lower (S.point i) } := by
    let : PathConnectedSpace { x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2 } :=
      hupper
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · obtain ⟨a, ha⟩ := hcomponents (S.point i) hone
      exact
        native_lower_pathConnected_of_attaching_component (S.data (S.point i)) hf.continuous a ha
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace { x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2 } :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 } :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have hjfirst : j.val = 0 := by
    by_contra hj
    have hlt : (⟨0, hn⟩ : Fin S.count) < j := by change 0 < j.val; omega
    have hbelow : f (S.first hn) ≤ S.lower (S.point j) :=
      (S.value_lt_upper (S.first hn)).le.trans (S.ordered_windows _ _ hlt).le
    exact
      isEmptyElim
        (⟨S.first hn, hbelow⟩ :
          { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 })
  have hset :
    {x : M | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} =
      {(S.first hn).val} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨i, he⟩ := S.point.surjective ⟨x, hx⟩
      have hi0 : nativeMorseIndex E f (S.point i) = 0 := by simpa only [he] using hi
      have hle : i.val ≤ j.val := hmax i hi0
      have hi0' : i.val = 0 := by omega
      have hip : S.point i = S.first hn := congrArg S.point (Fin.ext hi0')
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (he.symm.trans hip))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ ⟨(S.first hn).property, hfirst⟩
  exact Set.ncard_eq_one.mpr ⟨(S.first hn).val, hset⟩

theorem MorseCancellation.exists_native_one_handle_joining_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : nativeMorseCount E f 0 ≠ 1) :
    ∃ p : ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f p = 1 ∧
        ∃ u v, ¬Joined ((S.data p).coreBoundaryMap u) ((S.data p).coreBoundaryMap v) := by
  classical
  by_contra h
  apply hmin
  apply native_minimum_count_one_of_one_handle_components S hf
  intro p hp
  have hindex : 0 < Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rw [← nativeMorseIndex_eq_chart (S.data p).chart, hp]
    exact zero_lt_one
  apply native_attaching_component_of_pairwise_joined (S.data p) hindex
  intro u v
  by_contra huv
  exact h ⟨p, hp, u, v, huv⟩

theorem MorseCancellation.cancel_realized_higher_minimum {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f₀ : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : ManifoldMorse.IsMorse E f₀) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f₀) (hpzero : nativeMorseIndex E f₀ p = 0)
    (hqone : nativeMorseIndex E f₀ q = 1) (hrp : f₀ r < f₀ p) (hp : f₀ p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val))
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 j.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f₀).ncard := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ :=
    unique_connection_of_distinct_minimum_branches S hf₀.continuous G p r q hqone hpr hp u v hback
      hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, -, -, hpq, hconsecutive, hdesc, hmodels, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf₀ hm₀ S.distinct hV G hG hzero hdesc₀ hmodels₀ p r q
      hrp (hp.trans (S.lower_lt_value q)) hnoconnection
  let pf : ManifoldMorse.criticalPoints E f := ⟨p.val, by rw [hcrit]; exact p.property⟩
  let qf : ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
  have hconsecutivef : ∀ z : ManifoldMorse.criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) :=
    by
    intro z hz
    exact hconsecutive ⟨z.val, by rw [← hcrit]; exact z.property⟩ hz
  obtain ⟨T⟩ := ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  obtain ⟨g, hg, hmg, hcard, hcritg, hexterior⟩ :=
    cancel_unique_zero_one_connection cp cq hf hm ((hindices p p.property).trans hpzero)
      ((hindices q q.property).trans hqone) hV G hG (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj
      pf.property qf.property hpq (T.lower_lt_value pf) (T.value_lt_upper qf)
      (surgery_pair_band_isolation T pf qf hconsecutivef) hu hzback hunique hcp hcq
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation T pf qf hconsecutivef)
      hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinj (fun x hx => ((hcritg x).mp hx).1) hkeep
  exact ⟨g, hg, hmg, hinjg, hcard.trans (congrArg Set.ncard hcrit)⟩

theorem MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f₀ : M → ℝ} (S : AdaptedWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : ManifoldMorse.IsMorse E f₀)
    (hmin : nativeMorseCount E f₀ 0 ≠ 1) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f₀).ncard := by
  obtain ⟨q, hqone, u, v, hnot⟩ :=
    exists_native_one_handle_joining_components S.toSurgeryWindows hf₀ hmin
  obtain
    ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr, hp, hr, hback, hu, hv, -,
      hnoconnection⟩ :=
    S.realize_one_handle_minimum_branches hf₀ q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
    ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(S.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, S.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : f₀ p ≠ f₀ r := fun h => hpr (Subtype.ext (S.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels r p q
        hrzero hqone hlt hr v u hback hv hu (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels p r q
        hpzero hqone hgt hp u v hback hu hv hnoconnection

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) (x y : Hemisphere.Sphere 2)
    (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ z, g' z = e (g z)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              ((P \ { x, y } : Finset (Hemisphere.Sphere 2)) :
                    Set (Hemisphere.Sphere 2)) =
                  D.beltIntersectionPoints 2 g' ∧
                (∀ z ∈ P \ { x, y }, (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
                  (∑ z ∈ P \ { x, y }, (D.beltIntersectionSign 2 r g' z : ℤ)) =
                    ∑ z ∈ P, (D.beltIntersectionSign 2 r g z : ℤ) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hxB : x ∈ D.beltIntersectionPoints 2 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 2 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hg', hinj', hi', ht', hpoints, hgerm, hsign⟩ :=
    D.exists_signed_belt_cancellation_step hf hdim hindex hnull r g hg hinj hi ht x y hxB hyB hxy
  have hP' :
    ((P \ { x, y } : Finset (Hemisphere.Sphere 2)) : Set (Hemisphere.Sphere 2)) =
      D.beltIntersectionPoints 2 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Hemisphere.Sphere 2) (hz : z ∈ P \ { x, y }) :
    z ∈ D.beltIntersectionPoints 2 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, ⟨hg', hinj', hi', ht'⟩, hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact
      FiniteSignedCancellation.sum_sdiff_pair_of_eq P (D.beltIntersectionSign 2 r g)
        (D.beltIntersectionSign 2 r g') (x := x) (y := y) hx hy hxy
        (fun z hz => hsign z (hmem z hz))

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        ∃ P' : Finset (Hemisphere.Sphere 2),
          SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g' x = e (g x)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                (P' : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g' ∧
                  P' ⊆ P ∧
                    (∀ x ∈ P', (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                      (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)) =
                          ∑ x ∈ P, (D.beltIntersectionSign 2 r g x : ℤ) ∧
                        ∀ x ∈ P',
                          ∀ y ∈ P',
                            D.beltIntersectionSign 2 r g' x * D.beltIntersectionSign 2 r g' y ≠
                              -1 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  induction P using Finset.strongInductionOn generalizing g with
  | _ P
    ih =>
    by_cases hpair :
      ∃ x ∈ P, ∃ y ∈ P, D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨e₁, g₁, hiso₁, heq₁, hgood₁, hR, hgerm₁, hsum₁⟩ :=
        D.exists_finite_belt_cancellation_step hf hdim hindex hnull r P g hP hgood x y hx hy hxy
      let R : Finset (Hemisphere.Sphere 2) := P \ { x, y }
      have hsubpair : ({ x, y } : Finset (Hemisphere.Sphere 2)) ⊆ P := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hRlt : R ⊂ P := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨e₂, g₂, P₂, hiso₂, heq₂, hgood₂, hP₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih R hRlt g₁ hR hgood₁
      refine
        ⟨e₁.trans e₂, g₂, P₂, hiso₁.trans hiso₂, ?_, hgood₂, hP₂, hsub₂.trans Finset.sdiff_subset,
          ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change g₂ z = e₂ (e₁ (g z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hsub₂ hz))
    · refine
        ⟨Diffeomorph.refl _ _ _, g, P, SupportedDiffeomorph.isotopicToIdentity_refl,
          fun _ => rfl, hgood, hP, fun _ hx => hx, fun _ _ => Filter.EventuallyEq.refl _ _, rfl,
          ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ x, g' x = e (g x)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              D.beltIntersectionPoints 2 g' ⊆ D.beltIntersectionPoints 2 g ∧
                (∀ x ∈ D.beltIntersectionPoints 2 g',
                    (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                  (∀ hfin' : (D.beltIntersectionPoints 2 g').Finite,
                      D.beltIntersectionCount 2 r g' hfin' =
                        D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)) ∧
                    (D.beltIntersectionPoints 2 g').ncard =
                      (D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex
                            hgood)).natAbs := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let hfin := D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood
  obtain ⟨e, g', P', hiso, heq, hgood', hP', hsub, hgerm, hsum, hno⟩ :=
    D.exists_finite_belt_reduction hf hdim hindex hnull r hfin.toFinset g hfin.coe_toFinset hgood
  have hunit :
    ∀ x ∈ P', D.beltIntersectionSign 2 r g' x = 1 ∨ D.beltIntersectionSign 2 r g' x = -1 := by
    obtain ⟨hg', _, _, ht'⟩ := hgood'
    intro x hx
    exact D.beltIntersectionSign_unit hf 3 2 hindex r g' hg' ht' x (hP' ▸ hx)
  have hmem (x : Hemisphere.Sphere 2) (hx : x ∈ D.beltIntersectionPoints 2 g') : x ∈ P' := by
    change x ∈ (P' : Set (Hemisphere.Sphere 2))
    rw [hP']
    exact hx
  refine ⟨e, g', hiso, heq, hgood', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ P' := hmem x hx
    exact hfin.mem_toFinset.mp (hsub hxP)
  · intro x hx
    exact hgerm x (hmem x hx)
  · intro hfin'
    have hPfin : hfin'.toFinset = P' := by
      apply Finset.coe_injective
      exact hfin'.coe_toFinset.trans hP'.symm
    change (∑ x ∈ hfin'.toFinset, (D.beltIntersectionSign 2 r g' x : ℤ)) = _
    rw [hPfin]
    exact hsum
  · calc
      (D.beltIntersectionPoints 2 g').ncard = P'.card := by rw [← hP', Set.ncard_coe_finset]
      _ = (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)).natAbs :=
        (FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite P'
          (D.beltIntersectionSign 2 r g') hunit hno)
      _ = _ := congrArg Int.natAbs hsum

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount :
      (D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs =
        1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        ∃ x : Hemisphere.Sphere 2,
          SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ y, g' y = e (g y)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                D.beltIntersectionPoints 2 g' = { x } ∧
                  Set.range g' ∩ Set.range D.surgery.beltSphere = {g' x} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 2 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage :
    g' '' D.beltIntersectionPoints 2 g' = Set.range g' ∩ Set.range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' Set.range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [← himage, hx, Set.image_singleton]

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.remove_connections_of_index_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (n m : ℕ) (hqindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)
    (hppos : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1)
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1) := ⟨hqindex⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1) := ⟨hppos⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) n b.toHomeomorph
  have hα : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf n b
  have hB := (S.data p).belt_smooth hf m
  have hdim :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) <
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  obtain ⟨e, he, hdisjoint⟩ :=
    MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension hα hB hdim
  have hbasins :
    ∀ x : (S.data p).UpperLevel,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t (e x)) Filter.atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ := (S.transported_attaching_basin_iff hf p q n b.toHomeomorph horbit' x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hαx : e x ∈ Set.range (e ∘ α) := ⟨v, congrArg e hv⟩
    exact Set.disjoint_left.mp hdisjoint hαx hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := α (Classical.arbitrary (Hemisphere.Sphere n))
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hac hcb
      (MorseCancellation.surgery_pair_inner_band_regular p q hconsecutive hpa hbq)
      (S.data p).upper_regular z e he
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val e
      (fun x => (hgeometry x).2.1) (fun x => (hgeometry x).2.2) hend hleft hright
  refine ⟨V, G, hV, hG, fun x hx => (hzeros x).mpr (S.zero x hx), hneg, hgerms, ?_⟩
  exact
    FlowSuspension.no_connection_of_level_basin_disjointness S.flow G hf.continuous hqc hpc
      e (fun x => hback x q.val) (fun x => hforward x p.val) hbasins

theorem AdaptedWindows.remove_connections_of_nonincreasing_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  by_cases hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_upper_index_zero hf p q hpq hqzero⟩
  by_cases hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_lower_positive_zero hf p q hpq hpzero⟩
  exact
    S.remove_connections_of_index_le hf p q hpq hconsecutive
      (Module.finrank ℝ (S.data q).chart.NegativeCoordinates - 1)
      (Module.finrank ℝ (S.data p).chart.PositiveCoordinates - 1) (by omega) (by omega) hle

theorem AdaptedWindows.exchange_nonincreasing_native_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : MorseCancellation.nativeMorseIndex E f q ≤ MorseCancellation.nativeMorseIndex E f p) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            g p = f q ∧
              g q = f p ∧
                (∀ z,
                    f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                      g =ᶠ[𝓝 z] f) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                    Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
                      Nonempty (AdaptedWindows E g) ∧
                        (∀ z ∈ ManifoldMorse.criticalPoints E f,
                            MorseCancellation.nativeMorseIndex E g z =
                              MorseCancellation.nativeMorseIndex E f z) ∧
                          ∀ k,
                            MorseCancellation.nativeMorseCount E g k =
                              MorseCancellation.nativeMorseCount E f k := by
  have hle' :
    Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart,
      MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hle
  obtain ⟨V, G, hV, hG, hzeros, hneg, hgerms, hnoconnection⟩ :=
    S.remove_connections_of_nonincreasing_indices hf p q hpq hconsecutive hle'
  have hpgerm : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p p.property, S.critical_model_germ p] with y hy hmodel
    exact hy.trans hmodel
  have hqgerm : ∀ᶠ y in 𝓝 q.val, V y = (S.data q).chart.descentField y := by
    filter_upwards [hgerms q q.property, S.critical_model_germ q] with y hy hmodel
    exact hy.trans hmodel
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, -, hexterior, -, -, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV G hG hzeros
      hneg S.distinct (S.data p).chart (S.data q).chart hpgerm hqgerm hpband hqband hpq hqband
      hpband (MorseCancellation.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
      hnoconnection
  obtain ⟨hinj, hnew⟩ :=
    MorseCancellation.adapted_surgery_system_after_value_exchange S hg hmg p.property q.property hcrit
      hgp hgq hothers
  exact
    ⟨g, hg, hmg, hcrit, hgp, hgq, hexterior, hothers, hinj, hnew, hindices,
      MorseCancellation.nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

theorem MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f₀ : M → ℝ} (S₀ : AdaptedWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : ManifoldMorse.IsMorse E f₀) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              ∃ _ : AdaptedWindows E f,
                (∀ p q : ManifoldMorse.criticalPoints E f,
                    f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
                  ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧ nativeIndexDisorder E f = n
  have hex : ∃ n, P n :=
    ⟨nativeIndexDisorder E f₀, f₀, hf₀, hm₀, rfl, fun _ _ => rfl, S₀.distinct, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hindices, hinj, hdisorder⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  have horder :
    ∀ p q : ManifoldMorse.criticalPoints E f,
      f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
    by_contra hnot
    let _ := S.finite.fintype
    obtain ⟨p, q, hpq, hconsecutive, hinversion⟩ :=
      IndexDisorder.exists_adjacent_index_inversion (h :=
        fun x : ManifoldMorse.criticalPoints E f => f x)
        (fun x y h => Subtype.ext (hinj x.property y.property h))
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) hnot
    obtain ⟨g, hg, hmg, hcritg, hgp, hgq, -, hothers, hinjg, -, hindicesg, -⟩ :=
      S.exchange_nonincreasing_native_indices hf hm p q hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder E g < nativeIndexDisorder E f :=
      nativeIndexDisorder_exchange_lt S.finite hinj p q hpq hconsecutive hinversion hcritg hgp hgq
        hothers hindicesg
    have hindicesg₀ (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hminimal := Nat.find_min' hex ⟨g, hg, hmg, hcritg.trans hcrit, hindicesg₀, hinjg, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨f, hf, hm, hcrit, hindices, S, horder,
      nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

theorem MorseCancellation.minimal_excellent_morse_minimum_count_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 := by
  by_contra hmin
  obtain ⟨g, hg, hmg, hinjg, hcount⟩ :=
    exists_excellent_morse_reduction_of_multiple_minima S hf hm hmin
  exact minimal_excellent_morse_forbids_pair_removal hminimal hg hmg hinjg hcount

theorem MorseCancellation.minimal_excellent_morse_extreme_counts_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by
  refine ⟨minimal_excellent_morse_minimum_count_one S hf hm hminimal, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have hmin :=
    minimal_excellent_morse_minimum_count_one T hf.neg (isMorse_neg hm)
      (minimal_excellent_morse_neg hminimal)
  have hcounts := nativeMorseCount_neg hf hm (le_refl (Module.finrank ℝ E))
  rw [Nat.sub_self] at hcounts
  exact hcounts.symm.trans hmin

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_transverse_middle_belt_loop {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hq : MorseCancellation.nativeMorseIndex E f q = 1)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ 2) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ δ : C(Hemisphere.Sphere 1, { y : M // f y = a }),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ ∧
        Function.Injective δ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) ∧
            ∃ (z₀ : Hemisphere.Sphere 1) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (β :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1 → { y : M // f y = a }),
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧
                β v = δ z₀ ∧
                  NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) δ β
                      z₀ v ∧
                    (∀ᶠ w in 𝓝 v,
                        Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val)) ∧
                      (∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) ↔
                            z = z₀) ∧
                        ∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) :=
  by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf ha
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, htrans, hendpoints⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq 4 u hbranches hqa
      ha hlow (by omega) (by omega) (by omega)
  obtain ⟨t₀, ht₀⟩ := hreach z₀
  let za : { y : M // f y = a } := ⟨S.flow t₀ (γ z₀).val, ht₀⟩
  obtain ⟨D, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data q).upper_regular ha (γ z₀) za
  have hγsource (z : Circle) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hΓsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
        hγ.contMDiffAt
  let Γ : C(Circle, { y : M // f y = a }) := ⟨D ∘ γ, hΓsmooth.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro z w hzw
    exact hγi (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hΓd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
        (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (S.data q).surgery.beltSphere v = γ z₀ := ((hsingle z₀ v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (S.data q).surgery.beltSphere v ∈ D.source := hcross.symm ▸ hγsource z₀
  let β := D ∘ (S.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp))
  have hβcross : β v = Γ z₀ := congrArg D hcross
  have hΓtrans :
    NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) Γ β z₀ v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff D
          (hγ.mdifferentiableAt (by simp))
          (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp)) hcross (hγsource z₀)).mp
      (fun _ => htrans)
  have hβbasin :
    ∀ᶠ w in 𝓝 v, Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val) := by
    have hnear :=
      (((S.data q).belt_smooth hf 4).continuous.tendsto v) (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((S.data q).surgery.beltSphere w) hw
    change S.flow t ((S.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr
        ((S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hforward (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    have hbasin :
      Filter.Tendsto (fun s => S.flow s (Γ z).val) Filter.atTop (𝓝 q.val) ↔
        γ z ∈ Set.range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact
        (MorseCancellation.flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
          (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  have hΓends (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    rw [← ht]
    exact
      (hendpoints z).imp ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ p.val).mpr)
        ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr)
  let δ : C(Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨Γ ∘ MorseCancellation.standardCircleParametrization,
      Γ.continuous.comp MorseCancellation.standardCircleParametrization.continuous⟩
  let z := MorseCancellation.standardCircleParametrization.symm z₀
  have hz : MorseCancellation.standardCircleParametrization z = z₀ :=
    MorseCancellation.standardCircleParametrization.apply_symm_apply z₀
  have hδcross : β v = δ z := by
    change β v = Γ (MorseCancellation.standardCircleParametrization z)
    rw [hz]
    exact hβcross
  have hδtrans :
    NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) δ β z v := by
    intro _
    let B : EuclideanSpace ℝ (Fin 4) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v
    apply MorseCancellation.transverse_comp_standardCircle hΓsmooth B z
    rw [hz]
    exact hΓtrans hβcross
  refine
    ⟨δ, MorseCancellation.contMDiff_comp_standardCircle hΓsmooth,
      MorseCancellation.injective_comp_standardCircle hΓi,
      MorseCancellation.injective_derivative_comp_standardCircle hΓsmooth hΓd, z, v, β, hβ, hδcross,
      hδtrans, hβbasin, ?_, fun w => hΓends (MorseCancellation.standardCircleParametrization w)⟩
  intro w
  change
    Filter.Tendsto (fun t => S.flow t (Γ (MorseCancellation.standardCircleParametrization w)).val)
        Filter.atTop (𝓝 q.val) ↔
      _
  rw [hforward]
  exact
    ⟨fun hw => MorseCancellation.standardCircleParametrization.injective (hw.trans hz.symm), fun hw =>
      hw ▸ hz⟩

theorem SphereBoundary.exists_extension_immersive_on_sphere {E G H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x))
    (hdim : n + Module.finrank ℝ E < Module.finrank ℝ G) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ x : Metric.sphere (0 : E) 1, g x.1 = γ x) ∧
          ∀ x : Metric.sphere (0 : E) 1, Function.Injective (mfderiv 𝓘(ℝ, E) J g x.1) := by
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : Metric.sphere (0 : E) 1 → E) :=
    contMDiff_coe_sphere
  have hzero (x : Metric.sphere (0 : E) 1) : definingFunction x.1 = 0 :=
    (definingFunction_eq_zero_iff x.1).mpr x.property
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨g, hg, hhom, hderiv⟩ :=
    ManifoldImmersion.exists_compact_boundary_derivative_repair
      (⟨f, hf.continuous⟩ : C(E, N)) hf hb contDiff_definingFunction hzero hd
      (common_kernel_of_immersive_sphere_extension hf hext hγ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    exact (hhom.fst_eq_snd (hzero x)).symm.trans (hext x)
  · intro x
    exact hderiv x.1 ⟨x, rfl⟩

theorem exists_embedded_disk_extension_of_smooth_extension {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : Hemisphere.Ambient 2 → N}
    (hf : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ f) {γ : Hemisphere.Sphere 1 → N}
    (hext : ∀ x : Hemisphere.Sphere 1, f x.1 = γ x) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) J γ x)) (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J g x.1) := by
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]⟩
  have hd : 1 + Module.finrank ℝ (Hemisphere.Ambient 2) < Module.finrank ℝ G := by
    simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]
    omega
  obtain ⟨f₁, hf₁, hboundary₁, hderiv₁⟩ :=
    SphereBoundary.exists_extension_immersive_on_sphere (n := 1) hf hext hγderiv hd
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hC : IsClosed C := Metric.isClosed_sphere
  have hfixed : Set.InjOn f₁ (K ∩ C) := by
    intro x hx y hy hxy
    let xs : Hemisphere.Sphere 1 := ⟨x, hx.2⟩
    let ys : Hemisphere.Sphere 1 := ⟨y, hy.2⟩
    have hboundaryeq : γ xs = γ ys := (hboundary₁ xs).symm.trans (hxy.trans (hboundary₁ ys))
    exact congrArg Subtype.val (hγinj hboundaryeq)
  have hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J f₁ x) :=
    fun x hx => hderiv₁ ⟨x, hx.2⟩
  obtain ⟨g, hg, hhom, hemb, hderivg⟩ :=
    ManifoldImmersion.exists_relative_compact_embedding_twoDimensional f₁ hf₁
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]) hdim hK hC hfixed hderiv
  refine ⟨g, hg, ?_, hemb, fun x => hderivg x.1 x.property⟩
  intro x
  exact (hhom.fst_eq_snd x.property).symm.trans (hboundary₁ x)

theorem RadialFilling.contMDiffAt_direction {n : ℕ} (b : Hemisphere.Sphere n)
    {v : Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (direction b) v := by
  let V : TopologicalSpace.Opens (Hemisphere.Ambient (n + 1)) :=
    ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩
  have : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnorm :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, Hemisphere.Ambient (n + 1)) ∞
      (fun w : V => NormedSpace.normalize (w : Hemisphere.Ambient (n + 1))) :=
    contMDiff_normalize contMDiff_subtype_val (fun w => w.2)
  have hmem (w : V) :
    NormedSpace.normalize (w : Hemisphere.Ambient (n + 1)) ∈
      Metric.sphere (0 : Hemisphere.Ambient (n + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize w.2
  have hsphere := hnorm.codRestrict_sphere (n := n) hmem
  have hs :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (fun w : V => direction b w.1) := by
    apply hsphere.congr
    intro w
    exact Subtype.ext (direction_coe b w.2)
  exact (contMDiffAt_subtype_iff (U := V) (f := direction b) (x := ⟨v, hv⟩)).mp (hs ⟨v, hv⟩)

theorem RadialFilling.contMDiff_filling {n : ℕ} {G K M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace M]
    [ChartedSpace K M] {f : C(Hemisphere.Sphere n, M)} {c : M}
    (H : f.Homotopy (ContinuousMap.const _ c)) (b : Hemisphere.Sphere n)
    (hf : ContMDiff (𝓡 n) J ∞ f) (hH : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) J ∞ H)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) J ∞ (filling H b) := by
  intro v
  by_cases hinner : ‖v‖ < 1 / 4
  · apply (contMDiffAt_const (c := c)).congr_of_eventuallyEq
    have hn : {w : Hemisphere.Ambient (n + 1) | ‖w‖ < 1 / 4} ∈ 𝓝 v :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
    filter_upwards [hn] with w hw
    exact filling_eq_center H b htop (le_of_lt hw)
  · by_cases houter : 3 / 4 < ‖v‖
    · have hv : v ≠ 0 := norm_pos_iff.mp (by linarith)
      have hs := (hf (direction b v)).comp v (contMDiffAt_direction b hv)
      apply hs.congr_of_eventuallyEq
      have hn : {w : Hemisphere.Ambient (n + 1) | 3 / 4 < ‖w‖} ∈ 𝓝 v :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with w hw
      exact filling_eq_boundary H b hbottom (le_of_lt hw)
    · have hv : 0 < ‖v‖ := by linarith [le_of_not_gt hinner]
      have hunit : ‖v‖ < 1 := by linarith [le_of_not_gt houter]
      exact
        (hH (radialTime v, direction b v)).comp v (f := fun w => (radialTime w, direction b w))
          ((contMDiffAt_radialTime hv hunit).prodMk
            (contMDiffAt_direction b (norm_pos_iff.mp hv)))

theorem MorseCancellation.circle_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N]
    (γ : C(Hemisphere.Sphere 1, N)) (D : C(Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) :=
    { toFun := fun p => D (SphereCone.point p)
      continuous_toFun := D.continuous.comp SphereCone.continuous_point
      map_zero_left := by
        intro z
        have he :
          SphereCone.point (0, z) =
            (⟨z.val, Metric.sphere_subset_closedBall z.property⟩ : Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [SphereCone.point]
        rw [he]
        exact hboundary z
      map_one_left := by
        intro z
        have he :
          SphereCone.point (1, z) =
            (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [SphereCone.point]
        exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

theorem MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] (γ : C(Hemisphere.Sphere 1, N))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) (D : C(Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨c, ⟨H⟩⟩ := circle_nullhomotopy_of_disk γ D hboundary
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere 1 := ⟨v, hv⟩
  have hsmooth := RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  have hext := RadialFilling.filling_on_sphere H' b hlo
  exact exists_embedded_disk_extension_of_smooth_extension hsmooth hext hγinj hγderiv hdim

theorem AdaptedWindows.realize_unit_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (z : { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
                (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
                  (∀ x,
                      x ∉ ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                    (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                      Filter.Tendsto (fun t => G t z.val) Filter.atBot (𝓝 p.val) ∧
                        Filter.Tendsto (fun t => G t z.val) Filter.atTop (𝓝 q.val) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p.val) →
                                Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q.val) →
                                  ∃ t, G t z.val = x) ∧
                            (∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 y)) ∧
                              ∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop
                                    (𝓝 y) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount
  obtain ⟨z₀, -⟩ := Set.ncard_eq_one.mp hcount
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level ha
  obtain
    ⟨r, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband ha z₀ P hP
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val P
      (fun x y => (hgeometry x).2.1 y) (fun x y => (hgeometry x).2.2 y) hend hleft hright
  obtain ⟨z, hzb, hzf, hunique⟩ :=
    FlowSuspension.exists_unique_connection_of_unit_level_count S.flow G hf.continuous hpa
      hqa P (fun x => hback x p.val) (fun x => hforward x q.val) hcount
  exact
    ⟨V, G, z, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hzb, hzf, hunique,
      hback, hforward⟩

theorem AdaptedWindows.realize_unit_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∀ (α : X → { y : M // f y = a }) (β : Y → { y : M // f y = a }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
                β y = α x →
                  NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
                    (∀ᶠ u in 𝓝 x,
                        Filter.Tendsto (fun t => S.flow t (α u).val) Filter.atBot (𝓝 p.val)) →
                      (∀ᶠ u in 𝓝 y,
                          Filter.Tendsto (fun t => S.flow t (P (β u)).val) Filter.atTop
                            (𝓝 q.val)) →
                        ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
                              (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
                                (∀ z,
                                    z ∉ ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
                                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ w in 𝓝 z, V w = S.field w) ∧
                                    Filter.Tendsto (fun t => G t (α x).val) Filter.atBot
                                        (𝓝 p.val) ∧
                                      Filter.Tendsto (fun t => G t (α x).val) Filter.atTop
                                          (𝓝 q.val) ∧
                                        (∀ z,
                                            Filter.Tendsto (fun t => G t z) Filter.atBot
                                                (𝓝 p.val) →
                                              Filter.Tendsto (fun t => G t z) Filter.atTop
                                                  (𝓝 q.val) →
                                                ∃ t, G t (α x).val = z) ∧
                                          (∀ (z : { w : M // f w = a }) w,
                                              Filter.Tendsto (fun t => G t z.val) Filter.atBot
                                                  (𝓝 w) ↔
                                                Filter.Tendsto (fun t => S.flow t z.val)
                                                  Filter.atBot (𝓝 w)) ∧
                                            (∀ (z : { w : M // f w = a }) w,
                                                Filter.Tendsto (fun t => G t z.val) Filter.atTop
                                                    (𝓝 w) ↔
                                                  Filter.Tendsto (fun t => S.flow t (P z).val)
                                                    Filter.atTop (𝓝 w)) ∧
                                              let C : X × ℝ → M := fun u => G u.2 (α u.1).val
                                              let D : Y × ℝ → M := fun u => G u.2 (β u.1).val
                                              MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) C
                                                  (x, 0) ∧
                                                MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) D
                                                    (y, 0) ∧
                                                  C (x, 0) = (α x).val ∧
                                                    D (y, 0) = (α x).val ∧
                                                      (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                                                          Filter.Tendsto (fun t => G t (C u))
                                                            Filter.atBot (𝓝 p.val)) ∧
                                                        (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                                            Filter.Tendsto (fun t => G t (D u))
                                                              Filter.atTop (𝓝 q.val)) ∧
                                                          NativeTransversality.At
                                                            (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                                            𝓘(ℝ, E) C D (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, z, hV, hG, hzero, hdesc, hgerms, -, -, hunique, hback, hforward⟩ :=
    S.realize_unit_level_isotopy hf p q hpa hqa ha P hP hcount
  have hαG : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => G t (α u).val) Filter.atBot (𝓝 p.val) := by
    filter_upwards [hαbasin] with u hu
    exact (hback (α u) p.val).mpr hu
  have hβG : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => G t (β u).val) Filter.atTop (𝓝 q.val) := by
    filter_upwards [hβbasin] with u hu
    exact (hforward (β u) q.val).mpr hu
  have hxforward : Filter.Tendsto (fun t => G t (α x).val) Filter.atTop (𝓝 q.val) := by
    have hh := hβG.self_of_nhds
    rwa [hcross] at hh
  obtain ⟨s, hs⟩ := hunique (α x).val hαG.self_of_nhds hxforward
  have huniq (w : M) (hwb : Filter.Tendsto (fun t => G t w) Filter.atBot (𝓝 p.val))
    (hwf : Filter.Tendsto (fun t => G t w) Filter.atTop (𝓝 q.val)) : ∃ t, G t (α x).val = w := by
    obtain ⟨t, ht⟩ := hunique w hwb hwf
    refine ⟨t - s, ?_⟩
    rw [← hs, ← G.map_add, sub_add_cancel, ht]
  refine
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hαG.self_of_nhds, hxforward, huniq, hback, hforward, ?_⟩
  exact
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf ha hV G hG
      (fun w hw => hdesc w (ha w hw)) α β x y hα hβ hcross htrans hαG hβG

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.place_one_handle_in_unique_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧
        f p < S.toSurgeryWindows.lower q ∧
          ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
            Filter.Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
              Filter.atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := fun h => huv ((S.data q).attaching_isClosedEmbedding.injective h)
  obtain ⟨d, hd, ⟨r, hr, hru⟩, ⟨s, hs, hsv⟩⟩ :=
    MorseCancellation.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpu : Filter.Tendsto (fun t => S.flow t (d (α u)).val) Filter.atTop (𝓝 p.val) :=
    hunique r hr ▸ hru
  have hpv : Filter.Tendsto (fun t => S.flow t (d (α v)).val) Filter.atTop (𝓝 p.val) :=
    hunique s hs ▸ hsv
  refine
    ⟨d, hd, S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu, ?_⟩
  intro w
  rcases Metric.unitSphere_eq_two_points_of_finrank_eq_one hi u v huv w with rfl | rfl
  · exact hpu
  · exact hpv

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.realize_unique_minimum_one_handle_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (p q : ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    ∃ T : AdaptedWindows E f,
      (∀ r : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 r.val, T.field x = S.field x) ∧
        (∀ r, (T.data r).chart = (S.data r).chart) ∧
          (∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
              Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val)
                Filter.atTop (𝓝 p.val)) ∧
            ∀ r : ManifoldMorse.criticalPoints E f,
              r ≠ q →
                r ≠ p →
                  ∀ x,
                    ¬(Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 q.val) ∧
                        Filter.Tendsto (fun t => T.flow t x) Filter.atTop (𝓝 r.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, hpq, hall⟩ := S.place_one_handle_in_unique_minimum_basin hf p q hone hunique
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  have hVz : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0 := fun x hx =>
    (hzero x).mpr (S.zero x hx)
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
      (𝓝 p.val) :=
    (hforward _ p.val).mpr (hall w)
  have hno (r : ManifoldMorse.criticalPoints E f) (hrq : r ≠ q) (hrp : r ≠ p) (x : M) :
    ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val)) := by
    intro hx
    have hmono := FlowConstruction.antitone_flow_height hf G hG hVz hdesc x
    have hle : f r ≤ f q :=
      (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.2) 0).trans
        (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.1) 0)
    have hrq' : f r < f q :=
      lt_of_le_of_ne hle (fun h => hrq (Subtype.ext (S.distinct r.property q.property h)))
    have hrlow : f r < S.toSurgeryWindows.lower q :=
      (S.toSurgeryWindows.value_lt_upper r).trans (S.separated r q hrq')
    obtain ⟨t, ht⟩ :=
      FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
        (S.toSurgeryWindows.lower_lt_value q) hrlow
    let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
    have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
      (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
    have hzr : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 r.val) :=
      (MorseCancellation.flow_time_atTop_limit_iff G t x r.val).mpr hx.2
    obtain ⟨w, hw⟩ := (hbq z).mp hzq
    have hpz := hends w
    rw [hw] at hpz
    exact hrp (Subtype.ext (tendsto_nhds_unique hzr hpz))
  have hmodel (r : ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 r.val, V x = (S.data r).chart.descentField x := by
    filter_upwards [hgerms r r.property, S.critical_model_germ r] with x hx hxs
    exact hx.trans hxs
  obtain ⟨T, hfield, hflow, hchart⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow hf hm S.distinct hV G hG hVz hdesc
      (fun r => (S.data r).chart) hmodel
  refine ⟨T, ?_, hchart, ?_, ?_⟩
  · intro r
    rw [hfield]
    exact hgerms r r.property
  · intro w
    let z := (T.data q).surgery.attachingSphere w
    have hzq : Filter.Tendsto (fun t => T.flow t z.val) Filter.atBot (𝓝 q.val) :=
      (T.attaching_basin_iff hf q z).mpr ⟨w, rfl⟩
    obtain ⟨r₀, hr₀, r, hr, -, hrlim, hheight⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
        T.descent T.distinct z.val
    have hrq : (⟨r, hr⟩ : ManifoldMorse.criticalPoints E f) ≠ q := by
      intro heq
      have hlt := (hheight ((T.data q).lower_regular z.val z.property)).1
      have hrval : r = q.val := congrArg Subtype.val heq
      rw [hrval, z.property] at hlt
      nlinarith [sq_nonneg (T.data q).radius]
    have hrp : (⟨r, hr⟩ : ManifoldMorse.criticalPoints E f) = p := by
      by_contra hne
      apply hno ⟨r, hr⟩ hrq hne z.val
      rw [hflow] at hzq hrlim
      exact ⟨hzq, hrlim⟩
    exact (congrArg Subtype.val hrp) ▸ hrlim
  · intro r hrq hrp x
    rw [hflow]
    exact hno r hrq hrp x

theorem MorseCancellation.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        ManifoldMorse.IsMorse E g →
                          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                            (ManifoldMorse.criticalPoints E f).ncard ≤
                              (ManifoldMorse.criticalPoints E g).ncard) ∧
                    ∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        ManifoldMorse.IsMorse E g →
                          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                            (ManifoldMorse.criticalPoints E g).ncard =
                                (ManifoldMorse.criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  classical
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal₀⟩ := exists_minimal_excellent_morse_system E M
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
            (ManifoldMorse.criticalPoints E f).ncard =
                (ManifoldMorse.criticalPoints E f₀).ncard ∧
              nativeMorseCount E f 1 + nativeMorseCount E f 5 = n
  have hex : ∃ n, P n := ⟨_, f₀, hf₀, hm₀, S₀.distinct, rfl, rfl⟩
  obtain ⟨g, hg, hmg, hinjg, hcardg, hcostg⟩ := Nat.find_spec hex
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨f, hf, hm, hcrit, -, S, horder, hcounts⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points T hg hmg
  have hcardf :
    (ManifoldMorse.criticalPoints E f).ncard =
      (ManifoldMorse.criticalPoints E f₀).ncard := by rw [hcrit, hcardg]
  have hminimal :
    ∀ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
        ManifoldMorse.IsMorse E h →
          Set.InjOn h (ManifoldMorse.criticalPoints E h) →
            (ManifoldMorse.criticalPoints E f).ncard ≤
              (ManifoldMorse.criticalPoints E h).ncard := by
    intro h hh hmh hinjh
    rw [hcardf]
    exact hminimal₀ h hh hmh hinjh
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  refine ⟨f, hf, hm, S, horder, hmin, hmax, hminimal, ?_⟩
  intro h hh hmh hinjh hcardh
  rw [hcounts 1, hcounts 5, hcostg]
  exact Nat.find_min' hex ⟨h, hh, hmh, hinjh, hcardh.trans hcardf, rfl⟩

def DiskOnePointCollapse.collapse {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(MorseHandle.UnitDisk N, OnePoint N) :=
  ⟨fun z => interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z),
    interiorHomeomorph.onePointCongr.continuous.comp
      (OnePointCollapse.continuous_collapse boundary boundary_closed)⟩

theorem DiskOnePointCollapse.collapse_boundary {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ = 1) :
    collapse z = (OnePoint.infty) := by
  change interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) = (OnePoint.infty)
  rw [OnePointCollapse.collapse_of_mem boundary hz]
  rfl

theorem DiskOnePointCollapse.collapse_interior {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ < 1) :
    collapse z = ((OpenPartialHomeomorph.univUnitBall.symm (z : N) : N) : OnePoint N) := by
  change interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) = _
  rw [OnePointCollapse.collapse_of_not_mem boundary ((not_mem_boundary_iff z).mpr hz)]
  rfl

theorem DiskOnePointCollapse.collapse_eq_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z w : MorseHandle.UnitDisk N) :
    collapse z = collapse w ↔ z = w ∨ ‖(z : N)‖ = 1 ∧ ‖(w : N)‖ = 1 := by
  change
    interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) =
        interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary w) ↔
      _
  rw [interiorHomeomorph.onePointCongr.injective.eq_iff, OnePointCollapse.collapse_eq_iff]
  rfl

theorem DiskOnePointCollapse.collapse_compress {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : collapse (compress x) = (x : OnePoint N) := by
  rw [collapse_interior _ (norm_compress_lt x)]
  exact
    congrArg (fun y : N => (y : OnePoint N))
      (OpenPartialHomeomorph.univUnitBall.left_inv (Set.mem_univ x))

theorem DiskOnePointCollapse.collapse_eq_coe_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (x : N) :
    collapse z = (x : OnePoint N) ↔ z = compress x := by
  rw [← collapse_compress x, collapse_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact ((ne_of_lt (norm_compress_lt x)) h.2).elim
  · exact Or.inl

theorem DiskOnePointCollapse.collapse_eq_zero_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) :
    collapse z = ((0 : N) : OnePoint N) ↔ (z : N) = 0 := by
  rw [collapse_eq_coe_iff]
  constructor
  · intro hz
    exact (congrArg Subtype.val hz).trans compress_zero
  · intro hz
    exact Subtype.ext (hz.trans compress_zero.symm)

theorem DiskOnePointCollapse.collapse_eq_infty_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) :
    collapse z = (OnePoint.infty) ↔ ‖(z : N)‖ = 1 := by
  by_cases hz : ‖(z : N)‖ = 1
  · rw [collapse_boundary z hz]
    exact iff_of_true rfl hz
  · rw [collapse_interior z ((not_mem_boundary_iff z).mp hz)]
    exact iff_of_false (OnePoint.coe_ne_infty _) hz

theorem ClosedHandleCore.collapseMaps_agree {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P)
    (haz : oldInclusion A h a = handleInclusion A h z) :
    ((OnePoint.infty) : OnePoint N) = DiskOnePointCollapse.collapse z.1 := by
  have heq : (a : X) = h z := congrArg Subtype.val haz
  have hz := (hface z).mp (heq ▸ a.property)
  exact (DiskOnePointCollapse.collapse_boundary z.1 hz).symm

def ClosedHandleCore.collapseMap {N P X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    C(↥(A ∪ Set.range h), OnePoint N) :=
  ClosedCover.mapOfClosedPieces (oldInclusion A h) (handleInclusion A h) (old_closed A h hA)
    (handle_closed A h hh) (pieces_cover A h) (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface)

theorem ClosedHandleCore.collapseMap_old {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A) :
    collapseMap A h hA hh hface (oldInclusion A h a) = (OnePoint.infty) :=
  ClosedCover.mapOfClosedPieces_left (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) a

theorem ClosedHandleCore.collapseMap_handle {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    collapseMap A h hA hh hface (handleInclusion A h z) =
      DiskOnePointCollapse.collapse z.1 :=
  ClosedCover.mapOfClosedPieces_right (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) z

theorem EmbeddedCellAttachment.collapseMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (a : D.old)
    (z : MorseHandle.UnitDisk N) (haz : (a : X) = D.cell z) :
    ((OnePoint.infty) : OnePoint N) = DiskOnePointCollapse.collapse z :=
  (DiskOnePointCollapse.collapse_boundary z ((D.boundary z).mp (haz ▸ a.property))).symm

def EmbeddedCellAttachment.collapseMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(X, OnePoint N) :=
  ClosedCover.mapOfClosedPieces Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old (OnePoint.infty))
    DiskOnePointCollapse.collapse D.collapseMaps_agree

theorem EmbeddedCellAttachment.collapseMap_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (a : D.old) :
    D.collapseMap a = (OnePoint.infty) :=
  ClosedCover.mapOfClosedPieces_left Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) DiskOnePointCollapse.collapse
    D.collapseMaps_agree a

theorem EmbeddedCellAttachment.collapseMap_cell {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (z : MorseHandle.UnitDisk N) :
    D.collapseMap (D.cell z) = DiskOnePointCollapse.collapse z :=
  ClosedCover.mapOfClosedPieces_right Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) DiskOnePointCollapse.collapse
    D.collapseMaps_agree z

theorem EmbeddedCellAttachment.collapseMap_infty_iff {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = (OnePoint.infty) ↔ x ∈ D.old := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · exact iff_of_true (D.collapseMap_old ⟨x, hx⟩) hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_infty_iff, D.boundary]

theorem OnePointCover.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] OnePointCover.instLocal1 in
private def OnePointCover.spherePunctureHomeomorph (n : ℕ)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({ a }ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) a).symm).trans
    ((stereographic' n a).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

attribute [local instance] OnePointCover.instLocal1 in
def OnePointCover.punctureHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : OnePoint N) :
    ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ N)) := by
  let e : OnePoint N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let es : ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ ↥({e a}ᶜ : Set _) :=
    e.subtype
      (fun x => by
        change x ≠ a ↔ e x ≠ e a
        exact e.injective.ne_iff.symm)
  exact es.trans (spherePunctureHomeomorph _ (e a))

attribute [local instance] OnePointCover.instLocal1 in
theorem OnePointCover.oldPatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (oldPatch (N := N)) :=
  (punctureHomeomorph ((0 : N) : OnePoint N)).contractibleSpace

attribute [local instance] OnePointCover.instLocal1 in
theorem OnePointCover.finitePatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (finitePatch (N := N)) :=
  (punctureHomeomorph (OnePoint.infty : OnePoint N)).contractibleSpace

attribute [local instance] OnePointCover.instLocal1 in
theorem OnePointCover.overlap_subset_range {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∩ finitePatch ⊆ Set.range (OnePoint.some : N → _) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx.2 rfl).elim
  | coe x => exact ⟨x, rfl⟩

attribute [local instance] OnePointCover.instLocal1 in
theorem OnePointCover.overlap_preimage {N : Type*} [NormedAddCommGroup N] :
    (OnePoint.some : N → OnePoint N) ⁻¹' (oldPatch ∩ finitePatch) = {u : N | u ≠ 0} := by
  ext x
  change ((x : OnePoint N) ≠ ((0 : N) : OnePoint N) ∧ (x : OnePoint N) ≠ OnePoint.infty) ↔ x ≠ 0
  constructor
  · rintro ⟨h, -⟩ hx
    exact h (congrArg (OnePoint.some : N → OnePoint N) hx)
  · intro hx
    exact ⟨fun h => hx (OnePoint.coe_injective h), OnePoint.coe_ne_infty x⟩

attribute [local instance] OnePointCover.instLocal1 in
def OnePointCover.overlapHomeomorph {N : Type*} [NormedAddCommGroup N] :
    PuncturedRadial.Space N ≃ₜ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Homeomorph.setCongr overlap_preimage.symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange overlap_subset_range)

attribute [local instance] OnePointCover.instLocal1 in
theorem OnePointCover.overlapHomeomorph_apply {N : Type*} [NormedAddCommGroup N]
    (u : PuncturedRadial.Space N) : (overlapHomeomorph u).val = (u.val : OnePoint N) :=
  rfl

attribute [local instance] OnePointCover.instLocal1 in
def OnePointCover.overlapSphereEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans overlapHomeomorph.toHomotopyEquiv

theorem EmbeddedCellAttachment.collapseMap_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = ((0 : N) : OnePoint N) ↔ D.cell ⟨0, by simp⟩ = x := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · rw [D.collapseMap_old ⟨x, hx⟩]
    constructor
    · intro h
      exact (OnePoint.infty_ne_coe (0 : N) h).elim
    · intro h
      rw [← h, D.boundary] at hx
      simp at hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg D.cell (Subtype.ext hz.symm)
    · intro hz
      exact (congrArg Subtype.val (D.cell_closed.injective hz)).symm

theorem EmbeddedCellAttachment.collapseMaps_oldNeighborhood {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.oldNeighborhood (OnePointCover.oldPatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ ((0 : N) : OnePoint N)
  intro h
  have heq := (D.collapseMap_eq_zero_iff x).mp h
  rw [← heq, D.cell_mem_oldNeighborhood_iff] at hx
  norm_num at hx

theorem EmbeddedCellAttachment.collapseMaps_diskPatch {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.diskPatch (OnePointCover.finitePatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ OnePoint.infty
  exact fun h => hx ((D.collapseMap_infty_iff x).mp h)

def EmbeddedCellAttachment.collapseOverlapMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch),
      ↥(OnePointCover.oldPatch (N := N) ∩ OnePointCover.finitePatch)) :=
  CoverNaturality.mapOn D.collapseMap _ _
    (CoverNaturality.map_intersection _ _ _ _ D.collapseMap D.collapseMaps_oldNeighborhood
      D.collapseMaps_diskPatch)

theorem EmbeddedCellAttachment.collapseOverlap_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.collapseOverlapMap (D.overlapSphereEquiv u) =
      OnePointCover.overlapSphereEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos u := by
  apply Subtype.ext
  change
    D.collapseMap (D.cell (DiskAnnulus.middleDisk u)) =
      ((OnePointCover.overlapRadius • (u : N) : N) : OnePoint N)
  rw [D.collapseMap_cell,
    DiskOnePointCollapse.collapse_interior _ (DiskAnnulus.middleDisk_mem u).2]
  apply congrArg (OnePoint.some : N → OnePoint N)
  change
    (Real.sqrt (1 - ‖(3 / 4 : ℝ) • (u : N)‖ ^ 2))⁻¹ • ((3 / 4 : ℝ) • (u : N)) =
      OnePointCover.overlapRadius • (u : N)
  rw [DiskAnnulus.norm_middle, smul_smul]
  rfl

theorem EmbeddedCellAttachment.collapseOverlap_comp_sphere {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) :
    D.collapseOverlapMap.comp D.overlapSphereEquiv.toFun =
      (OnePointCover.overlapSphereEquiv (N := N) OnePointCover.overlapRadius
          OnePointCover.overlapRadius_pos).toFun :=
  ContinuousMap.ext D.collapseOverlap_sphere

def OnePointCover.overlapHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(oldPatch (N := N) ∩ finitePatch)) k :=
  SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k

def OnePointCover.sphereConnecting {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (overlapHomologyEquiv r hr k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism oldPatch finitePatch oldPatch_open
      finitePatch_open cover k)

theorem OnePointCover.sphereConnecting_injective {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Function.Injective (sphereConnecting (N := N) r hr k) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  have hi :
    Function.Injective
      (SingularMayerVietoris.connectingHomomorphism (oldPatch (N := N)) finitePatch oldPatch_open
        finitePatch_open cover k) :=
    Suspension.contractibleCoverConnecting_injective (oldPatch (N := N)) finitePatch
      oldPatch_open finitePatch_open cover k
  exact (overlapHomologyEquiv (N := N) r hr k).symm.injective.comp hi

def OnePointCover.sphereHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (k + 1) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  exact
    (Suspension.contractibleCoverHomologyHigherEquiv oldPatch finitePatch oldPatch_open
          finitePatch_open cover k).trans
      (overlapHomologyEquiv r hr (k + 1)).symm

theorem EmbeddedCellAttachment.collapse_overlapHomology_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (D.overlapHomologyEquiv k a) =
      OnePointCover.overlapHomologyEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k a := by
  change
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap _ k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    D.collapseOverlap_comp_sphere]

theorem EmbeddedCellAttachment.collapse_connecting_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap D.collapseMap (k + 1) a) =
      D.cellConnectingMap k a := by
  apply
    (OnePointCover.overlapHomologyEquiv (N := N) OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k).injective
  change
    OnePointCover.overlapHomologyEquiv _ _ k
        ((OnePointCover.overlapHomologyEquiv _ _ k).symm _) =
      OnePointCover.overlapHomologyEquiv _ _ k ((D.overlapHomologyEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.collapse_overlapHomology_compare,
    LinearEquiv.apply_symm_apply]
  exact
    (CoverNaturality.connecting_naturality_apply D.oldNeighborhood D.diskPatch
        OnePointCover.oldPatch OnePointCover.finitePatch D.collapseMap
        D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover OnePointCover.oldPatch_open
        OnePointCover.finitePatch_open OnePointCover.cover k a).symm

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.attachmentCollapseMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap),
      OnePoint d.chart.NegativeCoordinates) :=
  ClosedHandleCore.collapseMap _ d.handleMap (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.upperCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C({ y : M // f y ≤ f p + d.radius ^ 2 }, OnePoint d.chart.NegativeCoordinates) :=
  (d.attachmentCollapseMap hf).comp d.attachmentHomeomorph.symm.toHomotopyEquiv.toFun

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap)) :
    d.upperCollapseMap hf (d.attachmentHomeomorph x) = d.attachmentCollapseMap hf x := by
  change d.attachmentCollapseMap hf (d.attachmentHomeomorph.symm (d.attachmentHomeomorph x)) = _
  exact congrArg (d.attachmentCollapseMap hf) (d.attachmentHomeomorph.symm_apply_apply x)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_old {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : { y : M // f y ≤ f p - d.radius ^ 2 }) :
    d.upperCollapseMap hf (d.realizedLowerInclusion x) = (OnePoint.infty) := by
  change
    d.upperCollapseMap hf
        (d.attachmentHomeomorph (ClosedHandleCore.oldInclusion _ d.handleMap x)) =
      (OnePoint.infty)
  rw [d.upperCollapse_realization]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ x

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_handle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z : d.HandleDomain) :
    d.upperCollapseMap hf (d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩) =
      DiskOnePointCollapse.collapse z.1 := by
  exact
    (d.upperCollapse_realization hf
          (ClosedHandleCore.handleInclusion _ d.handleMap z)).trans
      (ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _ z)

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.levelCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(d.UpperLevel, OnePoint d.chart.NegativeCoordinates) :=
  (d.upperCollapseMap hf).comp ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_realized {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (y : d.UpperLevel) (x : ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap))
    (hy : (y : M) = (d.attachmentHomeomorph x).val) :
    d.levelCollapseMap hf y = d.attachmentCollapseMap hf x := by
  change d.upperCollapseMap hf ⟨y.val, y.property.le⟩ = _
  have heq :
    (⟨y.val, y.property.le⟩ : { z : M // f z ≤ f p + d.radius ^ 2 }) = d.attachmentHomeomorph x :=
    Subtype.ext hy
  rw [heq, d.upperCollapse_realization]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (r) :
    d.levelCollapseMap hf (d.surgery.newExterior r) = (OnePoint.infty) := by
  rw [d.levelCollapse_realized hf _ _ (d.newExterior_eq r)]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ ⟨r.val, r.property.1.le⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.surgery.newPiece z) =
      DiskOnePointCollapse.collapse
        (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1) := by
  rw [d.levelCollapse_realized hf _ _ (d.newPiece_eq z)]
  exact
    ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _
      (d.chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2))

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : d.UpperLevel) :
    d.levelCollapseMap hf x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ Set.range d.surgery.beltSphere := by
  have hx : x ∈ Set.range d.surgery.newExterior ∪ Set.range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hx with ⟨r, rfl⟩ | ⟨z, rfl⟩
  · rw [d.levelCollapse_newExterior]
    exact iff_of_false (OnePoint.infty_ne_coe _) (d.surgery.newExterior_avoids r)
  · rw [d.levelCollapse_newPiece, DiskOnePointCollapse.collapse_eq_zero_iff,
      d.surgery.newPiece_mem_belt_iff]
    rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.upperCollapseMap hf).comp (d.coreUnionHomotopyEquiv hf).toFun =
      (d.coreCellPresentation hf).collapseMap := by
  apply ContinuousMap.ext
  rintro ⟨x, hx | ⟨u, rfl⟩⟩
  · exact
      (d.upperCollapse_old hf ⟨x, hx⟩).trans
        ((d.coreCellPresentation hf).collapseMap_old ⟨⟨x, Or.inl hx⟩, hx⟩).symm
  · change
      d.upperCollapseMap hf
          (d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩) =
        (d.coreCellPresentation hf).collapseMap ((d.coreCellPresentation hf).cell u)
    rw [d.upperCollapse_handle, (d.coreCellPresentation hf).collapseMap_cell]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k) :
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (d.cellTotalHomologyEquiv hf k a) =
      SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).collapseMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k a) =
      _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    d.upperCollapse_coreCell]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a) =
      d.morseConnectingMap hf k a := by
  obtain ⟨b, rfl⟩ := (d.cellTotalHomologyEquiv hf (k + 1)).surjective a
  rw [d.upperCollapseHomology_coreCell, (d.coreCellPresentation hf).collapse_connecting_compare,
    d.morseConnecting_compare]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 2)) :
    OnePointCover.sphereHomologyEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) =
      d.morseConnectingMap hf (k + 1) a :=
  d.upperCollapse_connecting_compare hf (k + 1) a

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1)) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) := by
  rw [d.morse_exact_at_upper hf k]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a = 0 ↔
      d.morseConnectingMap hf k a = 0
  rw [← d.upperCollapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact
      (OnePointCover.sphereConnecting_injective OnePointCover.overlapRadius
          OnePointCover.overlapRadius_pos k)
        (h.trans (map_zero _).symm)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k)] :
    Function.Surjective (d.morseConnectingMap hf k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.coreBoundaryHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_attachingSphere hf k hk] at ha
  exact ha

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } (k + 1))] :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2)) := by
  intro a
  let C :=
    OnePointCover.sphereHomologyEquiv (N := d.chart.NegativeCoordinates)
      OnePointCover.overlapRadius OnePointCover.overlapRadius_pos k
  obtain ⟨b, hb⟩ := d.morseConnecting_surjective_of_lower hf (k + 1) (by omega) (C a)
  refine ⟨b, C.injective ?_⟩
  exact (d.upperCollapse_homology_equiv_compare hf k b).trans hb

def LocalDegree.NativeNeighborhood.overlapSphereEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥({ x }ᶜ ∩ openSet x d) :=
  (PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
        d.innerBoundary.radius_pos
        (by
          rw [d.innerBoundary_radius]
          exact half_lt_self d.radius_pos)).trans
    (puncturedHomeomorph x d).toHomotopyEquiv

def LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥(Pᶜ ∩ D.neighborhood x) :=
  (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).trans
    (Homeomorph.setCongr (D.overlap_eq x).symm).toHomotopyEquiv

theorem LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (u : Metric.sphere (0 : E) 1) :
    (D.overlapSphereEquiv x u).val =
      NativeParametrization.centered (x : M) ((D.data x).innerBoundary.radius • (u : E)) :=
  rfl

theorem LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.overlapMap x).comp (D.overlapSphereEquiv x).toFun = (D.data x).innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    LocalDegree.BoundaryData.map_coe]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.beltClosedDiskMap z) =
      DiskOnePointCollapse.collapse
        (MorseHandle.beltFaceDiskMap
          (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1)) := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.levelCollapse_newPiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    d.levelCollapseMap hf x = (d.collapseNormal x : OnePoint d.chart.NegativeCoordinates) := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  have hz := (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx
  rw [d.levelCollapse_beltClosedDiskMap,
    DiskOnePointCollapse.collapse_interior _
      ((MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val).mpr hz)]
  unfold collapseNormal
  rw [d.beltNormal_beltClosedDiskMap, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  rfl

theorem SphereNormalCoordinates.normalJacobian_smul_mul_pow {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) :
    normalJacobian j x (c • A) * c ^ Module.finrank ℝ N = normalJacobian j x A := by
  have hB := normalDerivative_smul_isInvertible A hA c hc
  have hcomp : A.comp A.inverse = ContinuousLinearMap.id ℝ N := by
    ext y
    exact hA.self_apply_inverse y
  have hdet : ((c • A).comp A.inverse).det = c ^ Module.finrank ℝ N := by
    rw [ContinuousLinearMap.smul_comp, hcomp]
    change (c • (LinearMap.id : N →ₗ[ℝ] N)).det = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hid : (A.comp A.inverse).det = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  have h :=
    (normalJacobian_mul_chartDet j x (c • A) hB A.inverse).trans
      (normalJacobian_mul_chartDet j x A hA A.inverse).symm
  simpa only [hdet, hid, mul_one] using h

theorem SphereNormalCoordinates.sign_normalJacobian_smul_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : 0 < c) :
    SignType.sign (normalJacobian j x (c • A)) = SignType.sign (normalJacobian j x A) := by
  have h := congrArg SignType.sign (normalJacobian_smul_mul_pow j x A hA c hc.ne')
  have hp : SignType.sign (c ^ Module.finrank ℝ N) = 1 := sign_eq_one_iff.mpr (pow_pos hc _)
  simpa only [sign_mul, hp, mul_one] using h

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x).IsInvertible)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    SignType.sign
        (SphereNormalCoordinates.normalJacobian j x
          (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
      d.beltIntersectionSign m j g x := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hA) hx]
  exact
    SphereNormalCoordinates.sign_normalJacobian_smul_pos j x _ hA _
      (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        SignType.sign
            (SphereNormalCoordinates.normalJacobian j x
              (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
          d.beltIntersectionSign m j g x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact d.collapseNormal_comp_sign m j g x hAi ⟨v, hv⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x).IsInvertible :=
  by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hAi) ⟨v, hv⟩]
  exact
    SphereNormalCoordinates.normalDerivative_smul_isInvertible A hAi _
      (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos).ne'

attribute [local instance 100] Classical.propDecidable in
abbrev ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) :=
  LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin m))
    (d.beltIntersectionPoints m g) (d.collapseNormal ∘ g) (g ⁻¹' d.surgery.NewInterior)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      Nonempty (d.CollapseNeighborhoods m g) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  have hfin := d.finite_beltIntersectionPoints hf n m hdim g hg hinj ht
  apply LocalDegree.nonempty_separatedNeighborhoods (EuclideanSpace ℝ (Fin m)) hfin
  · exact fun x hx => d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  · exact fun x hx => d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  · intro x hx
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.attachingCollapse {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    C(Hemisphere.Sphere m, OnePoint d.chart.NegativeCoordinates) :=
  (d.levelCollapseMap hf).comp g

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (x : Hemisphere.Sphere m) :
    d.attachingCollapse hf m g x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ d.beltIntersectionPoints m g :=
  d.levelCollapse_zero_iff hf (g x)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    Set.MapsTo (d.attachingCollapse hf m g) (d.beltIntersectionPoints m g)ᶜ
      OnePointCover.oldPatch := by
  intro x hx hzero
  exact hx ((d.attachingCollapse_zero_iff hf m g x).mp hzero)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    Set.MapsTo (d.attachingCollapse hf m g) (D.neighborhood i) OnePointCover.finitePatch := by
  intro x hx
  have hnew : g x ∈ d.surgery.NewInterior := D.neighborhood_subset i hx
  change d.levelCollapseMap hf (g x) ≠ OnePoint.infty
  rw [d.levelCollapse_eq_coe_collapseNormal hf hnew]
  exact OnePoint.coe_ne_infty _

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.collapseOverlapMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    C(↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i),
      ↥(OnePointCover.oldPatch (N := d.chart.NegativeCoordinates) ∩
          OnePointCover.finitePatch)) :=
  CoverNaturality.mapOn (d.attachingCollapse hf m g) _ _
    (fun _ hx =>
      ⟨d.attachingCollapse_maps_old hf m g hx.1,
        d.attachingCollapse_maps_neighborhood hf m g D i hx.2⟩)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    d.collapseOverlapMap hf m g D i =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    d.levelCollapseMap hf (g x.val) =
      (OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [OnePointCover.overlapHomeomorph_apply,
    LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact d.levelCollapse_eq_coe_collapseNormal hf (D.neighborhood_subset i x.property.2)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    (d.collapseOverlapMap hf m g D i).comp (D.overlapSphereEquiv i).toFun =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
        (D.data i).innerBoundary.map := by
  rw [d.collapseOverlapMap_eq hf m g D i, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

def ManifoldMorse.SurgeryWindows.BandData.homologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } k :=
  SingularHomology.homeomorphHomologyEquiv D.sublevelHomeomorph k

theorem ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val → 2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } 1) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          Subsingleton
            (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) }
              1) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 1 one_ne_zero
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n, hn'⟩) + (S.data (S.point ⟨n, hn'⟩)).radius ^ 2 } 1) :=
        ih hn' (by omega)
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl
      let H :=
        (S.data (S.point ⟨n, hn'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨n + 1, hn⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
            1) :=
        (SingularHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton
      exact
        (S.data (S.point ⟨n + 1, hn⟩)).upperHomologyOne_subsingleton hf.continuous
          (hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj)
  have hp : j.val - 1 < S.count := by omega
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val - 1, hp⟩) + (S.data (S.point ⟨j.val - 1, hp⟩)).radius ^ 2 }
        1) :=
    hupper (j.val - 1) hp (by omega)
  obtain ⟨T, _, hT, _⟩ :=
    S.exists_consecutiveBandBridge hf ⟨j.val - 1, hp⟩ j (by change j.val - 1 + 1 = j.val; omega)
  let H :=
    (S.data (S.point ⟨j.val - 1, hp⟩)).bandSublevelHomeomorph (S.data (S.point j)) T.toHomeomorph
      hT
  exact (SingularHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton

theorem ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  let := d.attachingHomology_subsingleton_of_index k hk hindex hne
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf k hk

def LinearSphereAction.sphereHomotopyEquiv {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₕ Metric.sphere (0 : F) 1 :=
  (LocalDegree.linearSphereEquiv B 1 zero_lt_one).trans
    (PuncturedRadial.sphereHomotopyEquiv 1 zero_lt_one).symm

theorem LinearSphereAction.sphereHomotopyEquiv_toFun {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    (sphereHomotopyEquiv B).toFun = sphereMap B.toContinuousLinearMap B.injective :=
  normalized_linearSphereMap B 1 zero_lt_one

def LinearSphereAction.homologyEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : F) 1) k :=
  SingularHomology.homotopyEquivHomologyEquiv (sphereHomotopyEquiv B) k

theorem LinearSphereAction.homologyEquiv_apply {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k) :
    homologyEquiv B k a =
      SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) k
        a := by
  change SingularMayerVietoris.singularHomologyMap (sphereHomotopyEquiv B).toFun k a = _
  rw [sphereHomotopyEquiv_toFun]

def LocalDegree.NativeNeighborhood.sphereConnecting {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k :=
  (SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d)
        k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism { x }ᶜ (openSet x d)
      isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k)

def LocalDegree.NativeNeighborhood.sphereHomologyEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] [ContractibleSpace ({ x }ᶜ : Set M)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) (k + 1) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact
    (Suspension.contractibleCoverHomologyHigherEquiv { x }ᶜ (openSet x d)
          isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k).trans
      (SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d) (k + 1)).symm

theorem SpherePoint.chart_radial_frame_comp {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
            0).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toContinuousLinearMap) =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
          0) := by
  apply ContinuousLinearMap.ext
  intro z
  have hD :=
    congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] V => A z.2)
      (chart_transition_ambient_derivative x y R he)
  have hcenter :
    R (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) =
      (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) := by
    rw [NativeParametrization.centered_zero, NativeParametrization.centered_zero]
    exact congrArg Subtype.val he
  change
    z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) +
        (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0)
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he z.2) =
      R
        (z.1 • (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) +
          (fderiv ℝ (fun u => (NativeParametrization.centered x u : V)) 0) z.2)
  rw [map_add, map_smul, hcenter]
  exact
    congrArg
      (fun v : V =>
        z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) + v)
      hD

theorem LocalDegree.BoundaryData.normalized_homology_compare {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (b : LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap k =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) k := by
  change
    SingularMayerVietoris.singularHomologyMap (PuncturedRadial.toSphere.comp b.map) k = _
  rw [SingularHomology.singularHomologyMap_comp, b.homology_compare, ←
    SingularHomology.singularHomologyMap_comp,
    LinearSphereAction.normalized_linearSphereMap]

theorem LocalDegree.BoundaryData.normalized_homology_eq_sign_smul {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) {f : EuclideanSpace ℝ (Fin (n + 2)) → F}
    {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : LocalDegree.BoundaryData f L s) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1) a =
      (SignType.sign (L.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [b.normalized_homology_compare]
  exact LinearSphereAction.homology_relative_sign n L B k a

def SphereNormalCoordinates.chartJacobian {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) (z : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  ((chartRadialFrame c z).comp j'.symm.toContinuousLinearMap).det

theorem SphereNormalCoordinates.chartJacobian_ne_zero {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) : chartJacobian c j B z ≠ 0 :=
  (RegularValues.bijective_iff_det_ne_zero _).mp
    ((bijective_chartRadialFrame c hz).comp
      ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans
          j).symm.bijective)

theorem SphereNormalCoordinates.chartJacobian_factor {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)) *
        (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      chartJacobian c j B z := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] F := mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)
  let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) c z
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  have hd : fderiv ℝ (f ∘ c) z = A.comp C := by
    have h := mfderiv_comp z hf (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hB : (B.symm.toContinuousLinearMap.comp A).IsInvertible :=
    (show B.symm.toContinuousLinearMap.IsInvertible from ⟨B.symm, rfl⟩).comp hA
  have h := normalJacobian_mul_chartDet j' (c z) (B.symm.toContinuousLinearMap.comp A) hB C
  rw [normalJacobian_change_normal_model j B (c z) A hA] at h
  change normalJacobian j (c z) A * _ = _
  rw [hd]
  rw [← ContinuousLinearMap.comp_assoc]
  apply h.trans
  unfold chartJacobian
  rw [chartRadialFrame_eq c hz]

theorem SphereNormalCoordinates.chartJacobian_sign_factor {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    SignType.sign (chartJacobian c j B z) *
        SignType.sign (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      SignType.sign (normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z))) := by
  have h := chartJacobian_factor c j B hz f hf hA
  apply sign_factor _ h
  intro hd
  rw [hd, MulZeroClass.mul_zero] at h
  exact chartJacobian_ne_zero c j B hz h.symm

theorem SpherePoint.chart_radial_frame_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)
    (j : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] V) :
    ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).det *
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
                0).comp
            j.symm.toContinuousLinearMap).det := by
  let L := NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he
  let Q := (ContinuousLinearMap.id ℝ ℝ).prodMap L.toContinuousLinearMap
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (Q.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = L.toLinearEquiv.toLinearMap.det := by
    have hconj : T.det = Q.det := LinearMap.det_conj Q.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) L.toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).comp
        T =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
              0).comp
          j.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change
      SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y) 0
          (j.symm (j (Q (j.symm v)))) =
        R
          (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
            0 (j.symm v))
    rw [j.symm_apply_apply]
    exact
      congrArg (fun A : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] V => A (j.symm v))
        (chart_radial_frame_comp x y R he)
  calc
    _ =
        (((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                    0).comp
                j.symm.toContinuousLinearMap).comp
            T).det := by
      rw [hdetT.symm]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := (congrArg ContinuousLinearMap.det hfactor).trans (LinearMap.det_comp _ _)

theorem SpherePoint.chartJacobian_transport {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (ℝ × F) ≃L[ℝ] V)
    (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j B 0 *
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0 :=
  chart_radial_frame_det x y R he
    ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j)

theorem SpherePoint.chartJacobian_transport_sign {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hR : R.toLinearEquiv.toLinearMap.det = 1)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j
            B 0) *
        SignType.sign
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) := by
  have h := chartJacobian_transport x y R he j B
  rw [hR, one_mul] at h
  rw [← sign_mul, h]

def LocalDegree.PointTransition.coordinateMap {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy)) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) :=
  CoverNaturality.overlapCoordinateMap { x }ᶜ
    (LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy)

theorem LocalDegree.PointTransition.coordinateMap_coe {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    (u : Metric.sphere (0 : E) 1) :
    (coordinateMap x y dx dy e he hV u).val =
      ‖(NativeParametrization.centered (D := E) y).symm
              (e
                (NativeParametrization.centered (D := E) x
                  (dx.innerBoundary.radius • (u : E))))‖⁻¹ •
        (NativeParametrization.centered (D := E) y).symm
          (e
            (NativeParametrization.centered (D := E) x
              (dx.innerBoundary.radius • (u : E)))) :=
  rfl

theorem LocalDegree.PointTransition.connecting_naturality {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k
        (LocalDegree.NativeNeighborhood.sphereConnecting x dx k a) =
      LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) :=
  CoverNaturality.normalized_connecting_naturality { x }ᶜ
    (LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy) isClosed_singleton.isOpen_compl
    (LocalDegree.NativeNeighborhood.isOpen_openSet x dx)
    (LocalDegree.NativeNeighborhood.singlePoint_cover x dx) isClosed_singleton.isOpen_compl
    (LocalDegree.NativeNeighborhood.isOpen_openSet y dy)
    (LocalDegree.NativeNeighborhood.singlePoint_cover y dy) k a

theorem LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    LocalDegree.PointTransition.coordinateMap x x (d.restrictRadius r hr hrR) d
        (Homeomorph.refl M) (identity_center x) (mapsTo_restrictRadius x d r hr hrR) =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [LocalDegree.PointTransition.coordinateMap_coe]
  let ds := d.restrictRadius r hr hrR
  change
    ‖(NativeParametrization.centered (D := E) x).symm
              (NativeParametrization.centered (D := E) x
                (ds.innerBoundary.radius • (u : E)))‖⁻¹ •
        (NativeParametrization.centered (D := E) x).symm
          (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      (u : E)
  have hu : ds.innerBoundary.radius • (u : E) ∈ (NativeParametrization.centered x).source :=
    closedBall_subset_source x ds (Metric.ball_subset_closedBall (ds.innerBoundary_mem_ball u))
  have hleft :
    (NativeParametrization.centered (D := E) x).symm
        (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      ds.innerBoundary.radius • (u : E) :=
    (NativeParametrization.centered x).left_inv' hu
  rw [hleft, LocalDegree.norm_radius_smul _ ds.innerBoundary.radius_pos,
    inv_smul_smul₀ ds.innerBoundary.radius_pos.ne']

theorem LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) [T1Space M] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x (d.restrictRadius r hr hrR) k a = sphereConnecting x d k a := by
  have h :=
    LocalDegree.PointTransition.connecting_naturality x x (d.restrictRadius r hr hrR) d
      (Homeomorph.refl M) (identity_center x) (mapsTo_restrictRadius x d r hr hrR) k a
  rw [coordinateMap_restrictRadius, SingularHomology.singularHomologyMap_id,
    LinearMap.id_apply] at h
  change
    sphereConnecting x (d.restrictRadius r hr hrR) k a =
      sphereConnecting x d k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id M) (k + 1) a) at h
  rwa [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] at h

theorem LocalDegree.NativeNeighborhood.sphereConnecting_eq {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f' : M → F'}
    {L' : E ≃L[ℝ] F'} {W' : Set M}
    (d' :
      LocalDegree.NeighborhoodData (f' ∘ NativeParametrization.centered (D := E) x) L'
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W'))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x d k a = sphereConnecting x d' k a := by
  let ρ := Min.min d.radius d'.radius
  have hρ : 0 < ρ := lt_min d.radius_pos d'.radius_pos
  rw [← sphereConnecting_restrictRadius x d ρ hρ (min_le_left _ _) k a, ←
    sphereConnecting_restrictRadius x d' ρ hρ (min_le_right _ _) k a]
  rfl

theorem LocalDegree.PointTransition.coordinateMap_eq_boundary {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy)) :
    coordinateMap x y dx dy e he hV = dx.innerBoundary.normalizedMap :=
  rfl

theorem LocalDegree.PointTransition.coordinateMap_homology {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k := by
  rw [coordinateMap_eq_boundary]
  exact dx.innerBoundary.normalized_homology_compare k

theorem LocalDegree.PointTransition.connecting_derivative_naturality {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₀ : M → F} {L₀ : E ≃L[ℝ] F}
    {W₀ : Set M}
    (d₀ :
      LocalDegree.NeighborhoodData (f₀ ∘ NativeParametrization.centered (D := E) x) L₀
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W₀))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k
        (LocalDegree.NativeNeighborhood.sphereConnecting x d₀ k a) := by
  have h := connecting_naturality x y dx dy e he hV k a
  rw [coordinateMap_homology x y e he dy dx hV k,
    LocalDegree.NativeNeighborhood.sphereConnecting_eq x dx d₀ k a] at h
  exact h.symm

theorem LocalDegree.pointConnecting_diffeomorph {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F}
    {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomeomorph.toHomotopyEquiv.toFun (k + 1)
          a) =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap
          (NativeChartTransition.linear x y e he).toContinuousLinearMap
          (NativeChartTransition.linear x y e he).injective)
        k (NativeNeighborhood.sphereConnecting x dx k a) := by
  let W := e.toHomeomorph ⁻¹' NativeNeighborhood.openSet y dy
  have hW : W ∈ 𝓝 x := by
    apply e.toHomeomorph.continuous.continuousAt
    have hy :=
      (NativeNeighborhood.isOpen_openSet y dy).mem_nhds
        (NativeNeighborhood.center_mem_openSet y dy)
    exact he.symm ▸ hy
  obtain ⟨b⟩ := NativeChartTransition.nonempty_neighborhoodData x y e he W hW
  have hV :
    Set.MapsTo e.toHomeomorph (NativeNeighborhood.openSet x b)
      (NativeNeighborhood.openSet y dy) :=
    NativeNeighborhood.openSet_subset x b
  exact PointTransition.connecting_derivative_naturality x y e.toHomeomorph he dy b hV dx k a

theorem SpherePoint.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] SpherePoint.instLocal1 in
def SpherePoint.pointDiffeomorph (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2))
      (SphereHomology.UnitSphere (n + 2)) ∞ :=
  sphereDiffeomorph (positiveTransport (n + 1) x y)

attribute [local instance] SpherePoint.instLocal1 in
theorem SpherePoint.pointDiffeomorph_apply (n : ℕ)
    (x y : SphereHomology.UnitSphere (n + 2)) : pointDiffeomorph n x y x = y :=
  positiveTransport_moves (n + 1) x y

attribute [local instance] SpherePoint.instLocal1 in
def SpherePoint.pointChartLinear (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  NativeChartTransition.linear x y (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y)

attribute [local instance] SpherePoint.instLocal1 in
theorem SpherePoint.pointClass_sign_compare (n : ℕ) {F G : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (x y : SphereHomology.UnitSphere (n + 2)) {fx : SphereHomology.UnitSphere (n + 2) → F}
    {fy : SphereHomology.UnitSphere (n + 2) → G} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
        ((NativeParametrization.centered y).source ∩
          NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      (SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det : ℤ) •
        LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a := by
  have h :=
    LocalDegree.pointConnecting_diffeomorph x y dx dy (pointDiffeomorph n x y)
      (pointDiffeomorph_apply n x y) (k + 1) a
  have hid :
    SingularMayerVietoris.singularHomologyMap
        (pointDiffeomorph n x y).toHomeomorph.toHomotopyEquiv.toFun (k + 2) a =
      a :=
    positiveTransport_homology (n + 1) x y (k + 2) a
  rw [hid] at h
  apply h.trans
  exact LinearSphereAction.homology_eq_sign_smul n (pointChartLinear n x y) k _

def SpherePoint.punctureHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1) :
    ↥({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    ((stereographic' n x).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target x)).trans (Homeomorph.Set.univ _)))

theorem SpherePoint.puncture_contractible {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
  (punctureHomeomorph (n := n) x).contractibleSpace

def SpherePoint.connectingHomologyEquiv {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : Metric.sphere (0 : V) 1)
    {f : Metric.sphere (0 : V) 1 → F} {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F}
    {W : Set (Metric.sphere (0 : V) 1)}
    (d :
      LocalDegree.NeighborhoodData
        (f ∘ NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x) L
        ((NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x).source ∩
          NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x ⁻¹' W))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : V) 1) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
        (k + 1) := by
  let : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
    puncture_contractible (n := n) x
  exact LocalDegree.NativeNeighborhood.sphereHomologyEquiv x d k

attribute [local instance] SpherePoint.instLocal2 in
def SpherePoint.outwardPointClass (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  (SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) :
      ℤ) •
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1)

attribute [local instance] SpherePoint.instLocal2 in
theorem SpherePoint.outwardPointClass_eq (n : ℕ) {F G H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x y : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {fy : SphereHomology.UnitSphere (n + 2) → G}
    {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
        ((NativeParametrization.centered y).source ∩
          NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ) : outwardPointClass n j B y dy k = outwardPointClass n j B x dx k := by
  have hs :=
    chartJacobian_transport_sign x y (positiveTransport (n + 1) x y)
      (positiveTransport_moves (n + 1) x y) (positiveTransport_det (n + 1) x y) j B
  have hs' :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j
            B 0) *
        SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) :=
    hs
  apply LinearMap.ext
  intro a
  change
    (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y)
              j B 0) :
          ℤ) •
        LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      _
  rw [pointClass_sign_compare n x y dx dy k a, smul_smul, ← SignType.coe_mul, hs']
  rfl

attribute [local instance] SpherePoint.instLocal2 in
theorem SpherePoint.chartSign_mul_self (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2)) :
    (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) *
        (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) =
      1 := by
  have hn :=
    SphereNormalCoordinates.chartJacobian_ne_zero (NativeParametrization.centered x) j
      B (NativeParametrization.zero_mem_centered_source x)
  have hs :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j
            B 0) *
        SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j
            B 0) =
      1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hn)
  simpa only [SignType.coe_mul, SignType.coe_one] using congrArg (fun s : SignType => (s : ℤ)) hs

attribute [local instance] SpherePoint.instLocal2 in
theorem SpherePoint.connecting_eq_sign_outward (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardPointClass n j B x dx k a := by
  change
    _ =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        ((SignType.sign
              (SphereNormalCoordinates.chartJacobian
                (NativeParametrization.centered x) j B 0) :
            ℤ) •
          LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a)
  rw [smul_smul, chartSign_mul_self n j B x, one_smul]

attribute [local instance] SpherePoint.instLocal2 in
def SpherePoint.outwardPointClassEquiv (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) := by
  let C := connectingHomologyEquiv x dx k
  let s : ℤ :=
    SignType.sign
      (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B 0)
  have hs : s * s = 1 := chartSign_mul_self n j B x
  refine LinearEquiv.ofBijective (outwardPointClass n j B x dx k) ⟨?_, ?_⟩
  · intro a b hab
    apply C.injective
    have h := congrArg (fun z => s • z) hab
    change s • (s • C a) = s • (s • C b) at h
    simpa only [smul_smul, hs, one_smul] using h
  · intro b
    refine ⟨C.symm (s • b), ?_⟩
    change s • C (C.symm (s • b)) = b
    rw [C.apply_symm_apply, smul_smul, hs, one_smul]

attribute [local instance] SpherePoint.instLocal3 in
def SpherePoint.outwardClass (n : ℕ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClass n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] SpherePoint.instLocal3 in
def SpherePoint.outwardClassEquiv (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClassEquiv n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] SpherePoint.instLocal3 in
theorem SpherePoint.outwardPointClass_eq_global (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered x) L
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' W))
    (k : ℕ) : outwardPointClass n j B x d k = outwardClass n j B k :=
  outwardPointClass_eq n j B (referencePoint n) x (referenceNeighborhood n (referencePoint n)) d k

attribute [local instance] SpherePoint.instLocal3 in
theorem SpherePoint.pointConnecting_eq_outward (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered x) L
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' W))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardClass n j B k a := by
  rw [connecting_eq_sign_outward n j B x d k a, outwardPointClass_eq_global]

def SpherePoint.sourceCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2) ≃ₗ[ℤ] ℤ :=
  (outwardClassEquiv n j B n).trans (SphereHomology.unitSphereHomologyTopEquiv n)

def SpherePoint.overlapCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (n + 1) ≃ₗ[ℤ] ℤ :=
  (LinearSphereAction.homologyEquiv B (n + 1)).symm.trans
    (SphereHomology.unitSphereHomologyTopEquiv n)

def SpherePoint.targetCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2) ≃ₗ[ℤ] ℤ :=
  (OnePointCover.sphereHomologyEquiv 1 zero_lt_one n).trans (overlapCountMark n B)

theorem SpherePoint.overlapCountMark_linear (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (n + 1)) :
    overlapCountMark n B
        (SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1) a) =
      SphereHomology.unitSphereHomologyTopEquiv n a := by
  rw [← LinearSphereAction.homologyEquiv_apply]
  change
    SphereHomology.unitSphereHomologyTopEquiv n
        ((LinearSphereAction.homologyEquiv B (n + 1)).symm
          (LinearSphereAction.homologyEquiv B (n + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

theorem SpherePoint.countMark_of_connecting (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (u : SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2))
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2))
    (c : ℤ)
    (h :
      OnePointCover.sphereConnecting 1 zero_lt_one (n + 1) u =
        c •
          SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1)
            (outwardClass n j B n a)) :
    targetCountMark n B u = c * sourceCountMark n j B a := by
  have h' := congrArg (overlapCountMark n B) h
  rw [map_zsmul, overlapCountMark_linear] at h'
  exact h'

def ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2 →ₗ[ℤ] ℤ :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2)

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Function.Surjective (d.indexTwoCollapseCoordinate hf hindex) :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf 0)

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    LinearMap.ker (d.indexTwoCollapseCoordinate hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap 2) := by
  rw [← d.upperCollapse_homology_kernel hf 1]
  ext a
  let C := SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)
  change
    C (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a) = 0 ↔
      SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

theorem ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    Function.Injective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    ∃ H :
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 × ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap 2 a) ∧
        ∀ z, d.indexTwoCollapseCoordinate hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    LinearMap.exists_addEquiv_split_of_ker_eq_range (d.lowerRealizationHomologyMap 2)
      (d.indexTwoCollapseCoordinate hf hindex) (d.lowerRealization_two_injective hf hindex)
      (d.indexTwoCoordinate_surjective hf hindex) (d.indexTwoCoordinate_kernel hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

theorem ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)]
    (n : ℕ)
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) :
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap 2 (e v)) ∧
        ∀ v, d.indexTwoCollapseCoordinate hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := d.exists_indexTwoHomology_split hf hindex
  let G :=
    (Fin.tailHeadAddEquiv n).trans
      ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

theorem ManifoldMorse.SurgeryWindows.indexTwoBasis_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (hn : n + 1 < S.count) (hpre : S.HasIndexTwoPrefix (n + 1))
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology
          { x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩) } 2) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩) } 2,
      (∀ v,
          H (Fin.cons 0 v) =
            (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
              (B.homologyEquiv 2 (e v))) ∧
        ∀ v,
          (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
              (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) (H v) =
            v 0 := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
        1) :=
    S.lower_homologyOne_subsingleton_of_indices hf ⟨n + 1, hn⟩ (Nat.succ_pos n)
      (fun i hi hin => by
        have h := hpre i hi (Nat.le_of_lt hin)
        omega)
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  exact
    (S.data (S.point ⟨n + 1, hn⟩)).exists_indexTwoBasis_extension hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) n (e.trans (B.homologyEquiv 2))

def ManifoldMorse.SurgeryWindows.indexTwoBasis {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) →
      (hn : n < S.count) →
        S.HasIndexTwoPrefix n →
          (Fin n → ℤ) ≃ₗ[ℤ]
            SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) } 2
  | 0, hn, _ =>
    by
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨0, hn⟩) } 2) :=
      by
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 2 (by norm_num)
    exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
    Classical.choose
      (S.indexTwoBasis_step hf n hn hpre
        (indexTwoBasis (S := S) hf n (Nat.lt_of_succ_lt hn)
          (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))

def ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 :=
  d.coreBoundaryHomologyMap 2 ((d.indexThreeBoundaryEquiv hindex).symm 1)

theorem ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    d.coreBoundaryHomologyMap 2 a =
      (d.indexThreeBoundaryEquiv hindex a) • d.indexThreeAttachingClass hindex := by
  conv_lhs => rw [d.indexThreeBoundary_scalar hindex a]
  rw [map_zsmul]
  rfl

theorem ManifoldMorse.MorseSurgeryData.coreBoundary_two_range {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.range (d.coreBoundaryHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [d.coreBoundary_two_eq_smul hindex b]
    exact
      Submodule.mem_span_singleton.mpr
        ⟨d.indexThreeBoundaryEquiv hindex b,
          int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (d.indexThreeBoundaryEquiv hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact
      (int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            z (d.indexThreeAttachingClass hindex)).symm.trans
        hz

theorem ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    Function.Surjective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 1) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 1] at ha
  exact ha

theorem ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.ker (d.lowerRealizationHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  rw [← d.morse_exact_at_lower hf 2 (by norm_num), d.coreBoundary_two_range hindex]

def ManifoldMorse.MorseSurgeryData.indexThreePresentation {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) {r c : ℕ}
    (P :
      IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c) :
    IntegerPresentation
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2) r
      (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 2) (d.indexThree_lowerRealization_surjective hf hindex)
    (d.indexThreeAttachingClass hindex) (d.indexThree_lowerRealization_kernel hf hindex)

def ManifoldMorse.SurgeryWindows.middlePresentation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    (c : ℕ) →
      (hc : r + c < S.count) →
        S.HasIndexThreeBlock r c →
          IntegerPresentation
            (SingularMayerVietoris.SingularHomology
              { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) } 2)
            r c
  | 0, hc, _ => IntegerPresentation.ofEquiv (S.indexTwoBasis hf r hc htwo)
  | c + 1, hc, hthree =>
    let P :=
      middlePresentation (S := S) hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation hf.continuous
      (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

def ManifoldMorse.SurgeryWindows.middleMatrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c) :
    Matrix (Fin r) (Fin c) ℤ :=
  (S.middlePresentation hf r htwo c hc hthree).matrix

theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock r n)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
          (∀ p ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
            ∃ α : Fin n → (Hemisphere.Sphere 2) → (S.data q).UpperLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                (MorseCancellation.nativeMiddleBlockPoint S r n hn) α := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := MorseCancellation.nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : MorseCancellation.nativeMorseIndex E f (p j) = 3 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have horder : StrictMono (fun j => f (p j)) := by
    intro i j hij
    apply W.point_strictMono
    change r + i.val + 1 < r + j.val + 1
    omega
  have habove (j : Fin n) : W.upper q < f (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    exact (W.separated q (p j) hqj).trans (W.lower_lt_value (p j))
  have hblock (j : Fin n) (z : ManifoldMorse.criticalPoints E f) (hz : W.upper q < f z)
    (hzj : f z ≤ f (p j)) : z ∈ Set.range p := by
    obtain ⟨k, rfl⟩ := W.point.surjective z
    have hrk : r < k.val := W.point_strictMono.lt_iff_lt.mp ((W.value_lt_upper q).trans hz)
    have hkj : k.val ≤ r + j.val + 1 := W.point_strictMono.le_iff_le.mp hzj
    let i : Fin n := ⟨k.val - (r + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (k.val - (r + 1)) + 1 = k.val
    omega
  exact
    S.exists_middle_block_realization hf hm hdim n (S.data q).upper_regular p hp horder habove
      hblock ε hε

end
