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
import Lib.Geometry.Manifold.Morse.RearrangementAmbient

/-!
# One-point covers and embedded cell attachments

The two-piece open cover of a one-point collapse (`OnePointCover.cover`,
`OnePointCover.punctureHomeomorph`), the Mayer-Vietoris homology of embedded cell attachments
(`EmbeddedCellAttachment.cell_exact_at_old`, `EmbeddedCellAttachment.cellConnectingMap`),
disk one-point collapses, disk shrinking isotopies, positive transports of sphere points
(`SpherePoint.positiveTransport`) and the sign of chart Jacobians in sphere normal coordinates.

Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see
`Lib/reports/integration-4/spheretop-moves.md` for the per-declaration receipt.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

universe u v

noncomputable section

def EmbeddedCellAttachment.oldHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k :=
  SingularHomology.homotopyEquivHomologyEquiv D.oldHomotopyEquiv k

def EmbeddedCellAttachment.attachingHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.old k :=
  SingularMayerVietoris.singularHomologyMap D.attachingSphere k

def EmbeddedCellAttachment.oldHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X k :=
  SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k

theorem EmbeddedCellAttachment.diskPatch_homology_subsingleton {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology D.diskPatch k) := by
  let := D.diskPatch_contractible
  exact SingularHomology.contractible_homology_subsingleton D.diskPatch k hk

theorem EmbeddedCellAttachment.coverRight_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.old k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
        (D.oldHomologyEquiv k a, 0) =
      D.oldHomologyMap k a := by
  rw [SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) k
        (SingularMayerVietoris.singularHomologyMap D.oldInclusion k a) =
      SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

theorem EmbeddedCellAttachment.coverRight_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0)
    (b :
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
        SingularMayerVietoris.SingularHomology D.diskPatch k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k b =
      D.oldHomologyMap k ((D.oldHomologyEquiv k).symm b.1) := by
  let := D.diskPatch_homology_subsingleton k hk
  have hb : (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) = b :=
    Prod.ext ((D.oldHomologyEquiv k).apply_symm_apply b.1) (Subsingleton.elim _ _)
  calc
    _ =
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) :=
      congrArg (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) hb.symm
    _ = _ := D.coverRight_old k _

theorem EmbeddedCellAttachment.range_coverRight {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) =
      LinearMap.range (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k).symm b.1, (D.coverRight_formula k hk b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k b, 0), D.coverRight_old k b⟩

theorem DiskShrinking.exists_embedded_disk_isotopy_of_path {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0)) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, hP, hP0, -⟩ :=
    MorseCancellation.exists_isotopic_pointMoving_of_path (J := 𝓘(ℝ, E)) isOpen_univ γ
      (fun _ => Set.mem_univ _)
  have hPf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (P ∘ f) := P.contMDiff.comp hf
  have hPfi : Set.InjOn (P ∘ f) (Metric.closedBall (0 : D) 1) := by
    intro x hx y hy hh
    exact hfi hx hy (P.injective hh)
  have hPfd :
    ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (P ∘ f) x) := by
    intro x hx
    rw [mfderiv_comp x (P.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
    have hi : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) P (f x) : E →L[ℝ] E) :=
      PartialChart.bijective_mfderiv P.toPartialDiffeomorph (Set.mem_univ _)
    exact hi.1.comp (hfd x hx)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_embedded_disk_isotopy_of_same_center hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0
  exact ⟨P.trans Q, hP.trans hQ, hformula⟩

theorem DiskShrinking.exists_embedded_disk_isotopy {D E M : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x :=
  exists_embedded_disk_isotopy_of_path hf hg hfi hgi hfd hgd n hn hdim hE
    (Joined.somePath (PathConnectedSpace.joined (f 0) (g 0)))

def DiskOnePointCollapse.boundary {N : Type*} [NormedAddCommGroup N] :
    Set (MorseHandle.UnitDisk N) :=
  {z | ‖(z : N)‖ = 1}

theorem DiskOnePointCollapse.boundary_closed {N : Type*} [NormedAddCommGroup N] :
    IsClosed (boundary (N := N)) :=
  isClosed_eq continuous_subtype_val.norm continuous_const

theorem DiskOnePointCollapse.not_mem_boundary_iff {N : Type*} [NormedAddCommGroup N]
    (z : MorseHandle.UnitDisk N) : z ∉ boundary ↔ ‖(z : N)‖ < 1 := by
  change ‖(z : N)‖ ≠ 1 ↔ ‖(z : N)‖ < 1
  constructor
  · exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
  · exact ne_of_lt

def DiskOnePointCollapse.interiorHomeomorph {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : ↥(boundary (N := N))ᶜ ≃ₜ N :=
  (Homeomorph.setCongr (by ext z; exact not_mem_boundary_iff z)).trans
    (DiskAnnulus.openDiskHomeomorph.trans Homeomorph.unitBall.symm)

def DiskOnePointCollapse.compress {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (x : N) : MorseHandle.UnitDisk N :=
  ⟨Homeomorph.unitBall x, Metric.ball_subset_closedBall (Homeomorph.unitBall x).property⟩

theorem DiskOnePointCollapse.norm_compress_lt {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : ‖(compress x : N)‖ < 1 :=
  mem_ball_zero_iff.mp (Homeomorph.unitBall x).property

theorem DiskOnePointCollapse.compress_zero {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : (compress (0 : N) : N) = 0 :=
  Homeomorph.coe_unitBall_apply_zero

theorem EmbeddedCellAttachment.collapse_piece_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Set.range (Subtype.val : D.old → X) ∪ Set.range D.cell = Set.univ := by
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using D.cover

def OnePointCover.oldPatch {N : Type*} [NormedAddCommGroup N] : Set (OnePoint N) :=
  {((0 : N) : OnePoint N)}ᶜ

def OnePointCover.finitePatch {N : Type*} : Set (OnePoint N) :=
  { OnePoint.infty }ᶜ

theorem OnePointCover.cover {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∪ finitePatch = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = ((0 : N) : OnePoint N)
  · right
    subst x
    exact OnePoint.coe_ne_infty 0
  · exact Or.inl hx

theorem OnePointCover.oldPatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (oldPatch (N := N)) :=
  isClosed_singleton.isOpen_compl

theorem OnePointCover.finitePatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (finitePatch (N := N)) :=
  isClosed_singleton.isOpen_compl

def OnePointCover.overlapRadius : ℝ :=
  (Real.sqrt (1 - (3 / 4 : ℝ) ^ 2))⁻¹ * (3 / 4)

theorem OnePointCover.overlapRadius_pos : 0 < overlapRadius := by
  have h : 0 < 1 - (3 / 4 : ℝ) ^ 2 := by norm_num
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr h)) (by norm_num)

theorem SphereNormalCoordinates.normalDerivative_smul_isInvertible {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N)
    (hA : A.IsInvertible) (c : ℝ) (hc : c ≠ 0) : (c • A).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • A.inverse)
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.self_apply_inverse, hc]
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.inverse_apply_self, hc]

def CoverLocalContributions.localMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : ∀ i, Set.MapsTo f (V i) V') (i : ι) : C(↥(U ∩ V i), ↥(U' ∩ V')) :=
  CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

theorem CoverLocalContributions.connecting_sum {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) V')
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' k
        (SingularMayerVietoris.singularHomologyMap f (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (localMap U V U' V' f hfU hfV i) k
          (componentConnecting U V hU hV hd hc k a i) := by
  rw [←
    CoverNaturality.connecting_naturality_apply U (⋃ i, V i) U' V' f hfU
      (map_union V V' f hfV) hU (isOpen_iUnion hV) hc hU' hV' hc' k a]
  rw [CoverOverlapHomology.homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem SpherePoint.hyperplaneReflection_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (u : V) (hu : u ≠ 0) :
    ((ℝ ∙ u)ᗮ.reflection).toLinearMap.det = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu,
    pow_one]

theorem SpherePoint.positive_transport_of_normal {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (v w : Metric.sphere (0 : V) 1) (u : V)
    (hu : u ≠ 0) (huw : Inner.inner ℝ u w.val = 0) (hvw : v ≠ w) :
    ∃ R : V ≃ₗᵢ[ℝ] V, R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  have hvw' : (v : V) - (w : V) ≠ 0 := by
    intro h
    exact hvw (Subtype.ext (sub_eq_zero.mp h))
  let R₁ := (ℝ ∙ ((v : V) - (w : V)))ᗮ.reflection
  let R₂ := (ℝ ∙ u)ᗮ.reflection
  have h₁ : R₁ v.val = w.val :=
    Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp v.property).trans
        (mem_sphere_zero_iff_norm.mp w.property).symm)
  have h₂ : R₂ w.val = w.val :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huw)
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · change R₂ (R₁ v.val) = w.val
    rw [h₁, h₂]
  · change (R₂.toLinearMap.comp R₁.toLinearMap).det = 1
    rw [LinearMap.det_comp, hyperplaneReflection_det u hu,
      hyperplaneReflection_det ((v : V) - (w : V)) hvw']
    norm_num

theorem SpherePoint.exists_positive_transport (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)),
      R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  by_cases hvw : v = w
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact congrArg Subtype.val hvw
    · exact LinearMap.det_id
  · let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) := ⟨by simp⟩
    let b :=
      OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1) (ne_zero_of_mem_unit_sphere w)
    let u : EuclideanSpace ℝ (Fin (n + 2)) :=
      (b (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)))
    have hun : ‖u‖ = 1 := b.norm_eq_one 0
    have hu : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have huw : Inner.inner ℝ u w.val = 0 := by
      have h := (b (0 : Fin (n + 1))).property
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp h
    exact positive_transport_of_normal v w u hu huw hvw

def SpherePoint.positiveTransport (n : ℕ) (v w : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (exists_positive_transport n v w)

theorem SpherePoint.positiveTransport_apply (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : positiveTransport n v w v.val = w.val :=
  (Classical.choose_spec (exists_positive_transport n v w)).1

theorem SpherePoint.positiveTransport_det (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : (positiveTransport n v w).toLinearMap.det = 1 :=
  (Classical.choose_spec (exists_positive_transport n v w)).2

def SpherePoint.sphereHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 :=
  R.toContinuousLinearEquiv.toHomeomorph.subtype
    (fun x => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔ ‖R x‖ = 1
      rw [R.norm_map])

theorem SpherePoint.sphereHomeomorph_eq_normalized {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : V ≃ₗᵢ[ℝ] V) :
    (sphereHomeomorph R).toHomotopyEquiv.toFun =
      LinearSphereAction.sphereMap R.toContinuousLinearEquiv.toContinuousLinearMap
        R.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change R x.val = ‖R x.val‖⁻¹ • R x.val
  rw [R.norm_map, mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

theorem SpherePoint.contMDiff_sphereHomeomorph {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereHomeomorph R) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ (fun x : Metric.sphere (0 : V) 1 => R x.val) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (m := ∞))
  exact h.codRestrict_sphere (n := n) (fun x => (sphereHomeomorph R x).property)

def SpherePoint.sphereDiffeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : V) 1) (Metric.sphere (0 : V) 1) ∞
    where
  toEquiv := (sphereHomeomorph R).toEquiv
  contMDiff_toFun := contMDiff_sphereHomeomorph R
  contMDiff_invFun := contMDiff_sphereHomeomorph R.symm

theorem SpherePoint.sphereHomeomorph_homology_of_det_pos (n : ℕ)
    (R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (hR : 0 < R.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereHomeomorph R).toHomotopyEquiv.toFun k a =
      a := by
  rw [sphereHomeomorph_eq_normalized]
  exact LinearSphereAction.homology_of_det_pos n R.toContinuousLinearEquiv hR k a

theorem SpherePoint.positiveTransport_moves (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    sphereHomeomorph (positiveTransport n v w) v = w :=
  Subtype.ext (positiveTransport_apply n v w)

theorem SpherePoint.positiveTransport_homology (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap
        (sphereHomeomorph (positiveTransport n v w)).toHomotopyEquiv.toFun k a =
      a := by
  apply sphereHomeomorph_homology_of_det_pos n _ _ k a
  rw [positiveTransport_det]
  norm_num

theorem SpherePoint.ambient_chart_hasFDerivAt {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source) :
    HasFDerivAt (fun u => (c u : V)) (fderiv ℝ (fun u => (c u : V)) z) z := by
  have hc : ContDiffOn ℝ ∞ (fun u => (c u : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact ((hc.contDiffAt (c.open_source.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt

theorem SpherePoint.chart_transition_eventually_eq {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fun u : EuclideanSpace ℝ (Fin m) =>
        (NativeParametrization.centered y
            (NativeChartTransition.chart x y (sphereDiffeomorph (n := m) R) u) :
          V)) =ᶠ[𝓝 0]
      (fun u : EuclideanSpace ℝ (Fin m) => R (NativeParametrization.centered x u : V)) := by
  let e := sphereDiffeomorph (n := m) R
  let T := NativeChartTransition.chart x y e
  have hS := T.open_source.mem_nhds (NativeChartTransition.zero_mem_source x y e he)
  filter_upwards [hS] with u hu
  have ht :
    e (NativeParametrization.centered x u) ∈
      (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin m)) y).target :=
    hu.2
  have h := (NativeParametrization.centered y).right_inv' ht
  exact congrArg Subtype.val h

theorem SpherePoint.chart_transition_ambient_derivative {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0).comp
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toContinuousLinearMap =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun u => (NativeParametrization.centered x u : V)) 0) := by
  let e := sphereDiffeomorph (n := m) R
  let T := NativeChartTransition.chart x y e
  have hx :=
    ambient_chart_hasFDerivAt (m := m) (NativeParametrization.centered x)
      (NativeParametrization.zero_mem_centered_source x)
  have hy :=
    ambient_chart_hasFDerivAt (m := m) (NativeParametrization.centered y)
      (NativeParametrization.zero_mem_centered_source y)
  have hyT :
    HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin m) => (NativeParametrization.centered y u : V))
      (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0) (T 0) :=
    (NativeChartTransition.chart_zero x y e he).symm ▸ hy
  have hchain := hyT.comp 0 (NativeChartTransition.hasFDerivAt_chart x y e he)
  have hR := R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0 hx
  exact hchain.unique (hR.congr_of_eventuallyEq (chart_transition_eventually_eq x y R he))

theorem SphereNormalCoordinates.sign_factor_mo1973_5719 {a b c : ℝ} (hb : b ≠ 0)
    (h : a * b = c) : SignType.sign c * SignType.sign b = SignType.sign a := by
  have hsq : SignType.sign b * SignType.sign b = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hb)
  rw [← h, sign_mul, mul_assoc, hsq, mul_one]

theorem SpherePoint.instLocal2 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

theorem SpherePoint.instLocal3 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] SpherePoint.instLocal3 in
def SpherePoint.referencePoint (n : ℕ) : SphereHomology.UnitSphere (n + 2) :=
  Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)

attribute [local instance] SpherePoint.instLocal3 in
def SpherePoint.referenceNeighborhood (n : ℕ) (x : SphereHomology.UnitSphere (n + 2)) :
    LocalDegree.NeighborhoodData
      (((NativeParametrization.centered (D := EuclideanSpace ℝ (Fin (n + 2))) x).symm ∘
          Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) ∘
        NativeParametrization.centered x)
      (NativeChartTransition.linear x x
        (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl)
      ((NativeParametrization.centered x).source ∩
        NativeParametrization.centered x ⁻¹'
          (Set.univ : Set (SphereHomology.UnitSphere (n + 2)))) :=
  Classical.choice
    (NativeChartTransition.nonempty_neighborhoodData x x
      (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl Set.univ (by simp))

end
