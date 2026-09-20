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
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.Geometry.Manifold.Morse.SurgeryHomology

/-!
# Ordered Morse systems and cancellation steps

Belt tubes and parameter balls (`MorseCancellation.nativeBeltTubeSource`,
`MorseCancellation.beltBallCoordinates`), adapted windows with prescribed flow, value exchange
and flow-preserving consecutive pairs, cancellation of unique zero-one connections, the
homology of zero-cells, reduction of multiple minima, index-ordered and outer-index-minimal
excellent Morse systems (`MorseCancellation.exists_minimal_excellent_morse_system`,
`MorseCancellation.exists_outer_index_minimal_ordered_morse_system`) and middle index blocks.

Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see
`Lib/reports/integration-4/spheretop-moves.md` for the per-declaration receipt.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

theorem IntLinearAutomorphism.apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (k : ℤ) : e k = e 1 * k := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul k 1

theorem IntLinearAutomorphism.apply_one_eq_one_or_neg_one (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := e.symm 1)
  rw [← apply_eq_mul, e.apply_symm_apply]

theorem MorseCancellation.two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : (Hemisphere.Sphere 2) ≃ₜ Y) (g : C((Hemisphere.Sphere 2), Y))
    (hg : Function.Bijective (SingularMayerVietoris.singularHomologyMap g 2)) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap g 2 =
          k •
            SingularMayerVietoris.singularHomologyMap (e : C((Hemisphere.Sphere 2), Y)) 2 :=
  by
  let H := SphereHomology.unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap g 2) hg
  let J := SingularHomology.homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

def MorseCancellation.nativeBeltTubeSource {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        PuncturedBall.Space d.chart.NegativeCoordinates 1,
      d.chart.beltSource d.radius d.radius_pos)
    where
  toFun
    z :=
    ⟨(z.1, z.2.val),
      d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
        ⟨Set.mem_univ _, by
          rw [mem_closedBall_zero_iff]
          exact z.2.property.2.le.trans (by norm_num)⟩⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def MorseCancellation.nativeBeltTubeInComplement {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        PuncturedBall.Space d.chart.NegativeCoordinates 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel))
    where
  toFun
    z := by
    let y := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (nativeBeltTubeSource d z)
    refine ⟨y.val, ?_⟩
    intro hy
    have hz := (d.beltNormal_eq_zero_iff y.property).mpr hy
    have heq : d.beltNormal y.val = d.radius • z.2.val :=
      d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (nativeBeltTubeSource d z)
    rw [heq] at hz
    exact (smul_ne_zero d.radius_pos.ne' z.2.property.1) hz
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp
            (nativeBeltTubeSource d).continuous)).subtype_mk
      _

def MorseCancellation.nativeBeltTubeMeridian {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    ((ContinuousMap.const _ v).prodMk (PuncturedBall.fromSphere 1 r hr hr1))

def MorseCancellation.parameterBallBoundary {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : A) 1, Metric.closedBall (0 : A) r)
    where
  toFun
    u := ⟨r • u.val, by rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul r hr u]⟩
  continuous_toFun := by
    have h : Continuous (fun u : Metric.sphere (0 : A) 1 => r • u.val) :=
      continuous_const.smul continuous_subtype_val
    exact h.subtype_mk _

def MorseCancellation.parameterBallCenter {A : Type} [NormedAddCommGroup A] (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : A) r :=
  ⟨0, by simpa using hr.le⟩

def MorseCancellation.parameterBallContraction {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (r : ℝ) (hr : 0 < r) :
    (parameterBallBoundary (A := A) r hr).Homotopy
      (ContinuousMap.const _ (parameterBallCenter r hr))
    where
  toFun
    z :=
    ⟨(1 - (z.1 : ℝ)) • (r • z.2.val),
      by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr z.1.property.2),
        LocalDegree.norm_radius_smul r hr z.2]
      exact mul_le_of_le_one_left hr.le (by linarith [z.1.property.1])⟩
  continuous_toFun := by
    have h :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : A) 1 => (1 - (z.1 : ℝ)) • (r • z.2.val)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left u := by apply Subtype.ext; simp [parameterBallBoundary]
  map_one_left u := by apply Subtype.ext; simp [parameterBallCenter]

theorem MorseCancellation.parameterBall_boundary_nullhomotopic {A : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {Y : Type} [TopologicalSpace Y] (r : ℝ) (hr : 0 < r)
    (g : C(Metric.closedBall (0 : A) r, Y)) :
    (g.comp (parameterBallBoundary r hr)).Homotopic
      (ContinuousMap.const _ (g (parameterBallCenter r hr))) := by
  have h := (ContinuousMap.Homotopic.refl g).comp ⟨parameterBallContraction r hr⟩
  exact h

theorem MorseCancellation.normalized_pos_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (hr : 0 < r) (x : F) : ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

def MorseCancellation.beltBallCoordinates {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    (d : ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius)) :
    C(Metric.closedBall (0 : A) ε,
      Metric.sphere (0 : d.chart.PositiveCoordinates) 1 × d.chart.NegativeCoordinates) :=
  ⟨fun z => ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm (F z)).val,
    continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm.continuous.comp
        F.continuous)⟩

theorem MorseCancellation.beltBallCoordinates_normal {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (z : Metric.closedBall (0 : A) ε) :
    (beltBallCoordinates d ε F z).2 = d.radius⁻¹ • d.beltNormal (F z).val :=
  rfl

def MorseCancellation.beltBallBoundaryNormal {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, PuncturedBall.Space d.chart.NegativeCoordinates 1) :=
  ⟨fun u => ⟨(beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2, hne u, hsmall _⟩,
    ((beltBallCoordinates d ε F).continuous.snd.comp
          (parameterBallBoundary ε hε).continuous).subtype_mk
      _⟩

def MorseCancellation.beltBallBoundaryInComplement {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    (((ContinuousMap.fst.comp (beltBallCoordinates d ε F)).comp
          (parameterBallBoundary ε hε)).prodMk
      (beltBallBoundaryNormal d ε hε F hsmall hne))

theorem MorseCancellation.beltBallBoundaryInComplement_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne u).val =
      (F (parameterBallBoundary ε hε u)).val := by
  let y := F (parameterBallBoundary ε hε u)
  let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
  change
    (e
          (nativeBeltTubeSource d
            ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)))).val =
      y.val
  have hs :
    nativeBeltTubeSource d ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)) =
      e.symm y := by
    apply Subtype.ext
    rfl
  rw [hs, e.apply_symm_apply]

theorem MorseCancellation.beltBallBoundary_normalized_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (PuncturedBall.toSphere 1 (beltBallBoundaryNormal d ε hε F hsmall hne u)).val =
      ‖d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        d.beltNormal (F (parameterBallBoundary ε hε u)).val := by
  change
    ‖d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        (d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val) =
      _
  exact normalized_pos_smul d.radius⁻¹ (inv_pos.mpr d.radius_pos) _

theorem MorseCancellation.exists_small_native_belt_neighborhood {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (G : A → d.UpperLevel) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) {t : Set A}
    (ht : t ∈ 𝓝 (0 : A)) (hc : ContinuousOn G t) (hcenter : G 0 = d.surgery.beltSphere v) :
    ∃ s : Set A,
      s ∈ 𝓝 (0 : A) ∧
        s ⊆ t ∧
          ContinuousOn G s ∧
            (∀ z ∈ s, G z ∈ d.beltNormalDomain) ∧
              (∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1) := by
  have hG : ContinuousAt G 0 := hc.continuousAt ht
  have hdomain : G 0 ∈ d.beltNormalDomain := hcenter ▸ d.belt_mem_normalDomain v
  have hsplit : ContinuousAt d.chart.splitChart (G 0).val :=
    d.chart.splitChart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.splitChart.open_source.mem_nhds hdomain)
  have hGM : ContinuousAt (fun z : A => (G z).val) 0 :=
    (continuous_subtype_val : Continuous (Subtype.val : d.UpperLevel → M)).continuousAt.comp hG
  have hsplitG : ContinuousAt (fun z : A => d.chart.splitChart (G z).val) 0 :=
    ContinuousAt.comp (f := fun z : A => (G z).val) hsplit hGM
  have hnormal : ContinuousAt (fun z => d.beltNormal (G z)) 0 := by
    change ContinuousAt (fun z : A => (d.chart.splitChart (G z).val).1) 0
    exact hsplitG.fst
  have hsize : ContinuousAt (fun z => ‖d.radius⁻¹ • d.beltNormal (G z)‖) 0 :=
    (hnormal.const_smul d.radius⁻¹).norm
  have hzero : ‖d.radius⁻¹ • d.beltNormal (G 0)‖ < 1 := by
    rw [hcenter, d.beltNormal_belt, smul_zero, norm_zero]
    norm_num
  have h₀ : G ⁻¹' d.beltNormalDomain ∈ 𝓝 (0 : A) :=
    hG.preimage_mem_nhds (d.isOpen_beltNormalDomain.mem_nhds hdomain)
  have h₁ : {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1} ∈ 𝓝 (0 : A) :=
    hsize.preimage_mem_nhds (Iio_mem_nhds hzero)
  let s := t ∩ (G ⁻¹' d.beltNormalDomain ∩ {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1})
  refine
    ⟨s, Filter.inter_mem ht (Filter.inter_mem h₀ h₁), Set.inter_subset_left,
      hc.mono Set.inter_subset_left, ?_, ?_⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_morseSurgeryData_of_field_germ_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ManifoldMorse.MorseSurgeryData E f p,
      d.radius < ε ∧
        d.chart = c ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f,
              f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
            ∀ z,
              z ∈
                  Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
                    Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) →
                ∀ᶠ x in 𝓝 (d.chart.splitChart.symm z), V x = d.chart.descentField x := by
  obtain ⟨ρ, hρ, hρε, W, hW, -, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hmodel :
    ∀ z,
      z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) →
        ∀ᶠ x in 𝓝 (c.splitChart.symm z), V x = c.descentField x := by
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with x hx
    exact heqW x hx
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    exact hmodel _ (MorseHandle.modelMap_mem_product hρ z)
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hF ρ hρ hblock
      hagreement hband
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ ManifoldMorse.criticalPoints E f := by
    intro hcrit
    exact hne (hx.symm.trans (congrArg f (hband x hcrit (hx ▸ hb))))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hh :=
      FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hF hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hh
  have hlevel :=
    FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F
      (FlowConstruction.antitone_flow_height hf F hF hzero hdesc) hbottom
  have horbits :=
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hF ρ hρ hblock (e := e) (horbit :=
      horbit) hmodel
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := hfront
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e hfront
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e hfront hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, rfl, hband, hmodel⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : ManifoldMorse.criticalPoints E f,
        ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x) :
    ∃ S : AdaptedWindows E f, S.field = V ∧ S.flow = F ∧ ∀ p, (S.data p).chart = c p := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (hr p)
  choose d hd hchart hisolated hgerm using hex
  have hseparated (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart⟩

def MorseCancellation.standardCircleParametrization :
    Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1) Circle ∞ := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  exact SphereCoordinates.standardParametrization ℂ 1

theorem MorseCancellation.contMDiff_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) :
    ContMDiff (𝓡 1) J ∞ (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.contMDiff

theorem MorseCancellation.injective_comp_standardCircle {N : Type*} [TopologicalSpace N]
    {γ : Circle → N} (hγ : Function.Injective γ) :
    Function.Injective (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.injective

theorem MorseCancellation.injective_derivative_comp_standardCircle {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hi : ∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) (z : Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z) := by
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  exact
    (hi _).comp
      (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).injective

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : ManifoldMorse.criticalPoints E f,
        ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ S : AdaptedWindows E f,
      S.field = V ∧ S.flow = F ∧ (∀ p, (S.data p).chart = c p) ∧ ∀ p, (S.data p).radius < ε p := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (lt_min (hr p) (hε p))
  choose d hd hchart hisolated hgerm using hex
  have hdr (p : ManifoldMorse.criticalPoints E f) : (d p).radius < r p :=
    (hd p).trans_le (min_le_left _ _)
  have hde (p : ManifoldMorse.criticalPoints E f) : (d p).radius < ε p :=
    (hd p).trans_le (min_le_right _ _)
  have hseparated (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart, hde⟩

def MorseCancellation.nativeIndexThreeAttachingSphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) : C((Hemisphere.Sphere 2), (S.data p).LowerLevel) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  exact
    (S.data p).surgery.attachingSphere.comp
      ((SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
            2).toHomeomorph :
        C((Hemisphere.Sphere 2),
          Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1))

def MorseCancellation.IsNativeMiddleBasinFamily {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (α : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = a }) : Prop :=
  let _ := RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) ∧
    (∀ j, Topology.IsClosedEmbedding (α j)) ∧
      (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) ∧
        Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) ∧
          ∀ j y,
            y ∈ Set.range (α j) ↔
              Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 (p j).val)

theorem MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let d : ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := PartialChart.restrictSource c.chart hU
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl⟩

theorem MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨d, hd⟩ :=
    exists_signed_morse_chart_of_germ_preserving_field (shiftedSignedMorseChart c k) hgerm
  exact ⟨d, hd⟩

theorem MorseCancellation.injOn_of_exchanged_values {X Y : Type*} {f g : X → Y} {S : Set X} {p q : X}
    (hinj : Set.InjOn f S) (hp : p ∈ S) (hq : q ∈ S) (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ S, x ≠ p → x ≠ q → g x = f x) : Set.InjOn g S := by
  classical
  have hform (x : X) (hx : x ∈ S) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hothers x hx hxp hxq
  have hmaps : Set.MapsTo (Equiv.swap p q) S S := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hq
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hp
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hx
  intro x hx y hy hxy
  apply (Equiv.swap p q).injective
  apply hinj (hmaps hx) (hmaps hy)
  rw [← hform x hx, ← hform y hy]
  exact hxy

theorem MorseCancellation.nativeMorseCount_eq_of_preserved_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x)
    (k : ℕ) : nativeMorseCount E g k = nativeMorseCount E f k := by
  have heq :
    {x : M | x ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g x = k} =
      {x : M | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k} := by
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hcrit]
    by_cases hx : x ∈ ManifoldMorse.criticalPoints E f
    · rw [hindex x hx]
    · simp only [hx, false_and]
  exact congrArg Set.ncard heq

theorem MorseCancellation.adapted_surgery_system_after_value_exchange {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : AdaptedWindows E f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : ManifoldMorse.IsMorse E g) (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ ManifoldMorse.criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) :
    Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hinj : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values S.distinct hp hq hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  exact ⟨hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

theorem MorseCancellation.exists_flow_preserving_value_exchange {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ x ∈ ManifoldMorse.criticalPoints E f,
                      x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
                    (∀ x,
                        x ∉ ManifoldMorse.criticalPoints E g →
                          mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                      (∀ x ∈ ManifoldMorse.criticalPoints E g,
                          ∃ c : ManifoldMorse.SignedMorseChart (E := E) g x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
                          ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  obtain ⟨S⟩ := ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels p p.property
  obtain ⟨cq, hcq⟩ := hmodels q q.property
  have hp : f p ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨S.lower_lt_value p, hpq.trans (S.value_lt_upper q)⟩
  have hq : f q ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨(S.lower_lt_value p).trans hpq, S.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, -, hpgerm, hqgerm, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV F hF hzero
      hdesc hinj cp cq hcp hcq hp hq hpq hq hp (surgery_pair_band_isolation S p q hconsecutive)
      hnoconnection
  have hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values hinj p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels :
    ∀ x ∈ ManifoldMorse.criticalPoints E g,
      ∃ c : ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    rw [hcrit] at hx
    by_cases hxp : x = p.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cp hpgerm
      exact ⟨c, hc ▸ hcp⟩
    by_cases hxq : x = q.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cq hqgerm
      exact ⟨c, hc ▸ hcq⟩
    obtain ⟨c, hc⟩ := hmodels x hx
    obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field c (hothers x hx hxp hxq)
    exact ⟨d, hd ▸ hc⟩
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, (fun x hx => hdescent x (hcrit ▸ hx)),
      hnewmodels, hindices, nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

theorem MorseCancellation.exists_flow_preserving_consecutive_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : ManifoldMorse.IsMorse E f₀)
    (hinj₀ : Set.InjOn f₀ (ManifoldMorse.criticalPoints E f₀))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f₀) (hrp : f₀ r < f₀ p) (hpq : f₀ p < f₀ q)
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val))) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ z : ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
                      (∀ x,
                          x ∉ ManifoldMorse.criticalPoints E f →
                            mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
                              ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                          ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x := by
  classical
  let _ := (ManifoldMorse.finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ x,
                        x ∉ ManifoldMorse.criticalPoints E f →
                          mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                      (∀ x ∈ ManifoldMorse.criticalPoints E f,
                          ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
                          IndexDisorder.beforeValueRank
                              (fun x : ManifoldMorse.criticalPoints E f₀ => f x) q =
                            n
  have hex : ∃ n, P n :=
    ⟨IndexDisorder.beforeValueRank
        (fun x : ManifoldMorse.criticalPoints E f₀ => f₀ x) q,
      f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hdesc, hmodels, hindices, hrank⟩ :=
    Nat.find_spec hex
  have hconsecutive : ∀ z : ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ :=
      IndexDisorder.exists_consecutive_below_of_intermediate (h :=
        fun x : ManifoldMorse.criticalPoints E f₀ => f x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg f h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg f h)
    have hzr : z.val ≠ r.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (not_lt_of_gt hpz) (by simpa only [h] using hrp')
    let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, by rw [hcrit]; exact z.property⟩
    let qf : ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
    have hbeforef : ∀ s : ManifoldMorse.criticalPoints E f, ¬(f zf < f s ∧ f s < f qf) := by
      intro s hs
      exact hbefore ⟨s.val, by rw [← hcrit]; exact s.property⟩ hs
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg, hindicesg, -⟩ :=
      exists_flow_preserving_value_exchange hf hm hinj hV F hF (fun x hx => hzero x (hcrit ▸ hx))
        hdesc hmodels zf qf hzq hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact p.property
    have hrcrit : r.val ∈ ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      have hlt : f r < f q := hrp'.trans hfpq
      exact (ne_of_lt hlt) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hdecrease :
      IndexDisorder.beforeValueRank
          (fun x : ManifoldMorse.criticalPoints E f₀ => g x) q <
        IndexDisorder.beforeValueRank
          (fun x : ManifoldMorse.criticalPoints E f₀ => f x) q := by
      apply
        IndexDisorder.beforeValueRank_exchange_lt (h :=
          fun x : ManifoldMorse.criticalPoints E f₀ => f x) (g :=
          fun x : ManifoldMorse.criticalPoints E f₀ => g x) (p := z) (q := q)
          (fun x y h =>
            Subtype.ext
              (hinj (by rw [hcrit]; exact x.property) (by rw [hcrit]; exact y.property) h))
          hzq hbefore hgz hgq
      intro x hxz hxq
      exact
        (hothers x (by rw [hcrit]; exact x.property) (fun h => hxz (Subtype.ext h))
            (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal :=
      Nat.find_min' hex
        ⟨g, hg, hmg, hcritg.trans hcrit, hinjg, hgp.trans hfp, hgr.trans hfr,
          (by rw [hgp, hgq]; exact hpz), hdescg, hmodelsg, hidxg₀, rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hconsecutive, hdesc, hmodels, hindices⟩

theorem MorseCancellation.isOpen_forward_basin_of_native_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodel : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)} := by
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hindex
  obtain ⟨r, hr, -, hbasin⟩ :=
    exists_descending_morse_basin_block c hf (hV.of_le (by simp)) F hF hzero hdesc hmodel
  have hnear : ∀ᶠ y in 𝓝 p, Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff F t y p).mp hy

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_unique_zero_one_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p q z : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hindexp : nativeMorseIndex E f p = 0)
    (hindexq : nativeMorseIndex E f q = 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {l u : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc l u → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f := by
  have hp0 : Module.finrank ℝ cp.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart cp).symm.trans hindexp
  have hq1 : Module.finrank ℝ cq.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart cq).symm.trans hindexq
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by
    have h := cq.finrank_negative_add_positive
    omega
  have hindex :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    have h :
      Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
      omega
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using h
  have hbasin : ∀ᶠ x in 𝓝 z, Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
    (isOpen_forward_basin_of_native_index_zero cp hf hV F hF hzero hdesc heqp hp0).mem_nhds hp
  have htrans :
    NativeTransversality.At 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) (fun x : M => x) z z :=
    by
    intro _ w
    refine ⟨(0, w), ?_⟩
    change
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) z 0 +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : M => x) z w =
        w
    rw [map_zero, zero_add]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w = w
    rw [mfderiv_id]
    rfl
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V hV hzero hdesc F
      hF hinj hpc hqc hpq hl hu hpair hp hq hunique heqp heqq (S := fun _ : M => z) (T :=
      fun x : M => x) mdifferentiableAt_const mdifferentiableAt_id rfl rfl
      (Filter.Eventually.of_forall (fun _ => hq)) hbasin htrans

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.componentChainWeight {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains X 0 →ₗ[ℤ] ℤ :=
  SingularChains.chainLift X 0 (fun σ => if Joined x (σ (stdSimplex.vertex 0)) then 1 else 0)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.componentChainWeight_point {X : Type} [TopologicalSpace X] (x y : X) :
    componentChainWeight x (SingularChains.pointChain y) = if Joined x y then 1 else 0 := by
  exact SingularChains.chainLift_simplex X 0 _ _

theorem MorseCancellation.componentChainWeight_boundary {X : Type} [TopologicalSpace X] (x : X)
    (b : SingularChains.Chains X 1) : componentChainWeight x (SingularChains.boundaryOne X b) = 0 :=
  by
  classical
  have heq : (componentChainWeight x).comp (SingularChains.boundaryOne X) = 0 := by
    apply SingularChains.chainMap_ext X 1
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, SingularChains.boundaryOne_simplex,
      map_sub, componentChainWeight, SingularChains.chainLift_simplex, ContinuousMap.comp_apply,
      SingularChains.simplexFace_zero_zero, SingularChains.simplexFace_zero_one]
    have hp : Joined (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) :=
      ⟨SingularChains.simplexPath σ⟩
    have hi : Joined x (σ (stdSimplex.vertex 1)) ↔ Joined x (σ (stdSimplex.vertex 0)) :=
      ⟨fun h => h.trans hp.symm, fun h => h.trans hp⟩
    rw [hi, sub_self]
  exact LinearMap.congr_fun heq b

theorem MorseCancellation.pointClass_eq_iff_joined {X : Type} [TopologicalSpace X] (x y : X) :
    SingularHomology.pointClass x = SingularHomology.pointClass y ↔
      Joined x y := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨b, hb⟩ :=
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 0
            (SingularHomology.pointCycle x) (SingularHomology.pointCycle y)).mp
        h
    have he := congrArg (componentChainWeight x) hb
    change
      componentChainWeight x (SingularChains.boundaryOne X b) =
        componentChainWeight x (SingularChains.pointChain x - SingularChains.pointChain y) at he
    rw [componentChainWeight_boundary, map_sub, componentChainWeight_point,
      componentChainWeight_point, if_pos (Joined.refl x), if_neg hn] at he
    norm_num at he
  · rintro ⟨p⟩
    apply
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 0
          (SingularHomology.pointCycle x) (SingularHomology.pointCycle y)).mpr
    exact ⟨SingularChains.pathChain p.symm, SingularChains.boundaryOne_pathChain p.symm⟩

theorem MorseCancellation.joined_iff_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y := by
  rw [← pointClass_eq_iff_joined, ← pointClass_eq_iff_joined, ←
    SingularHomology.singularHomologyMap_pointClass f, ←
    SingularHomology.singularHomologyMap_pointClass f, hf.eq_iff]

theorem MorseCancellation.pathConnectedSpace_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PathConnectedSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) :
    PathConnectedSpace X := by
  exact
    ⟨inferInstance, fun x y =>
      (joined_iff_of_homologyZero_injective f hf x y).mp (PathConnectedSpace.joined (f x) (f y))⟩

theorem MorseCancellation.pathConnectedSpace_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  let : Nonempty X := ⟨e.invFun (Classical.arbitrary Y)⟩
  exact
    pathConnectedSpace_of_homologyZero_injective e.toFun
      (SingularHomology.homotopyEquivHomologyEquiv e 0).injective

theorem MorseCancellation.ordered_upper_pathConnected_of_later_transfers {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (htransfer :
      ∀ j : Fin S.count,
        i.val < j.val →
          PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
            PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) :
    PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
  have hall :
    ∀ k : ℕ,
      ∀ i : Fin S.count,
        S.count - 1 - i.val = k →
          (∀ j : Fin S.count,
              i.val < j.val →
                PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
                  PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) →
            PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hindices
      have hpos : 0 < S.count := (Nat.zero_le i.val).trans_lt i.isLt
      by_cases hlast : i.val = S.count - 1
      · have hi : S.point i = S.last hpos := congrArg S.point (Fin.ext hlast)
        have hset : {x : M | f x ≤ S.upper (S.point i)} = Set.univ := by
          rw [hi]
          exact S.last_upper_univ hf hpos
        have hp : IsPathConnected {x : M | f x ≤ S.upper (S.point i)} :=
          hset.symm ▸ isPathConnected_univ
        exact isPathConnected_iff_pathConnectedSpace.mp hp
      · have hjlt : i.val + 1 < S.count := by omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hjmeasure : S.count - 1 - j.val < k := by
          dsimp [j]
          omega
        have hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } :=
          ih _ hjmeasure j rfl (fun q hq => hindices q (by dsimp [j] at hq; omega))
        let : PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) } :=
          hindices j (by dsimp [j]; omega) hupper
        have hij : i < j := by change i.val < i.val + 1; omega
        obtain ⟨e, -⟩ :=
          FlowConstruction.exists_regularSublevelHomotopyEquiv hf
            (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl htransfer

theorem MorseCancellation.cell_old_empty_of_empty_boundary {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] [PreconnectedSpace X]
    (D : EmbeddedCellAttachment N X) [IsEmpty (Metric.sphere (0 : N) 1)] : D.old = ∅ := by
  have hdisjoint (z : MorseHandle.UnitDisk N) : D.cell z ∉ D.old := by
    intro hz
    exact
      isEmptyElim
        (⟨z.val, mem_sphere_zero_iff_norm.mpr ((D.boundary z).mp hz)⟩ : Metric.sphere (0 : N) 1)
  have heq : D.old = (Set.range D.cell)ᶜ := by
    ext x
    constructor
    · intro hx ⟨z, hz⟩
      exact hdisjoint z (hz ▸ hx)
    · intro hx
      have hc : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
      exact hc.resolve_right hx
  have hc : IsClopen D.old := ⟨D.old_closed, heq.symm ▸ D.cell_closed.isClosed_range.isOpen_compl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact h
  · let z : MorseHandle.UnitDisk N := ⟨0, by simp⟩
    exact False.elim (hdisjoint z (h ▸ Set.mem_univ _))

theorem MorseCancellation.native_index_zero_point_unique {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hn : 0 < S.count) (hcount : nativeMorseCount E f 0 = 1) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f z = 0 → z = (S.first hn).val := by
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  change
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hcount
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hfirstmem :
    (S.first hn).val ∈
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨(S.first hn).property, hfirst⟩
  rw [hz₀, Set.mem_singleton_iff] at hfirstmem
  intro z hz hi
  have hzmem :
    z ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨hz, hi⟩
  rw [hz₀, Set.mem_singleton_iff] at hzmem
  exact hzmem.trans hfirstmem.symm

theorem MorseCancellation.native_index_one_excluded {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hcount : nativeMorseCount E f 1 = 0) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 1 := by
  have hfinite :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

def MorseCancellation.zeroChainCycle {X : Type} [TopologicalSpace X] :
    SingularChains.Chains X 0 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 0
    where
  toFun
    z :=
    SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 0 z
      (by
        have h := (SingularChains.singularComplex X).shape 0 0 (by simp)
        exact congrArg (fun f => f.hom z) h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def MorseCancellation.zeroChainClass {X : Type} [TopologicalSpace X] :
    SingularChains.Chains X 0 →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 0 :=
  (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 0).comp
    zeroChainCycle

theorem MorseCancellation.zeroChainClass_surjective {X : Type} [TopologicalSpace X] :
    Function.Surjective (zeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 0
      a
  exact ⟨c.val, rfl⟩

theorem MorseCancellation.homologyZero_linearMap_ext {X : Type} [TopologicalSpace X] {A : Type}
    [AddCommGroup A] [Module ℤ A] {L K : SingularMayerVietoris.SingularHomology X 0 →ₗ[ℤ] A}
    (h :
      ∀ x : X,
        L (SingularHomology.pointClass x) = K (SingularHomology.pointClass x)) :
    L = K := by
  have heq : L.comp zeroChainClass = K.comp zeroChainClass := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    have hσ : σ = ContinuousMap.const (SingularChains.Simplex 0) (σ (stdSimplex.vertex 0)) := by
      ext t
      exact congrArg σ (SingularChains.simplexZero_eq_vertex t)
    rw [hσ]
    exact h _
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := zeroChainClass_surjective a
  exact LinearMap.congr_fun heq z

theorem MorseCancellation.isMorseAt_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : ManifoldMorse.IsMorseAt E f p) :
    ManifoldMorse.IsMorseAt E (fun x => -f x) p := by
  obtain ⟨e, he, hp, hregular | hH⟩ := hm
  · refine ⟨e, he, hp, Or.inl ?_⟩
    change fderiv ℝ (fun x => -f (e.symm x)) (e p) ≠ 0
    rw [fderiv_fun_neg, neg_ne_zero]
    exact hregular
  · refine ⟨e, he, hp, Or.inr ?_⟩
    have hd : fderiv ℝ ((fun x => -f x) ∘ e.symm) = fun z => -fderiv ℝ (f ∘ e.symm) z := by
      funext z
      exact fderiv_fun_neg
    rw [hd, fderiv_fun_neg]
    change Function.Bijective (fun v => -(fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p) v))
    exact neg_bijective.comp hH

theorem MorseCancellation.isMorse_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (hm : ManifoldMorse.IsMorse E f) :
    ManifoldMorse.IsMorse E (fun x => -f x) := fun x => isMorseAt_neg (hm x)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.negative_finrank_neg_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.neg.NegativeCoordinates = Module.finrank ℝ c.PositiveCoordinates := by
  simp only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    ManifoldMorse.SignedMorseChart.PositiveCoordinates, MorseHandle.NegativeSpace,
    MorseHandle.PositiveSpace, finrank_euclideanSpace]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change -c.weights i = -1 ↔ c.weights i ≠ -1
  rcases c.signs i with h | h <;> norm_num [h]

theorem MorseCancellation.nativeMorseIndex_neg_add {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E (fun x => -f x) p + nativeMorseIndex E f p = Module.finrank ℝ E := by
  rw [nativeMorseIndex_eq_chart c.neg, nativeMorseIndex_eq_chart c, negative_finrank_neg_chart]
  exact (Nat.add_comm _ _).trans c.finrank_negative_add_positive

theorem MorseCancellation.nativeMorseCount_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    nativeMorseCount E (fun x => -f x) (Module.finrank ℝ E - k) = nativeMorseCount E f k := by
  unfold nativeMorseCount
  congr 1
  ext z
  rw [ManifoldMorse.criticalPoints_neg]
  change
    (z ∈ ManifoldMorse.criticalPoints E f ∧
        nativeMorseIndex E (fun x => -f x) z = Module.finrank ℝ E - k) ↔
      (z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k)
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩

theorem MorseCancellation.exists_minimal_excellent_morse_system (E : Type*) (M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            ∀ g : M → ℝ,
              ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                ManifoldMorse.IsMorse E g →
                  Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                    (ManifoldMorse.criticalPoints E f).ncard ≤
                      (ManifoldMorse.criticalPoints E g).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
            (ManifoldMorse.criticalPoints E f).ncard = n
  obtain ⟨f₀, hf₀, hm₀, -, hinj₀⟩ :=
    ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
  have hex : ∃ n, P n :=
    ⟨(ManifoldMorse.criticalPoints E f₀).ncard, f₀, hf₀, hm₀, hinj₀, rfl⟩
  obtain ⟨f, hf, hm, hinj, hcard⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  refine ⟨f, hf, hm, S, ?_⟩
  intro g hg hmg hinjg
  rw [hcard]
  exact Nat.find_min' hex ⟨g, hg, hmg, hinjg, rfl⟩

theorem MorseCancellation.minimal_excellent_morse_forbids_pair_removal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
    (hminimal :
      ∀ h : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
          ManifoldMorse.IsMorse E h →
            Set.InjOn h (ManifoldMorse.criticalPoints E h) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E h).ncard)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g)) :
    (ManifoldMorse.criticalPoints E g).ncard + 2 ≠
      (ManifoldMorse.criticalPoints E f).ncard := by
  have hle := hminimal g hg hmg hinjg
  omega

theorem MorseCancellation.distinct_critical_values_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) :
    Set.InjOn (fun x => -f x) (ManifoldMorse.criticalPoints E (fun x => -f x)) := by
  rw [ManifoldMorse.criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

theorem MorseCancellation.minimal_excellent_morse_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        ManifoldMorse.IsMorse E g →
          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
            (ManifoldMorse.criticalPoints E (fun x => -f x)).ncard ≤
              (ManifoldMorse.criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh :=
    hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [ManifoldMorse.criticalPoints_neg] using hh

theorem MorseCancellation.unitSphere_isEmpty_of_finrank_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] (hA : Module.finrank ℝ A = 0) :
    IsEmpty (PuncturedHandle.UnitSphere A) := by
  let _ : Subsingleton A := (Module.finrank_eq_zero_iff_of_free ℝ A).mp hA
  refine ⟨fun v => ?_⟩
  have hh := mem_sphere_zero_iff_norm.mp v.property
  rw [Subsingleton.elim (v : A) 0, norm_zero] at hh
  norm_num at hh

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeIndexDisorder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : ℕ :=
  if hfinite : (ManifoldMorse.criticalPoints E f).Finite then
    let _ := hfinite.fintype
    IndexDisorder.finiteIndexDisorder
      (fun x : ManifoldMorse.criticalPoints E f => f x)
      (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x)
  else 0

theorem MorseCancellation.nativeIndexDisorder_eq_of_finite {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite) :
    letI := hfinite.fintype
    nativeIndexDisorder E f =
      IndexDisorder.finiteIndexDisorder
        (fun x : ManifoldMorse.criticalPoints E f => f x)
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical simp only [nativeIndexDisorder, dif_pos hfinite]

theorem MorseCancellation.nativeIndexDisorder_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    letI := hfinite.fintype
    nativeIndexDisorder E g =
      IndexDisorder.finiteIndexDisorder
        (fun x : ManifoldMorse.criticalPoints E f => g x)
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  let _ := hfinite.fintype
  have hgfinite : (ManifoldMorse.criticalPoints E g).Finite := hcrit.symm ▸ hfinite
  let _ := hgfinite.fintype
  let e : ManifoldMorse.criticalPoints E f ≃ ManifoldMorse.criticalPoints E g :=
    Equiv.setCongr hcrit.symm
  rw [nativeIndexDisorder_eq_of_finite hgfinite]
  rw [←
    IndexDisorder.finiteIndexDisorder_comp_equiv
      (fun x : ManifoldMorse.criticalPoints E g => g x)
      (fun x : ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) e]
  have hw :
    ((fun x : ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) ∘ e) =
      fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x := by
    funext x
    exact hindex x x.property
  rw [hw]
  rfl

theorem MorseCancellation.nativeIndexDisorder_exchange_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindexlt : nativeMorseIndex E f q < nativeMorseIndex E f p)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    nativeIndexDisorder E g < nativeIndexDisorder E f := by
  classical
  let _ : DecidableEq (ManifoldMorse.criticalPoints E f) := fun a b =>
    Classical.propDecidable (a = b)
  let _ := hfinite.fintype
  have hform :
    (fun x : ManifoldMorse.criticalPoints E f => g x) =
      (fun x : ManifoldMorse.criticalPoints E f => f x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_right] using hgq
    have hh :=
      (hothers x x.property (fun h => hxp (Subtype.ext h))
          (fun h => hxq (Subtype.ext h))).self_of_nhds
    simpa only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hh
  rw [nativeIndexDisorder_transport hfinite hcrit hindex,
    nativeIndexDisorder_eq_of_finite hfinite, hform]
  have hi : Function.Injective (fun x : ManifoldMorse.criticalPoints E f => f x) :=
    fun x y h => Subtype.ext (hinj x.property y.property h)
  exact
    IndexDisorder.finiteIndexDisorder_swap_lt (h :=
      fun x : ManifoldMorse.criticalPoints E f => f x) hi
      (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) (p := p) (q := q)
      hpq hconsecutive hindexlt

theorem MorseCancellation.exists_transverse_sheet_of_circle_placement {A B E HA HB H X Y N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace HA] {I : ModelWithCorners ℝ A HA}
    [TopologicalSpace X] [ChartedSpace HA X] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HB] {I' : ModelWithCorners ℝ B HB} [TopologicalSpace Y] [ChartedSpace HB Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] (P : Diffeomorph J J N N ∞) {γ δ : X → N} {β : Y → N}
    {x : X} {y : Y} (hγ : MDifferentiableAt I J γ x) (hβ : MDifferentiableAt I' J β y)
    (hplace : ∀ z, P (γ z) = δ z) (hcross : β y = δ x)
    (htrans : NativeTransversality.At I I' J δ β x y) :
    ∃ β' : Y → N,
      MDifferentiableAt I' J β' y ∧
        β' y = γ x ∧ NativeTransversality.At I I' J γ β' x y ∧ ∀ z, P (β' z) = β z := by
  let β' := P.symm ∘ β
  have hβ' : MDifferentiableAt I' J β' y :=
    (P.symm.contMDiff.mdifferentiableAt (by simp)).comp y hβ
  have hcross' : β' y = γ x := by
    apply P.injective
    change P (P.symm (β y)) = P (γ x)
    rw [P.apply_symm_apply, hcross, hplace]
  have hforward (z : Y) : P (β' z) = β z := P.apply_symm_apply (β z)
  refine ⟨β', hβ', hcross', ?_, hforward⟩
  apply
    (TransverseGerms.native_transversality_partial_diffeomorph_iff P.toPartialDiffeomorph
        hγ hβ' hcross' (Set.mem_univ _)).mpr
  have hγeq : P.toPartialDiffeomorph ∘ γ = δ := funext hplace
  have hβeq : P.toPartialDiffeomorph ∘ β' = β := funext hforward
  rw [hγeq, hβeq]
  exact htrans

theorem MorseCancellation.exists_embedded_avoidance_into_level_basin {E M A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, M)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E) {K L C : Set A} (hK : IsCompact K)
    (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f₀ K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, f₀ x ∈ FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, M),
      ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧
        f₀.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
              (∀ x y, g x = g y → f₀ x = f₀ y) ∧
                ∀ x,
                  (f₀ x ∈ FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
                    g x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun p : J × V => b p.1 p.2) :=
    contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun p => b p.1 p.2, hs.continuous⟩
  have hrange : Set.range B = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (Set.range B) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ Set.range B := by
    intro x hx
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range f₀ B hf₀ hs
      hclosed hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ Set.range B ∨ x ∈ L := by
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hx
  simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using havoid x hx'

theorem MorseCancellation.superlevel_bound_of_critical_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} (hboundary : ∀ y, f y = l → g y = l)
    (hcritical : ∀ y ∈ ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    ∀ x, l ≤ f x → l ≤ g x := by
  intro x hx
  have hK : IsCompact {y : M | l ≤ f y} := (isClosed_le continuous_const hf).isCompact
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hg.continuous.continuousOn
  have hgp : l ≤ g p := by
    by_cases hlt : l < f p
    · have hlocal : IsLocalMin g p := by
        filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hlt] with y hy
        exact hmin hy.le
      exact hcritical p (ManifoldMorse.mem_criticalPoints_of_localMin hg hlocal) hp
    · have heq : f p = l := le_antisymm (le_of_not_gt hlt) hp
      exact (hboundary p heq).ge
  exact hgp.trans (hmin hx)

theorem MorseCancellation.birth_preserves_lower_levels {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} {U : Set M} {p q : M} (hU : U ⊆ {y : M | l < f y})
    (hexterior : ∀ y, y ∉ U → g =ᶠ[𝓝 y] f)
    (hkeep : ∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hcrit :
      ∀ y ∈ ManifoldMorse.criticalPoints E g,
        y ∈ ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hp : l ≤ g p) (hq : l ≤ g q) {a : ℝ} (ha : a < l) :
    (∀ y, g y = a ↔ f y = a) ∧ (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) := by
  have hout (y : M) (hy : f y ≤ l) : y ∉ U := fun h => (hU h).not_ge hy
  have hbound : ∀ y, l ≤ f y → l ≤ g y := by
    apply superlevel_bound_of_critical_bound hf hg
    · intro y hy
      exact (hexterior y (hout y hy.le)).self_of_nhds.trans hy
    · intro y hy hfy
      rcases hcrit y hy with hold | rfl | rfl
      · rw [(hkeep y hold).self_of_nhds]
        exact hfy
      · exact hp
      · exact hq
  refine ⟨?_, fun y hy => hexterior y (hout y (hy.trans ha.le))⟩
  intro y
  constructor
  · intro hgy
    have hfy : f y ≤ l := by
      by_contra h
      have hh := hbound y (le_of_not_ge h)
      rw [hgy] at hh
      exact ha.not_ge hh
    exact ((hexterior y (hout y hfy)).self_of_nhds).symm.trans hgy
  · intro hfy
    exact (hexterior y (hout y (hfy ▸ ha.le))).self_of_nhds.trans hfy

def MorseCancellation.equalLevelDiffeomorph {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f g : M → ℝ} {a : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a) :
    let _ := RegularLevel.chartedSpace hf hfr
    let _ := RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      { y : M // f y = a } { y : M // g y = a } ∞ := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let F : { y : M // f y = a } → { y : M // g y = a } := fun y => ⟨y, (heq y).mpr y.property⟩
  let G : { y : M // g y = a } → { y : M // f y = a } := fun y => ⟨y, (heq y).mp y.property⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun :=
        (RegularLevel.contMDiff_iff_inclusion hg hgr 𝓘(ℝ, RegularLevel.Model E) F).mpr
          (RegularLevel.contMDiff_inclusion hf hfr)
      contMDiff_invFun :=
        (RegularLevel.contMDiff_iff_inclusion hf hfr 𝓘(ℝ, RegularLevel.Model E) G).mpr
          (RegularLevel.contMDiff_inclusion hg hgr) }

theorem MorseCancellation.regular_level_of_retained_critical_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {p q : M}
    (hcrit :
      ∀ y ∈ ManifoldMorse.criticalPoints E g,
        y ∈ ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hkeep : ∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) (hp : a < g p)
    (hq : a < g q) : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g := by
  intro y hy hcy
  rcases hcrit y hcy with hold | rfl | rfl
  · exact hfr y (((hkeep y hold).self_of_nhds).symm.trans hy) hold
  · exact hp.ne' hy
  · exact hq.ne' hy

theorem MorseCancellation.isotopicToIdentity_conj {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
    (e : Diffeomorph I J M N ∞) {d : Diffeomorph I I M M ∞}
    (hd : SupportedDiffeomorph.IsotopicToIdentity d) :
    SupportedDiffeomorph.IsotopicToIdentity ((e.symm.trans d).trans e) := by
  obtain ⟨A, hA, hA0, hA1, hslices⟩ := hd
  refine
    ⟨(fun p => e (A (p.1, e.symm p.2))),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hA0, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (d (e.symm y))
    rw [hA1]
  · intro t
    obtain ⟨dₜ, hdₜ⟩ := hslices t
    refine ⟨(e.symm.trans dₜ).trans e, ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (dₜ (e.symm y))
    rw [hdₜ]

theorem MorseCancellation.unit_level_count_of_circle_placement {M X : Type*} [TopologicalSpace M]
    (F : Flow ℝ M) {f : M → ℝ} {a : ℝ} {p q : M} (P : { y : M // f y = a } ≃ { y : M // f y = a })
    (δ : X → { y : M // f y = a }) (z₀ : X)
    (hplacement : ∀ x, Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ↔ P x ∈ Set.range δ)
    (hsingle : ∀ z, Filter.Tendsto (fun t => F t (δ z).val) Filter.atTop (𝓝 q) ↔ z = z₀) :
    {x : { y : M // f y = a } |
          Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
            Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)}.ncard =
      1 := by
  have heq :
    {x : { y : M // f y = a } |
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)} =
      {P.symm (δ z₀)} := by
    ext x
    constructor
    · rintro ⟨hx, hforward⟩
      obtain ⟨z, hz⟩ := (hplacement x).mp hx
      have hz0 : z = z₀ := (hsingle z).mp (hz.symm ▸ hforward)
      apply Set.mem_singleton_iff.mpr
      apply P.injective
      rw [P.apply_symm_apply, ← hz, hz0]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      refine ⟨(hplacement _).mpr ⟨z₀, (P.apply_symm_apply _).symm⟩, ?_⟩
      rw [P.apply_symm_apply]
      exact (hsingle z₀).mpr rfl
  rw [heq]
  exact Set.ncard_singleton _

theorem MorseCancellation.no_other_connections_of_two_level_endpoints {M : Type*} [TopologicalSpace M]
    [T2Space M] (F : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {C : Set M} (hinj : Set.InjOn f C)
    (p q r : C) {a : ℝ} (hpa : a < f p) (hgap : ∀ j : C, f j < f p → f j < a)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hends :
      ∀ x : { y : M // f y = a },
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p.val) →
          Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 q.val) ∨
            Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 r.val)) :
    ∀ j : C,
      j ≠ p →
        j ≠ q →
          j ≠ r →
            ∀ x,
              ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)) := by
  intro j hjp hjq hjr x hx
  have hforwardHeight := hf.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f p :=
    (hmono x).le_of_tendsto hforwardHeight 0 |>.trans ((hmono x).ge_of_tendsto hbackwardHeight 0)
  have hlt : f j < f p :=
    lt_of_le_of_ne hle (fun h => hjp (Subtype.ext (hinj j.property p.property h)))
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits F hf hx.1 hx.2 hpa
      (hgap j hlt)
  let z : { y : M // f y = a } := ⟨F t x, ht⟩
  have hzb : Filter.Tendsto (fun s => F s z.val) Filter.atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff F t x p.val).mpr hx.1
  have hzf : Filter.Tendsto (fun s => F s z.val) Filter.atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff F t x j.val).mpr hx.2
  rcases hends z hzb with hq | hr
  · exact hjq (Subtype.ext (tendsto_nhds_unique hzf hq))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzf hr))

theorem MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} {m : ℕ} {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB]
    {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hdim : Module.finrank ℝ E = m + 1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f) (hrp : f r < f p) (hpq : f p < f q)
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)))
    {z : M} (hzp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p.val))
    (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q.val))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → M} {β : Y → M} {x : X} {y : Y} (hα : MDifferentiableAt I 𝓘(ℝ, E) α x)
    (hβ : MDifferentiableAt I' 𝓘(ℝ, E) β y) (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p.val))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) α β x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
                (ManifoldMorse.criticalPoints E f).ncard ∧
              (∀ w,
                  w ∈ ManifoldMorse.criticalPoints E g ↔
                    w ∈ ManifoldMorse.criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
                ∀ w ∈ ManifoldMorse.criticalPoints E g,
                  nativeMorseIndex E g w = nativeMorseIndex E f w := by
  obtain ⟨h, hh, hmh, hcrit, hinjh, -, -, hpqh, hconsecutive, hdesch, hmodelsh, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf hm hinj hV F hF hzero hdesc hmodels p r q hrp hpq
      hnoconnection
  have hpcrit : p.val ∈ ManifoldMorse.criticalPoints E h := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ ManifoldMorse.criticalPoints E h := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsh p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsh q.val hqcrit
  have hidx :
    Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp, hindices q.val q.property,
      hindices p.val p.property]
    exact hindex
  have hcard :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using hidx
  obtain ⟨W⟩ := ManifoldMorse.nonempty_surgeryWindows hh hmh hinjh
  let ph : ManifoldMorse.criticalPoints E h := ⟨p.val, hpcrit⟩
  let qh : ManifoldMorse.criticalPoints E h := ⟨q.val, hqcrit⟩
  have hconsecutiveh : ∀ s : ManifoldMorse.criticalPoints E h, ¬(h ph < h s ∧ h s < h qh) :=
    by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W ph qh hconsecutiveh
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hh hmh hdim hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdesch F hF hinjh hpcrit hqcrit hpqh
      (W.lower_lt_value ph) (W.value_lt_upper qh) hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0
      hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinjh (fun w hw => ((hcritg w).mp hw).1) hkeep
  rw [hcrit] at hcount
  refine ⟨g, hg, hmg, hinjg, hcount, ?_, ?_⟩
  · intro w
    rw [hcritg w, hcrit]
  · intro w hw
    exact
      (nativeMorseIndex_congr_germ (hkeep w hw)).trans (hindices w (hcrit ▸ ((hcritg w).mp hw).1))

theorem MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) : ∃ u v : Metric.sphere (0 : V) 1, u ≠ v := by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := UnitSphereEquiv.homeomorph L
  let u : Metric.sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  let v : Metric.sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  refine ⟨e.symm u, e.symm v, ?_⟩
  intro heq
  have hh : u = v := e.symm.injective heq
  have hval : (1 : ℝ) = -1 := congrArg Subtype.val hh
  norm_num at hval

theorem MorseCancellation.birth_preserves_lower_index_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a : ℝ}
    {k : ℕ}
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f) (hp : a < g p)
    (hq : a < g q)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k) :
    ∀ z : ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ k := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · rw [nativeMorseIndex_congr_germ (hkeep z.val hold)]
    apply hlow ⟨z.val, hold⟩
    rwa [← (hkeep z.val hold).self_of_nhds]
  · exact False.elim (hp.not_ge (hzp ▸ hz))
  · exact False.elim (hq.not_ge (hzq ▸ hz))

theorem MorseCancellation.birth_first_new_value_gap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a b : ℝ}
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hreg : ∀ z, f z = a → z ∉ ManifoldMorse.criticalPoints E f)
    (hband : ∀ z, f z ∈ Set.Ioo a b → z ∉ ManifoldMorse.criticalPoints E f) (hp : g p < b)
    (hpq : g p < g q) : ∀ z : ManifoldMorse.criticalPoints E g, g z < g p → g z < a := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · have hzb : g z < b := hz.trans hp
    have heq := (hkeep z.val hold).self_of_nhds
    by_contra hnot
    have haz : a ≤ f z := by rw [← heq]; exact le_of_not_gt hnot
    have hne : a ≠ f z := fun h => hreg z.val h.symm hold
    exact hband z.val ⟨lt_of_le_of_ne haz hne, by rwa [← heq]⟩ hold
  · exact False.elim ((hzp ▸ hz : g p < g p).false)
  · exact False.elim (hpq.not_gt (hzq ▸ hz))

theorem MorseCancellation.birth_preserves_unique_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (m : ManifoldMorse.criticalPoints E f)
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : nativeMorseIndex E g p ≠ 0) (hq : nativeMorseIndex E g q ≠ 0)
    (hunique : ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∀ z ∈ ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m.val := by
  intro z hz hi
  rcases hcrit z hz with hold | rfl | rfl
  · have hiold : nativeMorseIndex E f z = 0 :=
      (nativeMorseIndex_congr_germ (hkeep z hold)).symm.trans hi
    exact congrArg Subtype.val (hunique ⟨z, hold⟩ hiold)
  · exact False.elim (hp hi)
  · exact False.elim (hq hi)

theorem MorseCancellation.indexed_criticalPoints_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M}
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    {z : M | z ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
    exact ⟨⟨hzf, (hindex z hz).symm.trans hi⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hi⟩, hzp, hzq⟩
    have hz := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hz, (hindex z hz).trans hi⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeMorseCount_removed_of_index_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_removed_of_index_eq hcrit hindex k]
  exact (Nat.add_assoc _ _ _).trans hc

theorem MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {k : ℕ} (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_removed_of_index_eq hfinite hp hq hpq hcrit hindex
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

theorem MorseCancellation.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E g).ncard =
                  (ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        ManifoldMorse.IsMorse E g →
          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
            (ManifoldMorse.criticalPoints E g).ncard =
                (ManifoldMorse.criticalPoints E (fun x => -f x)).ncard →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  intro g hg hmg hinjg hcard
  have hh :=
    hsecondary (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
      (by simpa only [ManifoldMorse.criticalPoints_neg] using hcard)
  have hf1 := nativeMorseCount_neg hf hm (k := 1) (by omega)
  have hf5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hg1 := nativeMorseCount_neg hg hmg (k := 1) (by omega)
  have hg5 := nativeMorseCount_neg hg hmg (k := 5) (by omega)
  simp only [hdim, Nat.reduceSub] at hf1 hf5 hg1 hg5
  omega

theorem MorseCancellation.native_indices_monotone {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) :
    Monotone (fun i : Fin S.count => nativeMorseIndex E f (S.point i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact horder _ _ (S.point_strictMono hlt)
  · exact le_rfl

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_middle_index_blocks {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ,
      S.HasIndexTwoPrefix r ∧
        ∃ _ : r + c < S.count,
          S.HasIndexThreeBlock r c ∧
            r + c + 1 < S.count ∧
              ∀ i : Fin S.count,
                r + c < i.val →
                  4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by
  have hn := S.count_pos hf
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hmono : Monotone index := native_indices_monotone S horder
  have hfirst : index ⟨0, hn⟩ = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hlast : index ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ = 6 :=
    (nativeMorseIndex_eq_chart (S.data (S.last hn)).chart).trans
      ((S.last_index_dimension hf hn).trans hdim)
  have hcut (k : ℕ) : ∃ j : Fin S.count, ∀ i : Fin S.count, i ≤ j ↔ index i ≤ k := by
    let K := Finset.univ.filter (fun i : Fin S.count => index i ≤ k)
    have hK : K.Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfirst]; exact Nat.zero_le k⟩⟩
    let j := K.max' hK
    have hj : index j ≤ k := (Finset.mem_filter.mp (K.max'_mem hK)).2
    refine ⟨j, fun i => ⟨fun hij => (hmono hij).trans hj, ?_⟩⟩
    intro hi
    exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨a, ha⟩ := hcut 2
  obtain ⟨b, hb⟩ := hcut 3
  have hab : a ≤ b := (hb a).mpr (((ha a).mp le_rfl).trans (by omega))
  have hbLast : b.val + 1 < S.count := by
    have hb3 := (hb b).mp le_rfl
    have hne : b ≠ ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      intro he
      rw [he, hlast] at hb3
      omega
    have hvalne : b.val ≠ S.count - 1 := fun he => hne (Fin.ext he)
    omega
  have hnonzero (i : Fin S.count) (hi : 0 < i.val) : index i ≠ 0 := by
    intro hz
    have he : S.point i = S.first hn :=
      Subtype.ext (native_index_zero_point_unique S hf hn hzero _ (S.point i).property hz)
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have hnonone (i : Fin S.count) : index i ≠ 1 :=
    native_index_one_excluded S hone _ (S.point i).property
  refine ⟨a.val, b.val - a.val, ?_, by omega, ?_, by omega, ?_⟩
  · intro i hi hia
    have hi2 := (ha i).mp (show i ≤ a from hia)
    have hi0 := hnonzero i hi
    have hi1 := hnonone i
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 2
    omega
  · intro i hai hib
    have hi3 := (hb i).mp (show i ≤ b by change i.val ≤ b.val; omega)
    have hi2 : ¬index i ≤ 2 := fun he => (not_le_of_gt hai) ((ha i).mpr he)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    omega
  · intro i hbi
    have hi3 : ¬index i ≤ 3 := fun he =>
      (by
        have hh : i.val ≤ b.val := (hb i).mpr he
        omega)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change 4 ≤ index i
    omega

def MorseCancellation.nativeMiddleBlockPoint {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) (j : Fin n) :
    ManifoldMorse.criticalPoints E f :=
  S.toSurgeryWindows.point ⟨r + j.val + 1, by omega⟩

end
