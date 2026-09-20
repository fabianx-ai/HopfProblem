/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing

/-!
# Clean crossing charts and strip patches

Transverse coordinates and simultaneous sheet charts, isolating crossing neighbourhoods and finiteness of transverse intersections, sphere boundary and sphere normal coordinates, strip coordinates and strip normal data, clean corner patches, clean strip patches and clean bigon boundaries.

Moved verbatim from the project stock file `Hopf/SingularHomology.lean` (integration 4,
`Lib/reports/integration-4/singhom-moves.md`); the families here are
`TransverseCoordinates`, `NativeEuclideanEmbedding.SmoothRetraction`, `SphereBoundary`, `SphereNormalCoordinates`, `ManifoldMorse.MorseSurgeryData`, `StripCoordinates`, `StripNormalData`, `CleanCornerPatch`, `CleanStripPatch`, `WhitneyPairModel`, `CleanBigonBoundary`. The declarations keep their historical dotted names
and their order; the file order is the dependency order.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

def TransverseCoordinates.sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (q : D × Z) : A :=
  f q.1 + g q.2 - f 0

theorem TransverseCoordinates.sumMap_left {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup Z] [NormedAddCommGroup A] (f : D → A) (g : Z → A) (hzero : g 0 = f 0)
    (x : D) : sumMap f g (x, 0) = f x := by simp [sumMap, hzero]

theorem TransverseCoordinates.sumMap_right {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (z : Z) : sumMap f g (0, z) = g z := by
  simp [sumMap, add_sub_cancel_left]

theorem TransverseCoordinates.contDiffOn_sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} {U : Set D} {V : Set Z} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) : ContDiffOn ℝ ∞ (sumMap f g) (U ×ˢ V) :=
  ((hf.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).add
        (hg.comp contDiff_snd.contDiffOn (fun _ hx => hx.2))).sub
    contDiffOn_const

theorem TransverseCoordinates.hasFDerivAt_sumMap_zero {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} (hf : DifferentiableAt ℝ f 0)
    (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (sumMap f g) ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) (0, 0) := by
  have hfst := (ContinuousLinearMap.fst ℝ D Z).hasFDerivAt (x := (0, 0))
  have hsnd := (ContinuousLinearMap.snd ℝ D Z).hasFDerivAt (x := (0, 0))
  have hd :=
    ((hf.hasFDerivAt.comp (0, 0) hfst).add (hg.hasFDerivAt.comp (0, 0) hsnd)).sub
      (hasFDerivAt_const (f 0) (0, 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  simp [ContinuousLinearMap.coprod_apply]

def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) : D × Z → M :=
  r.toFun ∘ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g)

def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinateDomain {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (U : Set D) (V : Set Z) : Set (D × Z) :=
  (U ×ˢ V) ∩ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) ⁻¹' r.domain

theorem NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_left {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [NormedAddCommGroup Z] {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (f : D → M) (g : Z → M) (hzero : g 0 = f 0) (x : D) :
    r.sheetCoordinates f g (x, 0) = f x := by
  have hsum :=
    TransverseCoordinates.sumMap_left (e.toFun ∘ f) (e.toFun ∘ g) (congrArg e.toFun hzero) x
  change r.toFun (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (x, 0)) = f x
  rw [hsum]
  exact r.retract (f x)

theorem NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_right {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (z : Z) : r.sheetCoordinates f g (0, z) = g z := by
  rw [sheetCoordinates, Function.comp_apply, TransverseCoordinates.sumMap_right]
  exact r.retract (g z)

theorem NativeEuclideanEmbedding.SmoothRetraction.zero_mem_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedAddCommGroup Z]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) (f : D → M) (g : Z → M)
    {U : Set D} {V : Set Z} (hU : (0 : D) ∈ U) (hV : (0 : Z) ∈ V) :
    (0, 0) ∈ r.sheetCoordinateDomain f g U V := by
  refine ⟨⟨hU, hV⟩, ?_⟩
  change TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) ∈ r.domain
  rw [TransverseCoordinates.sumMap_right]
  exact r.contains ⟨g 0, rfl⟩

theorem NativeEuclideanEmbedding.SmoothRetraction.isOpen_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    IsOpen (r.sheetCoordinateDomain f g U V) :=
  (TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
        (e.smooth.comp_contMDiffOn hg).contDiffOn).continuousOn.isOpen_inter_preimage
    (hU.prod hV) r.open_domain

theorem NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_sheetCoordinates
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g)
      (r.sheetCoordinateDomain f g U V) :=
  r.smooth.comp
    ((TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
          (e.smooth.comp_contMDiffOn hg).contDiffOn).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hx => hx.2)

theorem NativeEuclideanEmbedding.SmoothRetraction.mfderiv_sheetCoordinates_zero
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} (hzero : g 0 = f 0) (hf : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f 0)
    (hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g 0) :
    mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0) =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) := by
  have heF := (e.smooth.contMDiffAt.comp 0 hf).contDiffAt
  have heG := (e.smooth.contMDiffAt.comp 0 hg).contDiffAt
  have hsum :=
    TransverseCoordinates.hasFDerivAt_sumMap_zero (heF.differentiableAt (by simp))
      (heG.differentiableAt (by simp))
  have hbase :
    TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) = e.toFun (f 0) := by
    rw [TransverseCoordinates.sumMap_right]
    exact congrArg e.toFun hzero
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0)) := by
    rw [hbase]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f 0, rfl⟩))).mdifferentiableAt
        (by simp)
  have hdf :
    fderiv ℝ (e.toFun ∘ f) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  have hdg :
    fderiv ℝ (e.toFun ∘ g) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    rw [hzero]
  rw [sheetCoordinates, mfderiv_comp (0, 0) hr hsum.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hsum.fderiv, hbase, hdf, hdg]
  apply ContinuousLinearMap.ext
  intro q
  have hleft :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) q.1)) (r.mfderiv_retract_comp (f 0))
  have hright :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) q.2)) (r.mfderiv_retract_comp (f 0))
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f 0))
  let T : E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)
  let F : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0
  let G : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0
  change R (T (F q.1) + T (G q.2)) = F q.1 + G q.2
  change R (T (F q.1)) = F q.1 at hleft
  change R (T (G q.2)) = G q.2 at hright
  rw [map_add, hleft, hright]

theorem TransverseCoordinates.isInvertible_coprod_of_surjective {D Z E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ E] (F : D →L[ℝ] E) (G : Z →L[ℝ] E)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Function.Surjective (F.coprod G)) : (F.coprod G).IsInvertible := by
  have hd : Module.finrank ℝ (D × Z) = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod] using hdim
  have hi : Function.Injective (F.coprod G) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr ht
  let L := (LinearEquiv.ofBijective (F.coprod G).toLinearMap ⟨hi, ht⟩).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

theorem exists_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  let W₀ := r.sheetCoordinateDomain f g U V
  have hW₀ : IsOpen W₀ := r.isOpen_sheetCoordinateDomain hU hV hf hg
  have hs : ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g) W₀ :=
    r.contMDiffOn_sheetCoordinates hf hg
  let W := W₀ ∩ r.sheetCoordinates f g ⁻¹' O
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hW₀ hO
  have h0W : (0, 0) ∈ W := by
    refine ⟨r.zero_mem_sheetCoordinateDomain f g h0U h0V, ?_⟩
    change r.sheetCoordinates f g (0, 0) ∈ O
    rw [r.sheetCoordinates_left f g hzero]
    exact h0O
  have hinv : (mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0)).IsInvertible := by
    rw [r.mfderiv_sheetCoordinates_zero hzero (hf.contMDiffAt (hU.mem_nhds h0U))
        (hg.contMDiffAt (hV.mem_nhds h0V))]
    exact
      TransverseCoordinates.isInvertible_coprod_of_surjective (D := D) (Z := Z) (E := E) _ _ hdim
        ht
  obtain ⟨Φ, h0Φ, hΦW, heq⟩ :=
    exists_partialDiffeomorph_into_manifold hW h0W (hs.mono Set.inter_subset_left) hinv
  obtain ⟨a, ha, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0Φ)
  refine ⟨a, ha, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · intro q hq
    exact (hΦW hq).1.1
  · intro y hy
    have hq := Φ.map_target' hy
    have hmem := (hΦW hq).2
    change r.sheetCoordinates f g (Φ.invFun y) ∈ O at hmem
    rw [heq hq] at hmem
    exact (Φ.right_inv' hy) ▸ hmem
  · intro x hx
    exact (heq hx).symm.trans (r.sheetCoordinates_left f g hzero x)
  · intro z hz
    exact (heq hz).symm.trans (r.sheetCoordinates_right f g z)

theorem exists_clean_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hembf : Topology.IsEmbedding (fun x : U => f x))
    (hembg : Topology.IsEmbedding (fun z : V => g z))
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ b : ℝ,
      0 < b ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) b ×ˢ Metric.closedBall (0 : Z) b ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) ∧
                    (∀ q ∈ Φ.source, (Φ q ∈ f '' U ↔ q.2 = 0) ∧ (Φ q ∈ g '' V ↔ q.1 = 0)) := by
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright⟩ :=
    exists_simultaneous_sheetChart hU hV h0U h0V hf hg hzero hdim ht hO h0O
  have hballU : IsOpen {x : U | (x : D) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hballV : IsOpen {z : V | (z : Z) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  obtain ⟨A, hA, hpreA⟩ := hembf.isInducing.isOpen_iff.mp hballU
  obtain ⟨B, hB, hpreB⟩ := hembg.isInducing.isOpen_iff.mp hballV
  have h0A : f 0 ∈ A := by
    have hz : (⟨0, h0U⟩ : U) ∈ {x : U | (x : D) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreA] at hz
    exact hz
  have h0B : g 0 ∈ B := by
    have hz : (⟨0, h0V⟩ : V) ∈ {z : V | (z : Z) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreB] at hz
    exact hz
  have hsmallF {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : x ∈ Metric.closedBall 0 a := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun x : U => f x) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hsmallG {z : Z} (hz : z ∈ V) (hzB : g z ∈ B) : z ∈ Metric.closedBall 0 a := by
    have hz' : (⟨z, hz⟩ : V) ∈ (fun z : V => g z) ⁻¹' B := hzB
    rw [hpreB] at hz'
    exact Metric.ball_subset_closedBall hz'
  let Ψ := PartialChart.restrictTarget Φ (hA.inter hB)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hcenter : Φ (0, 0) = f 0 := hleft 0 h0Φ
  have h0Ψ : (0, 0) ∈ Ψ.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ (0, 0) ∈ A ∩ B
    rw [hcenter]
    exact ⟨h0A, hzero ▸ h0B⟩
  obtain ⟨b, hb, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds h0Ψ)
  refine
    ⟨b, hb, Ψ, ?_, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, (fun x hx => hleft x hx.1),
      (fun z hz => hright z hz.1), ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · rintro ⟨x, z⟩ hq
    have hAq : Φ (x, z) ∈ A := hq.2.1
    have hBq : Φ (x, z) ∈ B := hq.2.2
    constructor
    · constructor
      · rintro ⟨u, hu, heq⟩
        have huA : f u ∈ A := heq ▸ hAq
        have haxis : (u, 0) ∈ Φ.source := hprod ⟨hsmallF hu huA, Metric.mem_closedBall_self ha.le⟩
        have hpair : (x, z) = (u, 0) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hleft u haxis).symm)
        exact congrArg Prod.snd hpair
      · intro hz
        change z = 0 at hz
        subst z
        exact ⟨x, (hsource hq.1).1, (hleft x hq.1).symm⟩
    · constructor
      · rintro ⟨v, hv, heq⟩
        have hvB : g v ∈ B := heq ▸ hBq
        have haxis : (0, v) ∈ Φ.source := hprod ⟨Metric.mem_closedBall_self ha.le, hsmallG hv hvB⟩
        have hpair : (x, z) = (0, v) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hright v haxis).symm)
        exact congrArg Prod.fst hpair
      · intro hx
        change x = 0 at hx
        subst x
        exact ⟨z, (hsource hq.1).2, (hright z hq.1).symm⟩

theorem exists_clean_crossingChart_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, E) (A × B) M ∞,
          Metric.closedBall (0 : A) a ×ˢ Metric.closedBall (0 : B) a ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ d.source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F (c 0) ∧
                  (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (c u)) ∧
                    (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (d v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let f := F ∘ c
  let g := G ∘ d
  have hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hg : ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ g d.source := hG.comp_contMDiffOn d.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun u : c.source => f u) :=
    hembF.comp c.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hembg : Topology.IsEmbedding (fun v : d.source => g v) :=
    hembG.comp d.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hdf :
    mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0 =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0) :=
    mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hc0)
  have hdg :
    mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0 =
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)).comp (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0) :=
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (d.mdifferentiableAt (by simp) hd0)
  have ht' :
    Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0)) := by
    rw [hdf, hdg]
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := ht w
    obtain ⟨a, ha⟩ := (PartialChart.bijective_mfderiv c hc0).2 u
    obtain ⟨b, hb⟩ := (PartialChart.bijective_mfderiv d hd0).2 v
    refine ⟨(a, b), ?_⟩
    let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)
    let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)
    let C : A →L[ℝ] D := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0
    let Q : B →L[ℝ] Z := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0
    change DF (C a) + DG (Q b) = w
    change C a = u at ha
    change Q b = v at hb
    rw [ha, hb]
    exact huv
  obtain ⟨U, hU, hpreU⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  obtain ⟨V, hV, hpreV⟩ := hembG.isInducing.isOpen_iff.mp d.open_target
  have hxU : F (c 0) ∈ U := by
    change c 0 ∈ F ⁻¹' U
    rw [hpreU]
    exact c.map_source' hc0
  have hyV : G (d 0) ∈ V := by
    change d 0 ∈ G ⁻¹' V
    rw [hpreV]
    exact d.map_source' hd0
  have hxV : F (c 0) ∈ V := hxy ▸ hyV
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart c.open_source d.open_source hc0 hd0 hf hg hxy hembf hembg
      hdim ht' (hO.inter (hU.inter hV)) ⟨hxO, hxU, hxV⟩
  refine
    ⟨a, ha, Φ, hprod, hsource, fun _ hq => (htarget hq).1,
      hleft 0 (hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩), hleft,
      hright, ?_⟩
  intro q hq
  have hqUV := (htarget (Φ.map_source' hq)).2
  have hrangeF : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨n, hn⟩
      have hnU : F n ∈ U := hn ▸ hqUV.1
      have hnT : n ∈ c.target := by
        change n ∈ F ⁻¹' U at hnU
        rwa [hpreU] at hnU
      refine ⟨c.invFun n, c.map_target' hnT, ?_⟩
      exact (congrArg F (c.right_inv' hnT)).trans hn
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  have hrangeG : Φ q ∈ Set.range G ↔ Φ q ∈ g '' d.source := by
    constructor
    · rintro ⟨p, hp⟩
      have hpV : G p ∈ V := hp ▸ hqUV.2
      have hpT : p ∈ d.target := by
        change p ∈ G ⁻¹' V at hpV
        rwa [hpreV] at hpV
      refine ⟨d.invFun p, d.map_target' hpT, ?_⟩
      exact (congrArg G (d.right_inv' hpT)).trans hp
    · rintro ⟨v, _, hv⟩
      exact ⟨d v, hv⟩
  exact ⟨hrangeF.trans (himages q hq).1, hrangeG.trans (himages q hq).2⟩

theorem exists_clean_crossingChart {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆
                (NativeParametrization.centered (D := D) x).source ×ˢ
                  (NativeParametrization.centered (D := Z) y).source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F x ∧
                  (∀ u,
                      (u, 0) ∈ Φ.source →
                        Φ (u, 0) = F (NativeParametrization.centered (D := D) x u)) ∧
                    (∀ v,
                        (0, v) ∈ Φ.source →
                          Φ (0, v) = G (NativeParametrization.centered (D := Z) y v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let c := NativeParametrization.centered (D := D) x
  let d := NativeParametrization.centered (D := Z) y
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hd0 : (0 : Z) ∈ d.source := NativeParametrization.zero_mem_centered_source y
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hdy : d 0 = y := NativeParametrization.centered_zero y
  have hxy' : G (d 0) = F (c 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c 0) ∈ O := by rw [hcx]; exact hxO
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy' hdim ht' hO
      hxO'
  exact
    ⟨a, ha, Φ, hprod, hsource, htarget, hcenter.trans (congrArg F hcx), hleft, hright, himages⟩

theorem exists_isolating_crossing_neighborhood {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    ∃ O : Set M, IsOpen O ∧ F x ∈ O ∧ O ∩ (Set.range F ∩ Set.range G) = {F x} := by
  obtain ⟨a, ha, Φ, hprod, -, -, hcenter, -, -, himages⟩ :=
    exists_clean_crossingChart hF hG hembF hembG x y hxy hdim ht isOpen_univ (Set.mem_univ _)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hFx : F x ∈ Φ.target := hcenter ▸ Φ.map_source' h0Φ
  refine ⟨Φ.target, Φ.open_target, hFx, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwF, hwG⟩
    let q := Φ.invFun w
    have hq : q ∈ Φ.source := Φ.map_target' hw
    have heq : Φ q = w := Φ.right_inv' hw
    have hqF : Φ q ∈ Set.range F := heq.symm ▸ hwF
    have hqG : Φ q ∈ Set.range G := heq.symm ▸ hwG
    have hq0 : q = (0, 0) := Prod.ext ((himages q hq).2.mp hqG) ((himages q hq).1.mp hqF)
    exact Set.mem_singleton_iff.mpr (heq.symm.trans ((congrArg Φ hq0).trans hcenter))
  · intro hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact ⟨hFx, ⟨x, rfl⟩, ⟨y, hxy⟩⟩

theorem isDiscrete_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    IsDiscrete (Set.range F ∩ Set.range G) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro z ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
  obtain ⟨O, hO, -, heq⟩ :=
    exists_isolating_crossing_neighborhood hF hG hembF hembG x y hxy hdim (ht x y hxy)
  exact ⟨O, hO, heq⟩

theorem finite_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] [CompactSpace N] [CompactSpace P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    (Set.range F ∩ Set.range G).Finite := by
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  exact
    ((isCompact_range hF.continuous).inter_right (isCompact_range hG.continuous).isClosed).finite
      (isDiscrete_transverse_intersections hF hG hembF hembG hdim ht)

def SphereBoundary.definingFunction {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  ‖x‖ ^ 2 - 1

theorem SphereBoundary.contDiff_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ContDiff ℝ ∞ (definingFunction (E := E)) :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

theorem SphereBoundary.definingFunction_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    (x : E) : definingFunction x = 0 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  simp only [definingFunction, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

theorem SphereBoundary.fderiv_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) : fderiv ℝ (definingFunction (E := E)) x = 2 • innerSL ℝ x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv

theorem SphereBoundary.fderiv_definingFunction_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x v : E) :
    fderiv ℝ (definingFunction (E := E)) x v = 0 ↔ Inner.inner ℝ x v = 0 := by
  rw [fderiv_definingFunction]
  rw [two_smul, add_apply]
  change Inner.inner ℝ x v + Inner.inner ℝ x v = 0 ↔ Inner.inner ℝ x v = 0
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

theorem SphereBoundary.common_kernel_of_immersive_sphere_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x)) :
    ∀ y,
      definingFunction y = 0 →
        ∀ v : E,
          mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ (definingFunction (E := E)) y v = 0 → v = 0 := by
  intro y hy v hfv hρv
  let x : Metric.sphere (0 : E) 1 := ⟨y, (definingFunction_eq_zero_iff y).mp hy⟩
  have hinner : Inner.inner ℝ y v = 0 := (fderiv_definingFunction_eq_zero_iff y v).mp hρv
  have hrange : v ∈ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : E) 1 → E) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hinner
  obtain ⟨w, hw⟩ := hrange
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w = v at hw
  have hextfun : (f ∘ (Subtype.val : Metric.sphere (0 : E) 1 → E)) = γ := funext hext
  have hchain :
    mfderiv (𝓡 n) J γ x =
      (mfderiv 𝓘(ℝ, E) J f y).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) := by
    rw [← hextfun,
      mfderiv_comp x (hf.mdifferentiableAt (by simp))
        ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))]
  have hγzero : mfderiv (𝓡 n) J γ x w = 0 := by
    rw [hchain]
    change
      (mfderiv 𝓘(ℝ, E) J f y)
          ((mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w) =
        0
    rw [hw]
    exact hfv
  have hwzero : w = 0 := (hγ x) (by simpa only [map_zero] using hγzero)
  rw [hwzero, map_zero] at hw
  exact hw.symm

def SphereNormalCoordinates.inclusionDerivative {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x

theorem SphereNormalCoordinates.inner_inclusionDerivative_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) (u : EuclideanSpace ℝ (Fin n)) :
    Inner.inner ℝ (x : V) (inclusionDerivative x u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) x]
  exact ⟨u, rfl⟩

theorem SphereNormalCoordinates.inner_self_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x : Metric.sphere (0 : V) 1) : Inner.inner ℝ (x : V) x = 1 := by
  have hx : ‖(x : V)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [real_inner_self_eq_norm_sq, hx, one_pow]

def SphereNormalCoordinates.normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp A.inverse)

theorem SphereNormalCoordinates.normalFrame_apply {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    normalFrame x A z = z.1 • (x : V) + inclusionDerivative x (A.inverse z.2) :=
  rfl

theorem SphereNormalCoordinates.inner_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    Inner.inner ℝ (x : V) (normalFrame x A z) = z.1 := by
  rw [normalFrame_apply, inner_add_right, inner_smul_right, inner_self_eq_one,
    inner_inclusionDerivative_zero, mul_one, add_zero]

theorem SphereNormalCoordinates.bijective_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    Function.Bijective (normalFrame x A) := by
  constructor
  · intro z w hzw
    have hfst : z.1 = w.1 := by
      simpa only [inner_normalFrame] using congrArg (fun v : V => Inner.inner ℝ (x : V) v) hzw
    have ht : inclusionDerivative x (A.inverse z.2) = inclusionDerivative x (A.inverse w.2) := by
      rw [normalFrame_apply, normalFrame_apply, hfst] at hzw
      exact add_left_cancel hzw
    have hJ : Function.Injective (inclusionDerivative (n := n) x) :=
      injective_mvfderiv_subtypeVal_sphere x
    exact Prod.ext hfst (hA.inverse.injective (hJ ht))
  · intro v
    have ht : v - Inner.inner ℝ (x : V) v • (x : V) ∈ (inclusionDerivative (n := n) x).range := by
      change
        v - Inner.inner ℝ (x : V) v • (x : V) ∈
          (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x).range
      rw [range_mvfderiv_subtypeVal]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, inner_self_eq_one, mul_one, sub_self]
    obtain ⟨u, hu⟩ := ht
    change inclusionDerivative x u = v - Inner.inner ℝ (x : V) v • (x : V) at hu
    refine ⟨(Inner.inner ℝ (x : V) v, A u), ?_⟩
    rw [normalFrame_apply, hA.inverse_apply_self, hu]
    abel

def SphereNormalCoordinates.normalJacobian {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : ℝ :=
  ((normalFrame x A).comp j.symm.toContinuousLinearMap).det

theorem SphereNormalCoordinates.normalJacobian_ne_zero {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian j x A ≠ 0 := by
  apply (RegularValues.bijective_iff_det_ne_zero _).mp
  exact (bijective_normalFrame x A hA).comp j.symm.bijective

theorem SphereNormalCoordinates.normalJacobian_change_normal_model {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] {N' : Type*} [NormedAddCommGroup N']
    [NormedSpace ℝ N'] (r : (ℝ × N) ≃L[ℝ] V) (j : N' ≃L[ℝ] N) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r)
        x (j.symm.toContinuousLinearMap.comp A) =
      normalJacobian r x A := by
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] N' := j.symm.toContinuousLinearMap.comp A
  have hj : j.symm.toContinuousLinearMap.IsInvertible := ⟨j.symm, rfl⟩
  have hB : B.IsInvertible := hj.comp hA
  have hinv (z : N) : B.inverse (j.symm z) = A.inverse z := by
    apply hB.injective
    rw [hB.self_apply_inverse]
    change j.symm z = j.symm (A (A.inverse z))
    rw [hA.self_apply_inverse]
  unfold normalJacobian
  apply congrArg ContinuousLinearMap.det
  apply ContinuousLinearMap.ext
  intro v
  change
    (r.symm v).1 • (x : V) + inclusionDerivative x (B.inverse (j.symm (r.symm v).2)) =
      (r.symm v).1 • (x : V) + inclusionDerivative x (A.inverse (r.symm v).2)
  rw [hinv]

def ManifoldMorse.MorseSurgeryData.beltNormalReference {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m) :
    (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim, Nat.add_comm])

def ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : ℝ :=
  letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  SphereNormalCoordinates.normalJacobian j x
    (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)

def ManifoldMorse.MorseSurgeryData.beltIntersectionSign {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : SignType :=
  SignType.sign (d.beltIntersectionJacobian m j g x)

def ManifoldMorse.MorseSurgeryData.beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) : Set (Hemisphere.Sphere m) :=
  g ⁻¹' Set.range d.surgery.beltSphere

theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSigns_opposite_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x y : Hemisphere.Sphere m) :
    d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1 ↔
      d.beltIntersectionJacobian m j g x * d.beltIntersectionJacobian m j g y < 0 := by
  unfold beltIntersectionSign
  rw [← sign_mul, sign_eq_neg_one_iff]

def ManifoldMorse.MorseSurgeryData.beltIntersectionCount {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel)
    (hfin : (d.beltIntersectionPoints m g).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (d.beltIntersectionSign m j g x : ℤ)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian_ne_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g → d.beltIntersectionJacobian m j g x ≠ 0 := by
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
  exact SphereNormalCoordinates.normalJacobian_ne_zero j x A hAi

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSign_unit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        d.beltIntersectionSign m j g x = 1 ∨ d.beltIntersectionSign m j g x = -1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  have hn : d.beltIntersectionSign m j g x ≠ 0 :=
    sign_ne_zero.mpr (d.beltIntersectionJacobian_ne_zero hf n m hdim j g hg ht x hx)
  rcases SignType.trichotomy (d.beltIntersectionSign m j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.finite_beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.beltIntersectionPoints m g).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg hinj ht
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    have hp : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    have hs := d.chart.finrank_negative_add_positive
    omega
  have hfin :=
    finite_transverse_intersections hg (d.belt_smooth hf n) hinj
      d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)
  have hpre : (g ⁻¹' (Set.range g ∩ Set.range d.surgery.beltSphere)).Finite :=
    hfin.preimage hinj.injOn
  exact hpre.subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

def TransverseCoordinates.normalCoordinate {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) : M → B :=
  Prod.snd ∘ Φ.symm

theorem TransverseCoordinates.contMDiffOn_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, B) ∞ (normalCoordinate Φ) Φ.target := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  exact hs.comp_contMDiffOn Φ.contMDiffOn_invFun

theorem TransverseCoordinates.mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p =
      (ContinuousLinearMap.snd ℝ D B).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm p) := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  have hd :
    mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (Φ.symm p) =
      ContinuousLinearMap.snd ℝ D B := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.snd ℝ D B).fderiv
  rw [normalCoordinate,
    mfderiv_comp p (hs.mdifferentiableAt (by simp)) (Φ.symm.mdifferentiableAt (by simp) hp), hd]
  rfl

theorem TransverseCoordinates.surjective_mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p) := by
  rw [mfderiv_normalCoordinate Φ hp]
  exact
    (show Function.Surjective (ContinuousLinearMap.snd ℝ D B) from fun w => ⟨(0, w), rfl⟩).comp
      (PartialChart.bijective_mfderiv Φ.symm hp).2

theorem TransverseCoordinates.normalCoordinate_sheet_eventually_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {N : Type*} [TopologicalSpace N]
    {F : N → M} (hF : Continuous F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) : (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hy
  have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
  exact (hclean _ hq).mp ⟨y, (Φ.right_inv' hy).symm⟩

theorem TransverseCoordinates.normalDerivative_comp_sheet_eq_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {G N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace N] [ChartedSpace G N] {F : N → M}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    {x : N} (hx : F x ∈ Φ.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)).comp (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) = 0 :=
  by
  have heq := normalCoordinate_sheet_eventually_zero Φ hF.continuous hclean hx
  have hzero : mfderiv 𝓘(ℝ, G) 𝓘(ℝ, B) (normalCoordinate Φ ∘ F) x = 0 := by
    rw [heq.mfderiv_eq]
    simp only [mfderiv_const]
    rfl
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hx)
  rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))] at hzero
  exact hzero

theorem StripCoordinates.hasDerivAt_horizontalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (u, s)) (fderiv ℝ F (t, s) (1, 0)) t := by
  have hi : HasDerivAt (fun u : ℝ => (u, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  exact hF.hasFDerivAt.comp_hasDerivAt t hi

abbrev StripCoordinates.Space (A B : Type*) :=
  (ℝ × A) × B

def StripCoordinates.center {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (t : ℝ) : Space A B :=
  ((t, 0), 0)

def StripCoordinates.model {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (v : ℝ → B) (p : ℝ × ℝ) : Space A B :=
  ((p.1, 0), p.2 • v p.1)

def StripCoordinates.normalDerivative {A B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : (ℝ × ℝ) → Space A B) (t : ℝ) : B :=
  fderiv ℝ (fun p => (F p).2) (t, 0) (0, 1)

def StripCoordinates.blend {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (F₀ F₁ : (ℝ × ℝ) → Space A B)
    (β₀ β₁ : ℝ → ℝ) (p : ℝ × ℝ) : Space A B :=
  model v p + β₀ p.1 • (F₀ p - model v p) + β₁ p.1 • (F₁ p - model v p)

theorem StripCoordinates.contDiff_model {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (model (A := A) v) :=
  (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.smul (hv.comp contDiff_fst))

theorem StripCoordinates.contDiff_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (blend v F₀ F₁ β₀ β₁) :=
  ((contDiff_model hv).add ((hβ₀.comp contDiff_fst).smul (hF₀.sub (contDiff_model hv)))).add
    ((hβ₁.comp contDiff_fst).smul (hF₁.sub (contDiff_model hv)))

theorem StripCoordinates.model_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (t : ℝ) :
    model (A := A) v (t, 0) = StripCoordinates.center t := by
  simp only [model, StripCoordinates.center, zero_smul]

theorem StripCoordinates.blend_zero {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {β₀ β₁ : ℝ → ℝ} (h₀ : ∀ t, β₀ t ≠ 0 → F₀ (t, 0) = StripCoordinates.center t)
    (h₁ : ∀ t, β₁ t ≠ 0 → F₁ (t, 0) = StripCoordinates.center t) (t : ℝ) :
    blend v F₀ F₁ β₀ β₁ (t, 0) = StripCoordinates.center t := by
  have hterm₀ : β₀ t • (F₀ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, model_zero, sub_self, smul_zero]
  have hterm₁ : β₁ t • (F₁ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, model_zero, sub_self, smul_zero]
  change
    model v (t, 0) + β₀ t • (F₀ (t, 0) - model v (t, 0)) + β₁ t • (F₁ (t, 0) - model v (t, 0)) =
      StripCoordinates.center t
  rw [hterm₀, hterm₁, add_zero, add_zero, model_zero]

theorem StripCoordinates.blend_eq_left {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 1)
    (h₁ : β₁ p.1 = 0) : blend v F₀ F₁ β₀ β₁ p = F₀ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem StripCoordinates.blend_eq_right {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 0)
    (h₁ : β₁ p.1 = 1) : blend v F₀ F₁ β₀ β₁ p = F₁ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem StripCoordinates.normalDerivative_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (h₀ : ∀ t, β₀ t ≠ 0 → normalDerivative F₀ t = v t)
    (h₁ : ∀ t, β₁ t ≠ 0 → normalDerivative F₁ t = v t) (t : ℝ) :
    normalDerivative (blend v F₀ F₁ β₀ β₁) t = v t := by
  have hm : HasDerivAt (fun s : ℝ => s • v t) (v t) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v t)
  have hd₀ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₀.snd.contDiffAt.differentiableAt (by simp))
  have hd₁ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₁.snd.contDiffAt.differentiableAt (by simp))
  have hterm₀ : β₀ t • (normalDerivative F₀ t - v t) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, sub_self, smul_zero]
  have hterm₁ : β₁ t • (normalDerivative F₁ t - v t) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, sub_self, smul_zero]
  have hblend :
    HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2)
      (v t + β₀ t • (normalDerivative F₀ t - v t) + β₁ t • (normalDerivative F₁ t - v t)) 0 :=
    HasDerivAt.add (HasDerivAt.add hm (HasDerivAt.const_smul (β₀ t) (HasDerivAt.sub hd₀ hm)))
      (HasDerivAt.const_smul (β₁ t) (HasDerivAt.sub hd₁ hm))
  have hblend' : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2) (v t) 0 := by
    simpa only [hterm₀, hterm₁, add_zero] using hblend
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_blend hv hF₀ hF₁ hβ₀ hβ₁).snd.contDiffAt.differentiableAt (by simp))).unique
      hblend'

structure StripNormalData (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (S : Set M) (k : (ℝ × ℝ) → M) where
  chart :
    PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M ∞
  line : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) chart.source
  sheet : ∀ q ∈ chart.source, chart q ∈ S ↔ q.2 = 0
  center : ∀ t, k (t, 0) = chart (StripCoordinates.center t)
  normal_nonzero :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (TransverseCoordinates.normalCoordinate chart ∘ k) (t, 0) (0, 1) ≠ 0

theorem StripCoordinates.horizontal_derivative_of_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : ∀ s, F (s, 0) = StripCoordinates.center s) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have heq : (fun s : ℝ => F (s, 0)) = StripCoordinates.center := funext hc
  rw [heq] at hd
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique hcenter

theorem StripCoordinates.horizontal_derivative_of_center_germ {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : (fun s : ℝ => F (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique (hcenter.congr_of_eventuallyEq hc)

theorem StripCoordinates.normalDerivative_eq_snd_fderiv {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) : normalDerivative F t = (fderiv ℝ F (t, 0) (0, 1)).2 := by
  have hd := hF.hasFDerivAt.snd
  rw [normalDerivative, hd.fderiv]
  rfl

theorem StripCoordinates.injective_of_horizontal_and_normal {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : (ℝ × ℝ) →L[ℝ] Space A B) (hh : L (1, 0) = StripCoordinates.center 1)
    (hn : (L (0, 1)).2 ≠ 0) : Function.Injective L := by
  have hker : ∀ p : ℝ × ℝ, L p = 0 → p = 0 := by
    rintro ⟨a, b⟩ hp
    have hsplit : (a, b) = a • ((1 : ℝ), 0) + b • (0, 1) := by ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hh] at hp
    have hb0 : b • (L (0, 1)).2 = 0 := by
      simpa [StripCoordinates.center] using congrArg Prod.snd hp
    have hb : b = 0 := (smul_eq_zero.mp hb0).resolve_right hn
    subst b
    have ha : a = 0 := by
      simpa [StripCoordinates.center] using congrArg (fun q : Space A B => q.1.1) hp
    subst a
    rfl
  intro p q hpq
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hpq, sub_self]

theorem StripCoordinates.injective_fderiv_at_center {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = StripCoordinates.center s)
    (hn : normalDerivative F t ≠ 0) : Function.Injective (fderiv ℝ F (t, 0)) := by
  apply
    injective_of_horizontal_and_normal (fderiv ℝ F (t, 0)) (horizontal_derivative_of_center hF hc)
  rwa [← normalDerivative_eq_snd_fderiv hF]

def StripCoordinates.sheetTransverseInclusion {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] : A →L[ℝ] Space A B :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)

theorem StripCoordinates.sheetTransverseInclusion_apply {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (a : A) :
    (sheetTransverseInclusion : A →L[ℝ] Space A B) a = ((0, a), 0) :=
  rfl

theorem StripCoordinates.sheetTransverse_eq_strip_iff {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0) (a : A)
    (p : ℝ × ℝ) : sheetTransverseInclusion a = L p ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro heq
    have hsplit : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
    have hexp : L p = p.1 • StripCoordinates.center 1 + p.2 • L (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hh]
    rw [hexp] at heq
    have hp2zero : p.2 • (L (0, 1)).2 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg Prod.snd heq).symm
    have hp2 : p.2 = 0 := (smul_eq_zero.mp hp2zero).resolve_right hn
    rw [hp2, zero_smul, add_zero] at heq
    have hp1 : p.1 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg (fun q : Space A B => q.1.1) heq).symm
    have ha : a = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.2) heq
    exact ⟨ha, Prod.ext hp1 hp2⟩
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

theorem StripCoordinates.injective_sheetTransverse_normalQuotient {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : Space A B →L[ℝ] Z)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0)
    (hker : Q.ker = L.range) : Function.Injective (Q.comp sheetTransverseInclusion) := by
  have hz : ∀ a : A, Q (sheetTransverseInclusion a) = 0 → a = 0 := by
    intro a ha
    have hmem : sheetTransverseInclusion a ∈ L.range := by
      rw [← hker]
      exact ha
    obtain ⟨p, hp⟩ := hmem
    exact ((sheetTransverse_eq_strip_iff L hh hn a p).mp hp.symm).1
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change (Q.comp sheetTransverseInclusion) (a - b) = 0
  rw [map_sub, hab, sub_self]

theorem StripCoordinates.ker_comp_eq_range_of_injective {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Space A B →L[ℝ] V) (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : V →L[ℝ] Z)
    (hT : Function.Injective T) (hker : Q.ker = (T.comp L).range) : (Q.comp T).ker = L.range := by
  ext v
  constructor
  · intro hv
    have hmem : T v ∈ (T.comp L).range := by
      rw [← hker]
      exact hv
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hT hp⟩
  · rintro ⟨p, rfl⟩
    have hmem : T (L p) ∈ Q.ker := by
      rw [hker]
      exact ⟨p, rfl⟩
    exact hmem

def StripNormalData.coordinateMap {A B E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) : (ℝ × ℝ) → StripCoordinates.Space A B :=
  d.chart.symm ∘ k

theorem StripNormalData.center_mem_target {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    k (t, 0) ∈ d.chart.target := by
  rw [d.center t]
  exact d.chart.map_source' (d.line ht)

theorem StripNormalData.coordinate_center_germ {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.coordinateMap (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds
      (d.chart.open_source.mem_nhds (d.line ht))] with
    s hs
  change d.chart.invFun (k (s, 0)) = StripCoordinates.center s
  rw [d.center s, d.chart.left_inv' hs]

theorem StripNormalData.coordinate_center {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.coordinateMap (t, 0) = StripCoordinates.center t :=
  (d.coordinate_center_germ ht).eq_of_nhds

theorem StripNormalData.contDiffAt_coordinateMap {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) : ContDiffAt ℝ ∞ d.coordinateMap (t, 0) :=
  ((d.chart.contMDiffOn_invFun.contMDiffAt
          (d.chart.open_target.mem_nhds (d.center_mem_target ht))).comp
      (t, 0) hk).contDiffAt

theorem StripNormalData.horizontal_coordinateDerivative {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    fderiv ℝ d.coordinateMap (t, 0) (1, 0) = StripCoordinates.center 1 :=
  StripCoordinates.horizontal_derivative_of_center_germ
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp)) (d.coordinate_center_germ ht)

theorem StripNormalData.normal_coordinateDerivative_nonzero {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    (fderiv ℝ d.coordinateMap (t, 0) (0, 1)).2 ≠ 0 := by
  rw [←
    StripCoordinates.normalDerivative_eq_snd_fderiv
      ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp))]
  exact d.normal_nonzero t ht

theorem StripNormalData.native_derivative_factor {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0) =
      (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
            (StripCoordinates.center t)).comp
        (fderiv ℝ d.coordinateMap (t, 0)) := by
  have hcoords := d.contDiffAt_coordinateMap ht hk
  have heq : (d.chart ∘ d.coordinateMap) =ᶠ[𝓝 (t, 0)] k := by
    filter_upwards [hk.continuousAt.preimage_mem_nhds
        (d.chart.open_target.mem_nhds (d.center_mem_target ht))] with
      p hp
    change d.chart (d.chart.invFun (k p)) = k p
    exact d.chart.right_inv' hp
  have hcsource : d.coordinateMap (t, 0) ∈ d.chart.source := by
    rw [d.coordinate_center ht]
    exact d.line ht
  rw [← heq.mfderiv_eq,
    mfderiv_comp (t, 0) (d.chart.mdifferentiableAt (by simp) hcsource)
      (hcoords.contMDiffAt.mdifferentiableAt (by simp)),
    d.coordinate_center ht, mfderiv_eq_fderiv]
  rfl

theorem TransverseCoordinates.mfderiv_zero_section {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)).comp (ContinuousLinearMap.inl ℝ D B) := by
  have heq : f = Φ ∘ (ContinuousLinearMap.inl ℝ D B) := funext (fun y => (hzero y).symm)
  have hinl : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, D × B) ∞ (ContinuousLinearMap.inl ℝ D B) :=
    (ContinuousLinearMap.inl ℝ D B).contDiff.contMDiff
  rw [heq, mfderiv_comp x (Φ.mdifferentiableAt (by simp) hx) (hinl.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (ContinuousLinearMap.inl ℝ D B).fderiv]
  rfl

theorem TransverseCoordinates.ker_normalDerivative_eq_range_zero_section {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x)).ker =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).range := by
  let L : (D × B) →L[ℝ] E := mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)
  let R : E →L[ℝ] (D × B) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (Φ (x, 0))
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, D × B) 𝓘(ℝ, E) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hRL : R.comp L = ContinuousLinearMap.id ℝ (D × B) := hdiff.symm_comp_deriv hx
  have hRL_apply (q : D × B) : R (L q) = q := by
    change (R.comp L) q = q
    rw [hRL]
    rfl
  have hsurj : Function.Surjective L := (PartialChart.bijective_mfderiv Φ hx).2
  have hnormal :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x) = (ContinuousLinearMap.snd ℝ D B).comp R :=
    by
    rw [← hzero x, mfderiv_normalCoordinate Φ (Φ.map_source' hx)]
    rfl
  rw [hnormal, mfderiv_zero_section Φ hzero hx]
  ext v
  constructor
  · intro hv
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj v
    have hb : b = 0 := by
      change (R v).2 = 0 at hv
      rw [← hab, hRL_apply] at hv
      exact hv
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨a, rfl⟩
    change (R (L (a, 0))).2 = 0
    rw [hRL_apply]

def StripNormalData.normalFrame {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) : A →L[ℝ] Z :=
  (fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t)).comp
    StripCoordinates.sheetTransverseInclusion

theorem StripNormalData.contDiffOn_normalFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.normalFrame Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds ht.2)
  have hchart := d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1)
  have htransition :
    ContDiffAt ℝ ∞ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
      (StripCoordinates.center t) :=
    (hnormal.comp (StripCoordinates.center t) hchart).contDiffAt
  have hcenter :
    ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact
    (((htransition.fderiv_right (by simp)).comp t hcenter.contDiffAt).clm_comp
        contDiffAt_const).contDiffWithinAt

theorem StripNormalData.exists_open_normalFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame Ψ) U := by
  have hcenter :
    Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hW : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  refine
    ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target),
      hW.preimage hcenter, fun t ht => ⟨d.line ht, htarget t ht⟩, ?_⟩
  exact d.contDiffOn_normalFrame Ψ

theorem StripNormalData.injective_normalFrame_of_strip_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ x, Ψ (x, 0) = f x) {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p) (hcp : c p = (t, 0))
    (hcs : Function.Surjective (fderiv ℝ c p)) (hgerm : f =ᶠ[𝓝 p] k ∘ c) :
    Function.Injective (d.normalFrame Ψ t) := by
  let T : StripCoordinates.Space A B →L[ℝ] E :=
    mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
      (StripCoordinates.center t)
  let L : (ℝ × ℝ) →L[ℝ] StripCoordinates.Space A B := fderiv ℝ d.coordinateMap (t, 0)
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p)
  let J : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p
  let K : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)
  have hfp : f p = d.chart (StripCoordinates.center t) := by
    have heq := hgerm.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcp, d.center t] at heq
    exact heq
  have htarget : f p ∈ Ψ.target := by
    have h := Ψ.map_source' hp
    rwa [hzero p] at h
  have hk' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (c p) := by
    rw [hcp]
    exact hk
  have hdf :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).comp (fderiv ℝ c p) := by
    rw [hgerm.mfderiv_eq,
      mfderiv_comp p (hk'.mdifferentiableAt (by simp))
        (hc.contMDiffAt.mdifferentiableAt (by simp)),
      hcp, mfderiv_eq_fderiv]
    rfl
  have hker : Q.ker = (T.comp L).range := by
    have h1 : Q.ker = J.range :=
      TransverseCoordinates.ker_normalDerivative_eq_range_zero_section Ψ hzero hp
    have h2 : J.range = K.range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p).range = K.range
      rw [hdf]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hcs)
    have h3 : K.range = (T.comp L).range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).range = (T.comp L).range
      rw [d.native_derivative_factor ht hk]
      rfl
    exact h1.trans (h2.trans h3)
  have hT : Function.Injective T := (PartialChart.bijective_mfderiv d.chart (d.line ht)).1
  have hinj :
    Function.Injective ((Q.comp T).comp StripCoordinates.sheetTransverseInclusion) :=
    StripCoordinates.injective_sheetTransverse_normalQuotient L (Q.comp T)
      (d.horizontal_coordinateDerivative ht hk) (d.normal_coordinateDerivative_nonzero ht hk)
      (StripCoordinates.ker_comp_eq_range_of_injective T L Q hT hker)
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds htarget)
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Z) ∞ (TransverseCoordinates.normalCoordinate Ψ)
      (d.chart (StripCoordinates.center t)) := by
    rw [← hfp]
    exact hnormal
  have htransition :
    fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t) =
      Q.comp T := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (StripCoordinates.center t) (hnormal'.mdifferentiableAt (by simp))
        (d.chart.mdifferentiableAt (by simp) (d.line ht))]
    rw [← hfp]
    rfl
  change
    Function.Injective
      ((fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
            (StripCoordinates.center t)).comp
        StripCoordinates.sheetTransverseInclusion)
  rw [htransition]
  exact hinj

def StripNormalData.sheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  (Ψ.symm ∘ d.chart) ∘ (ContinuousLinearMap.inl ℝ (ℝ × A) B)

def StripNormalData.sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    (ℝ × A) →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (d.sheetTransition Ψ) (t, 0)

theorem StripNormalData.contDiffAt_tubularTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
  ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)).comp
      (StripCoordinates.center t)
      (d.chart.contMDiffOn_toFun.contMDiffAt
        (d.chart.open_source.mem_nhds (d.line ht)))).contDiffAt

theorem StripNormalData.contDiffAt_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
  (d.contDiffAt_tubularTransition Ψ ht htarget).comp (t, 0)
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt

theorem StripNormalData.sheetDifferential_eq {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    d.sheetDifferential Ψ t =
      (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)).comp
        (ContinuousLinearMap.inl ℝ (ℝ × A) B) := by
  rw [sheetDifferential, sheetTransition,
    fderiv_comp (t, 0) ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp))
      (ContinuousLinearMap.inl ℝ (ℝ × A) B).differentiableAt,
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).fderiv]
  rfl

theorem StripNormalData.normal_sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A)) =
      d.normalFrame Ψ t := by
  have hn :
    fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t) =
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)) := by
    change
      fderiv ℝ ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z) ∘ (Ψ.symm ∘ d.chart))
          (StripCoordinates.center t) =
        _
    rw [fderiv_comp _ (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).differentiableAt
        ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp)),
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).fderiv]
  rw [d.sheetDifferential_eq Ψ ht htarget, normalFrame, hn]
  rfl

theorem StripNormalData.sheetTransition_center_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {f : (ℝ × ℝ) → M}
    (hzero : ∀ p, Ψ (p, 0) = f p) {q : ℝ → (ℝ × ℝ)} {t : ℝ} (hq : ContinuousAt q t)
    (hp : (q t, 0) ∈ Ψ.source) {c : (ℝ × ℝ) → (ℝ × ℝ)} (hcq : ∀ s, c (q s) = (s, 0))
    (hgerm : f =ᶠ[𝓝 (q t)] k ∘ c) :
    (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0) := by
  have hs := (hq.prodMk continuousAt_const).preimage_mem_nhds (Ψ.open_source.mem_nhds hp)
  filter_upwards [hs, hgerm.comp_tendsto hq.tendsto] with s hsource heq
  dsimp only [Function.comp_apply] at heq
  rw [hcq s] at heq
  change Ψ.invFun (d.chart (StripCoordinates.center s)) = (q s, 0)
  rw [← d.center s, ← heq, ← hzero (q s)]
  exact Ψ.left_inv' hsource

theorem StripNormalData.sheetDifferential_arc_of_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    {q : ℝ → (ℝ × ℝ)} {v : ℝ × ℝ} (hq : HasDerivAt q v t)
    (hgerm : (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0)) :
    d.sheetDifferential Ψ t (1, 0) = (v, 0) := by
  have hF := (d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)
  have hi : HasDerivAt (fun s : ℝ => (s, (0 : A))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hi
  have hq' : HasDerivAt (fun s => (q s, (0 : Z))) (v, 0) t :=
    hq.prodMk (hasDerivAt_const t (0 : Z))
  exact hd.unique (hq'.congr_of_eventuallyEq hgerm)

def TransverseCoordinates.cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) :
    (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

theorem TransverseCoordinates.cornerLinear_apply {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) :=
  rfl

theorem TransverseCoordinates.injective_cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Function.Injective (cornerLinear u v) := by
  intro p q hpq
  exact
    Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
      ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

def TransverseCoordinates.cornerMap {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) : (ℝ × ℝ) → M :=
  Φ ∘ cornerLinear u v

theorem TransverseCoordinates.contMDiffOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

theorem TransverseCoordinates.injOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Set.InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

theorem TransverseCoordinates.injective_mfderiv_cornerMap {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap,
    mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp) (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

theorem exists_native_clean_corner_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (c 0) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (c (s • u))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (d (t • v))) := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy hdim ht hO
      hxO
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  refine
    ⟨W, Φ.open_source.preimage L.continuous, h0W, k,
      TransverseCoordinates.contMDiffOn_cornerMap Φ u v,
      TransverseCoordinates.injOn_cornerMap Φ hu hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · change Φ (L 0) = F (c 0)
    rw [map_zero]
    exact hcenter
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using him
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at ht
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

structure CleanCornerPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) where
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_zero : (0 : ℝ × ℝ) ∈ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  sheets : ∀ p ∈ domain, (map p ∈ S ↔ p.2 = 0) ∧ (map p ∈ T ↔ p.1 = 0)
  axis_first : ∀ t, (t, 0) ∈ domain → map (t, 0) = a t
  axis_second : ∀ t, (0, t) ∈ domain → map (0, t) = b t

def CleanCornerPatch.swap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    (c : CleanCornerPatch (E := E) S T a b) : CleanCornerPatch (E := E) T S b a := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e : (ℝ × ℝ) → ℝ × ℝ) := e.contDiff.contMDiff
  refine
    { domain := e ⁻¹' c.domain
      open_domain := c.open_domain.preimage e.continuous
      contains_zero := ?_
      map := c.map ∘ e
      smooth := c.smooth.comp he.contMDiffOn (fun _ hp => hp)
      injective := ?_
      derivative_injective := ?_
      sheets := fun p hp => ⟨(c.sheets (e p) hp).2, (c.sheets (e p) hp).1⟩
      axis_first := fun t ht => c.axis_second t ht
      axis_second := fun t ht => c.axis_first t ht }
  · change e 0 ∈ c.domain
    rw [map_zero]
    exact c.contains_zero
  · intro p hp q hq hpq
    exact e.injective (c.injective hp hq hpq)
  · intro p hp
    have hc := c.smooth.contMDiffAt (c.open_domain.mem_nhds hp)
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact
      (c.derivative_injective (e p) hp).comp
        (PartialChart.bijective_mfderiv e.toDiffeomorph.toPartialDiffeomorph
            (Set.mem_univ p)).1

structure CleanStripPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a : ℝ → M) (k₀ k₁ : (ℝ × ℝ) → M) where
  width : ℝ
  width_pos : 0 < width
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_strip : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width ⊆ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  closed_embedding :
    Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width => map p)
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  first_sheet : ∀ p ∈ domain, map p ∈ S ↔ p.2 = 0
  second_sheet : ∀ p ∈ domain, map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1
  center : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (t, 0) = a t
  left_germ : map =ᶠ[𝓝 (0, 0)] k₀
  right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse

theorem bigon_strip_maps_left_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (-1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 0 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 0 using 1
    norm_num
  have hk :=
    k.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hx]
        exact (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt)
  have hl :=
    l.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hy]
        exact (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt)
  have hnear : ∀ᶠ p in 𝓝 ((-1 : ℝ), (0 : ℝ)), WhitneyPairModel.arcTime p ≤ 1 / 3 := by
    have ht : WhitneyPairModel.arcTime (-1, 0) < 1 / 3 := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_lt_const ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp, WhitneyPairModel.lowerStripCoordinates_left h hp,
    WhitneyPairModel.upperStripCoordinates_left hh hp]
  change
    c₀.map (WhitneyPairModel.leftCornerCoordinates h p) =
      c₀.map ((WhitneyPairModel.leftCornerCoordinates h p).swap.swap)
  rw [Prod.swap_swap]

theorem bigon_strip_maps_right_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 1 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 1 using 1
    norm_num
  have hk :=
    k.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hx] at ht
        exact ht)
  have hl :=
    l.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hy] at ht
        exact ht)
  have hnear : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 2 / 3 ≤ WhitneyPairModel.arcTime p := by
    have ht : 2 / 3 < WhitneyPairModel.arcTime (1, 0) := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_const_lt ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp]
  change
    c₁.map (StripCoordinates.reverse (WhitneyPairModel.lowerStripCoordinates h p)) =
      c₁.map ((StripCoordinates.reverse (WhitneyPairModel.upperStripCoordinates h p)).swap)
  rw [WhitneyPairModel.lowerStripCoordinates_right h hp,
    WhitneyPairModel.upperStripCoordinates_right hh hp, Prod.swap_swap]

theorem exists_smooth_open_gluing {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y] [ChartedSpace F Y] {f g : X → Y} {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g V) (hfg : Set.EqOn f g (U ∩ V)) :
    ∃ k : X → Y, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k (U ∪ V) ∧ Set.EqOn k f U ∧ Set.EqOn k g V := by
  classical
  let k := U.piecewise f g
  have hkf : Set.EqOn k f U := fun x hx => Set.piecewise_eq_of_mem U f g hx
  have hkg : Set.EqOn k g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hkf hxU).trans (hfg ⟨hxU, hx⟩)
    · exact Set.piecewise_eq_of_notMem U f g hxU
  exact
    ⟨k, (hf.congr (fun _ hx => hkf hx)).union_of_isOpen (hg.congr (fun _ hx => hkg hx)) hU hV,
      hkf, hkg⟩

theorem exists_smooth_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                  Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain ∧
                    Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain ∧
                      ∃ f : (ℝ × ℝ) → M,
                        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V) ∧
                          Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U ∧
                            Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                  f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) := by
  let Dlo := WhitneyPairModel.lowerStripCoordinates h ⁻¹' k.domain
  let Dhi := WhitneyPairModel.upperStripCoordinates h ⁻¹' l.domain
  have hDlo : IsOpen Dlo :=
    k.open_domain.preimage (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').continuous
  have hDhi : IsOpen Dhi :=
    l.open_domain.preimage (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').continuous
  have hkl :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) Dlo :=
    k.smooth.comp (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  have hlu :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (l.map ∘ WhitneyPairModel.upperStripCoordinates h) Dhi :=
    l.smooth.comp (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp (bigon_strip_maps_left_germ hh.ne' c₀ c₁ k l)
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_right_germ hh.ne' c₀ c₁ k l)
  have hlowD : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) Dlo := by
    intro t ht
    change WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0) ∈ k.domain
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have huppD :
    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) Dhi := by
    intro t ht
    change
      WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ l.domain
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  obtain ⟨U, V, hU, hV, hUD, hVD, hover, hlowU, huppV, hfront⟩ :=
    WhitneyPairModel.exists_bigon_boundary_cover hh hDlo hDhi (hO₀.union hO₁) (Or.inl hleft)
      (Or.inr hright) hlowD huppD
  have hfg :
    Set.EqOn (k.map ∘ WhitneyPairModel.lowerStripCoordinates h)
      (l.map ∘ WhitneyPairModel.upperStripCoordinates h) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨f, hf, hflo, hfhi⟩ := exists_smooth_open_gluing hU hV (hkl.mono hUD) (hlu.mono hVD) hfg
  refine
    ⟨U, V, hU, hV, hfront, hlowU, huppV, fun _ hp => hUD hp, fun _ hp => hVD hp, f, hf, hflo,
      hfhi, ?_, ?_⟩
  · intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  · intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht

theorem StripCoordinates.injective_plane_of_horizontal_and_normal
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hh : L (1, 0) = (1, 0)) (hn : (L (0, 1)).2 ≠ 0) :
    Function.Injective L := by
  let i : (ℝ × ℝ) →L[ℝ] Space ℝ ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hh' : (i.comp L) (1, 0) = StripCoordinates.center 1 := by
    change i (L (1, 0)) = StripCoordinates.center 1
    rw [hh]
    rfl
  have hi := injective_of_horizontal_and_normal (i.comp L) hh' hn
  intro p q hpq
  exact hi (congrArg i hpq)

def StripCoordinates.detector {A B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (v : ℝ → B) (F : (ℝ × ℝ) → Space A B) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪v p.1, (F p).2⟫_ℝ)

theorem StripCoordinates.contDiff_detector {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (detector v F) :=
  contDiff_fst.prodMk ((hv.comp contDiff_fst).inner ℝ hF.snd)

theorem StripCoordinates.detector_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (t : ℝ) :
    detector v F (t, 0) = (t, 0) := by
  simp only [detector, hc, StripCoordinates.center, inner_zero_right]

theorem StripCoordinates.detector_vertical_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hn : ∀ t, normalDerivative F t = v t) (t : ℝ) :
    fderiv ℝ (detector v F) (t, 0) (0, 1) = (0, ⟪v t, v t⟫_ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => (F (t, s)).2) (v t) 0 := by
    have h :=
      hasDerivAt_verticalSlice (t := t) (s := 0) (hF.snd.contDiffAt.differentiableAt (by simp))
    change HasDerivAt _ (normalDerivative F t) 0 at h
    rwa [hn t] at h
  have hinner : HasDerivAt (fun s : ℝ => ⟪v t, (F (t, s)).2⟫_ℝ) (⟪v t, v t⟫_ℝ) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (v t)).inner ℝ hd
  have hslice : HasDerivAt (fun s : ℝ => detector v F (t, s)) (0, ⟪v t, v t⟫_ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk hinner
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_detector hv hF).contDiffAt.differentiableAt (by simp))).unique
      hslice

theorem StripCoordinates.injective_fderiv_detector_at_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    {v : ℝ → B} {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (hn : ∀ t, normalDerivative F t = v t)
    {t : ℝ} (ht : v t ≠ 0) : Function.Injective (fderiv ℝ (detector v F) (t, 0)) := by
  have hQ : DifferentiableAt ℝ (detector v F) (t, 0) :=
    (contDiff_detector hv hF).contDiffAt.differentiableAt (by simp)
  have hh : fderiv ℝ (detector v F) (t, 0) (1, 0) = (1, 0) := by
    have hd := hasDerivAt_horizontalSlice hQ
    have heq : (fun s : ℝ => detector v F (s, 0)) = fun s => (s, 0) := funext (detector_zero hc)
    rw [heq] at hd
    exact hd.unique ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
  apply injective_plane_of_horizontal_and_normal _ hh
  rw [detector_vertical_derivative hv hF hn t]
  exact inner_self_ne_zero.mpr ht

theorem WhitneyPairModel.lowerStripCoordinates_horizontal_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0) = (1 / 2, 0) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_horizontalSlice hf
  have heq : (fun x : ℝ => lowerStripCoordinates h (x, 0)) = fun x => ((x + 1) / 2, 0) := by
    funext x
    simp [lowerStripCoordinates, arcTime]
  rw [heq] at hd
  exact
    hd.unique (((hasDerivAt_id s).add_const 1).div_const 2 |>.prodMk (hasDerivAt_const s (0 : ℝ)))

theorem WhitneyPairModel.lowerStripCoordinates_vertical_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1) =
      (cornerSign ((s + 1) / 2) * (1 / (4 * h * cornerScale ((s + 1) / 2))),
        1 / (4 * h * cornerScale ((s + 1) / 2))) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_verticalSlice hf
  have hdiv :
    HasDerivAt (fun u : ℝ => u / (4 * h * cornerScale ((s + 1) / 2)))
      (1 / (4 * h * cornerScale ((s + 1) / 2))) 0 :=
    (hasDerivAt_id 0).div_const _
  have hfirst := (HasDerivAt.const_mul (cornerSign ((s + 1) / 2)) hdiv).const_add ((s + 1) / 2)
  exact hd.unique (hfirst.prodMk hdiv)

theorem WhitneyPairModel.injective_fderiv_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (lowerStripCoordinates h) (s, 0)) := by
  let L := fderiv ℝ (lowerStripCoordinates h) (s, 0)
  have hhor : ((2 : ℝ) • L) (1, 0) = (1, 0) := by
    change (2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0)) = (1, 0)
    rw [lowerStripCoordinates_horizontal_derivative hh]
    norm_num
  have hnorm : (((2 : ℝ) • L) (0, 1)).2 ≠ 0 := by
    change ((2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1))).2 ≠ 0
    rw [lowerStripCoordinates_vertical_derivative hh]
    change (2 : ℝ) * (1 / (4 * h * cornerScale ((s + 1) / 2))) ≠ 0
    exact
      mul_ne_zero (by norm_num)
        (one_div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne'))
  have hi :=
    StripCoordinates.injective_plane_of_horizontal_and_normal ((2 : ℝ) • L) hhor hnorm
  intro x y hxy
  exact hi (congrArg (fun z : ℝ × ℝ => (2 : ℝ) • z) hxy)

theorem WhitneyPairModel.injective_fderiv_exchangeEdges (h : ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (exchangeEdges h) p) := by
  have heq : exchangeEdges h ∘ exchangeEdges h = id := funext (exchangeEdges_involutive h)
  have hd :
    (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [←
      fderiv_comp p ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))
        ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp)),
      heq, fderiv_id]
  intro x y hxy
  have he := congrArg (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)) hxy
  change
    ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p)) x =
      ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p))
        y at he
  rw [hd] at he
  exact he

theorem WhitneyPairModel.injective_fderiv_upperStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (upperStripCoordinates h) (s, h * (1 - s ^ 2))) := by
  rw [upperStripCoordinates,
    fderiv_comp _ ((contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp))
      ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))]
  have heq : exchangeEdges h (s, h * (1 - s ^ 2)) = (s, 0) := by
    simp only [exchangeEdges, sub_self]
  rw [heq]
  exact (injective_fderiv_lowerStripCoordinates hh s).comp (injective_fderiv_exchangeEdges h _)

theorem WhitneyPairModel.mem_frontier_bigon_iff_exists_time {h : ℝ} (hh : 0 < h)
    (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (2 * t - 1, 0) ∨ p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
  constructor
  · intro hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    refine ⟨t, ht, ?_⟩
    rcases hpedge with hpzero | hpupper
    · exact Or.inl (Prod.ext hbase hpzero)
    · right
      apply Prod.ext hbase
      rw [← hbase]
      exact hpupper
  · rintro ⟨t, ht, rfl | rfl⟩
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨lowerArc_mem_bigon hh.le ?_, Or.inl rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨upperArc_mem_bigon hh.le ?_, Or.inr rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]

theorem WhitneyPairModel.injOn_frontier_bigon_of_arcs {M : Type*} {h : ℝ} (hh : 0 < h)
    {f : (ℝ × ℝ) → M} {a b : ℝ → M} (ha : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hb : Set.InjOn b (Set.Icc (0 : ℝ) 1))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    Set.InjOn f (frontier (bigon h)) := by
  have hcross {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : a t = b s) : (2 * t - 1, (0 : ℝ)) = (2 * s - 1, h * (1 - (2 * s - 1) ^ 2)) := by
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro p hp q hq heq
  obtain ⟨t, ht, hp'⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  obtain ⟨s, hs, hq'⟩ := (mem_frontier_bigon_iff_exists_time hh q).mp hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · rw [hlower t ht, hlower s hs] at heq
    rw [ha ht hs heq]
  · rw [hlower t ht, hupper s hs] at heq
    exact hcross ht hs heq
  · rw [hupper t ht, hlower s hs] at heq
    exact (hcross hs ht heq.symm).symm
  · rw [hupper t ht, hupper s hs] at heq
    rw [hb ht hs heq]

theorem CleanStripPatch.center_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  have h0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have htK : (t, 0) ∈ k.domain := k.contains_strip ⟨ht, h0⟩
  have hsK : (s, 0) ∈ k.domain := k.contains_strip ⟨hs, h0⟩
  have hmaps : k.map (t, 0) = k.map (s, 0) := by
    rw [k.center t ht, k.center s hs]
    exact heq
  exact congrArg Prod.fst (k.injective htK hsK hmaps)

theorem strip_center_coincidences_of_corner_overlap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  intro t ht s hs heq
  have hk0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hl0 : (0 : ℝ) ∈ Set.Icc (-l.width) l.width :=
    ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hmaps : k.map (t, 0) = l.map (s, 0) := by rw [k.center t ht, l.center s hs]; exact heq
  rcases hover (t, 0) (k.contains_strip ⟨ht, hk0⟩) (s, 0) (l.contains_strip ⟨hs, hl0⟩) hmaps with
    hleft | hright
  · exact Or.inl ⟨congrArg Prod.fst hleft, (congrArg Prod.snd hleft).symm⟩
  · right
    have ht' : 1 - t = 0 := congrArg Prod.fst hright
    have hs' : 0 = 1 - s := congrArg Prod.snd hright
    constructor <;> linarith

theorem injective_nativeDerivative_of_strip_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {r : (ℝ × ℝ) → ℝ × ℝ}
    (hr : ContDiff ℝ ∞ r) {f : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (heq : Set.EqOn f (k.map ∘ r) U) (hmap : Set.MapsTo r U k.domain) {p : ℝ × ℝ} (hp : p ∈ U)
    (hi : Function.Injective (fderiv ℝ r p)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hgerm : f =ᶠ[𝓝 p] k.map ∘ r := Filter.mem_of_superset (hU.mem_nhds hp) (fun _ hx => heq hx)
  rw [hgerm.mfderiv_eq]
  have hk := k.smooth.contMDiffAt (k.open_domain.mem_nhds (hmap hp))
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp)) (hr.contMDiff.mdifferentiableAt (by simp))]
  have hri : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r p) := by
    rw [mfderiv_eq_fderiv]
    exact hi
  exact (k.derivative_injective (r p) (hmap hp)).comp hri

theorem injective_nativeDerivative_bigon_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∀ p ∈ frontier (WhitneyPairModel.bigon h),
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  intro p hp
  obtain ⟨t, ht, rfl | rfl⟩ := (WhitneyPairModel.mem_frontier_bigon_iff_exists_time hh p).mp hp
  · exact
      injective_nativeDerivative_of_strip_germ k
        (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne') hU hflo hmapU (hlowU ht)
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates hh.ne' _)
  · exact
      injective_nativeDerivative_of_strip_germ l
        (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne') hV hfhi hmapV (huppV ht)
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates hh.ne' _)

theorem exists_embedded_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hfront : frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V))
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
          W ⊆ U ∪ V ∧
            Set.InjOn f W ∧ ∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t := by
    intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  have hupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t := by
    intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht
  have hinj :=
    WhitneyPairModel.injOn_frontier_bigon_of_arcs hh k.center_injOn l.center_injOn hlow hupp
      (strip_center_coincidences_of_corner_overlap k l hover)
  have hi :=
    injective_nativeDerivative_bigon_boundary hh k l hU hV hlowU huppV hmapU hmapV hflo hfhi
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  exact
    ManifoldImmersion.exists_open_embedded_immersive_neighborhood (hU.union hV) hf hcompact hfront
      hinj hi

theorem WhitneyPairModel.interpolated_strip_time_mem_Ioo {h t β z J : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 < J)
    (hJdef : J = (1 - β) * (1 - t) + β * t) (hz : 0 < z) (hzupper : z < 4 * h * t * (1 - t)) :
    t + (2 * β - 1) * (z / (4 * h * J)) ∈ Set.Ioo (0 : ℝ) 1 := by
  let H := 4 * h * t * (1 - t)
  have hH : 0 < H := mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
  let θ := z / H
  let e := t * β / J
  have hθ0 : 0 < θ := div_pos hz hH
  have hθ1 : θ < 1 := (div_lt_one hH).mpr hzupper
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg ht.1.le hβ.1) hJ.le
  have he1 : e ≤ 1 := by
    apply (div_le_one hJ).mpr
    rw [hJdef]
    have hr := mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr ht.2.le)
    nlinarith
  have hid : t + (2 * β - 1) * (z / (4 * h * J)) = (1 - θ) * t + θ * e := by
    dsimp [θ, e, H]
    field_simp [hh.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', hJ.ne']
    rw [hJdef]
    ring
  rw [hid]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) ht.1) (mul_nonneg hθ0.le he0)
  · have hpos : 0 < (1 - θ) * (1 - t) + θ * (1 - e) :=
      add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht.2))
        (mul_nonneg hθ0.le (sub_nonneg.mpr he1))
    nlinarith

theorem WhitneyPairModel.lowerStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (lowerStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (lowerStripCoordinates h p).2 := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  have hheight : 0 < h * (1 - p.1 ^ 2) := hp0.trans hphi
  have hsq : p.1 ^ 2 < 1 := by
    have hpos : 0 < 1 - p.1 ^ 2 := (mul_pos_iff_of_pos_left hh).mp hheight
    linarith
  have ht : arcTime p ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [arcTime]
    constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  have hβ : cornerTransition (arcTime p) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hheight_eq : h * (1 - p.1 ^ 2) = 4 * h * arcTime p * (1 - arcTime p) := by
    dsimp [arcTime]
    ring
  have hzupper : p.2 < 4 * h * arcTime p * (1 - arcTime p) := hheight_eq ▸ hphi
  refine ⟨?_, ?_⟩
  · exact interpolated_strip_time_mem_Ioo hh ht hβ (cornerScale_pos _) rfl hp0 hzupper
  · exact div_pos hp0 (mul_pos (mul_pos (by norm_num) hh) (cornerScale_pos _))

theorem WhitneyPairModel.exchangeEdges_mem_interior {h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) : exchangeEdges h p ∈ interior (bigon h) := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h * (1 - p.1 ^ 2) - p.2 ∧ h * (1 - p.1 ^ 2) - p.2 < h * (1 - p.1 ^ 2)
  constructor <;> linarith

theorem WhitneyPairModel.upperStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (upperStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (upperStripCoordinates h p).2 :=
  lowerStripCoordinates_interior hh (exchangeEdges_mem_interior hp)

theorem CleanStripPatch.avoids_sheets {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) {p : ℝ × ℝ} (hp : p ∈ k.domain)
    (ht : p.1 ∈ Set.Ioo (0 : ℝ) 1) (hn : p.2 ≠ 0) : k.map p ∉ S ∪ T := by
  rintro (hS | hT)
  · exact hn ((k.first_sheet p hp).mp hS)
  · rcases (k.second_sheet p hp).mp hT with h0 | h1
    · exact ht.1.ne' h0
    · exact ht.2.ne h1

theorem bigon_boundary_map_avoids_sheets {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) {p : ℝ × ℝ}
    (hp : p ∈ U ∪ V) (hpi : p ∈ interior (WhitneyPairModel.bigon h)) : f p ∉ S ∪ T := by
  rcases hp with hpU | hpV
  · rw [hflo hpU]
    have hc := WhitneyPairModel.lowerStripCoordinates_interior hh hpi
    exact k.avoids_sheets (hmapU hpU) hc.1 hc.2.ne'
  · rw [hfhi hpV]
    have hc := WhitneyPairModel.upperStripCoordinates_interior hh hpi
    change l.map (WhitneyPairModel.upperStripCoordinates h p) ∉ S ∪ T
    rw [Set.union_comm]
    exact l.avoids_sheets (hmapV hpV) hc.1 hc.2.ne'

structure CleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) where
  height_pos : 0 < h
  map : (ℝ × ℝ) → M
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ domain ∩ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  closed_neighborhood : Set (ℝ × ℝ)
  compact_neighborhood : IsCompact closed_neighborhood
  closed_closed_neighborhood : IsClosed closed_neighborhood
  boundary_covered : frontier (WhitneyPairModel.bigon h) ⊆ interior closed_neighborhood
  neighborhood_subset : closed_neighborhood ⊆ domain
  closed_embedding : Topology.IsClosedEmbedding (fun p : closed_neighborhood => map p)
  clean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ closed_neighborhood,
      p ∉ frontier (WhitneyPairModel.bigon h) → map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h

theorem exists_clean_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∃ f : (ℝ × ℝ) → M,
      ∃ W : Set (ℝ × ℝ),
        IsOpen W ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W ∧
            Set.InjOn f W ∧
              (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
                (∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
                  ∃ C : Set (ℝ × ℝ),
                    IsCompact C ∧
                      IsClosed C ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ interior C ∧
                          C ⊆ W ∧
                            Topology.IsClosedEmbedding (fun p : C => f p) ∧
                              (∀ p ∈ WhitneyPairModel.bigon h ∩ C,
                                  p ∉ frontier (WhitneyPairModel.bigon h) → f p ∉ S ∪ T) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                      f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, 0)]
                                          k.map ∘ WhitneyPairModel.lowerStripCoordinates h) ∧
                                      (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
                                          l.map ∘ WhitneyPairModel.upperStripCoordinates h) := by
  obtain ⟨U, V, hU, hV, hfront, hlowU, huppV, hmapU, hmapV, f, hf, hflo, hfhi, hlow, hupp⟩ :=
    exists_smooth_bigon_boundary_neighborhood hh c₀ c₁ k l
  obtain ⟨W, hW, hfrontW, hWUV, hinj, hi⟩ :=
    exists_embedded_bigon_boundary_neighborhood hh k l hover hU hV hfront hlowU huppV hmapU hmapV
      hf hflo hfhi
  have hclean : ∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T := fun p hp =>
    bigon_boundary_map_avoids_sheets hh k l hmapU hmapV hflo hfhi (hWUV hp.1) hp.2
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCclosed, hfrontC, hCW⟩ := exists_compact_closed_between hcompact hW hfrontW
  have hemb : Topology.IsClosedEmbedding (fun p : C => f p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hc : Continuous (fun p : C => f p) :=
      continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono (hCW.trans hWUV))
    apply hc.isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hCW p.property) (hCW q.property) hpq)
  refine
    ⟨f, W, hW, hf.mono hWUV, hinj, hi, hclean, C, hC, hCclosed, hfrontC, hCW, hemb, ?_, hlow,
      hupp, ?_, ?_⟩
  · intro p hp hnot
    apply hclean p ⟨hCW hp.2, ?_⟩
    by_contra hni
    apply hnot
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlowU ht)) (fun _ hp => hflo hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (huppV ht)) (fun _ hp => hfhi hp)

theorem nonempty_cleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀) (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    Nonempty (CleanBigonBoundary (E := E) S T a b k.map l.map h) := by
  obtain
    ⟨f, W, hW, hf, hinj, hi, havoid, C, hC, hCc, hfront, hCW, hemb, hclean, hlow, hupp, hlowg,
      huppg⟩ :=
    exists_clean_bigon_boundary_neighborhood hh c₀ c₁ k l hover
  exact
    ⟨{  height_pos := hh
        map := f
        domain := W
        open_domain := hW
        smooth := hf
        injective := hinj
        derivative_injective := hi
        interior_avoids := havoid
        closed_neighborhood := C
        compact_neighborhood := hC
        closed_closed_neighborhood := hCc
        boundary_covered := hfront
        neighborhood_subset := hCW
        closed_embedding := hemb
        clean := hclean
        lower := hlow
        upper := hupp
        lower_germ := hlowg
        upper_germ := huppg }⟩

end
