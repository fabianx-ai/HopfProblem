/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Simultaneous charts at a transverse crossing

Let `F : N → M` and `G : P → M` be smooth embeddings into a compact manifold `M`, of complementary
dimension, meeting transversally at `F x = G y`. Then near that point `M` has a chart
`Φ : D × Z → M` in which the two submanifolds are the two coordinate factors: `Φ (u, 0)` runs
along `F`, `Φ (0, v)` along `G`, and a point of the chart lies on `F` (resp. `G`) exactly when its
second (resp. first) coordinate vanishes. Consequently transverse intersection points are
isolated, and two compact submanifolds of complementary dimension meeting transversally meet in a
finite set.

The chart is obtained by adding the two parametrisations in a Euclidean embedding of `M`,
retracting back to `M`, and applying the inverse function theorem; the derivative at the origin is
the coproduct of the two derivatives, invertible by transversality and the dimension count.

## Main results

* `exists_simultaneous_sheetChart`, `exists_clean_simultaneous_sheetChart` : the chart for two
  parametrised sheets, and its clean form.
* `exists_clean_crossingChart_of_parametrizations`, `exists_clean_crossingChart` : the clean
  chart for two embedded submanifolds.
* `exists_isolating_crossing_neighborhood`, `isDiscrete_transverse_intersections`,
  `finite_transverse_intersections` : transverse intersections of complementary dimension are
  discrete, and finite for compact submanifolds.

## References

* Victor Guillemin and Alan Pollack, *Differential topology*, §1.5 (transversality) and §2.3
  (finiteness of transverse intersections of complementary dimension).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- The map `(x, z) ↦ f x + g z - f 0` gluing two maps into a normed space along their common value
at the origin; it restricts to `f` on the first factor and to `g` on the second.
-/
def TransverseCoordinates.sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (q : D × Z) : A :=
  f q.1 + g q.2 - f 0

/-- The glued map restricts to `f` on the first factor, provided `f` and `g` agree at the origin. -/
theorem TransverseCoordinates.sumMap_left {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup Z] [NormedAddCommGroup A] (f : D → A) (g : Z → A) (hzero : g 0 = f 0)
    (x : D) : sumMap f g (x, 0) = f x := by simp [sumMap, hzero]

/-- The glued map restricts to `g` on the second factor. -/
theorem TransverseCoordinates.sumMap_right {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (z : Z) : sumMap f g (0, z) = g z := by
  simp [sumMap, add_sub_cancel_left]

/-- The glued map is smooth on a product of sets on which the two maps are smooth. -/
theorem TransverseCoordinates.contDiffOn_sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} {U : Set D} {V : Set Z} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) : ContDiffOn ℝ ∞ (sumMap f g) (U ×ˢ V) :=
  ((hf.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).add
        (hg.comp contDiff_snd.contDiffOn (fun _ hx => hx.2))).sub
    contDiffOn_const

/-- The derivative of the glued map at the origin is the coproduct of the two derivatives. -/
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

/-- The two-sheet chart candidate attached to a smooth retraction of a tubular neighbourhood of `M`
in `E`: the two maps are added in `E` and pushed back to `M` by the retraction.
-/
def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) : D × Z → M :=
  r.toFun ∘ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g)

/-- The domain on which the two-sheet chart candidate is defined: the product of the two given sets
intersected with the preimage of the retraction's domain.
-/
def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinateDomain {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (U : Set D) (V : Set Z) : Set (D × Z) :=
  (U ×ˢ V) ∩ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) ⁻¹' r.domain

/-- The two-sheet chart candidate restricts to `f` on the first factor. -/
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

/-- The two-sheet chart candidate restricts to `g` on the second factor. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_right {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (z : Z) : r.sheetCoordinates f g (0, z) = g z := by
  rw [sheetCoordinates, Function.comp_apply, TransverseCoordinates.sumMap_right]
  exact r.retract (g z)

/-- The origin belongs to the domain of the two-sheet chart candidate whenever it belongs to both
given sets.
-/
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

/-- The domain of the two-sheet chart candidate is open. -/
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

/-- The two-sheet chart candidate is smooth on its domain. -/
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

/-- At the origin the derivative of the two-sheet chart candidate is the coproduct of the
derivatives of the two maps; so the candidate is a local diffeomorphism exactly when the two
sheets are transverse.
-/
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

/-- For linear maps out of spaces of complementary dimension, surjectivity of the coproduct `F ⊕ G`
implies that it is invertible; this is the linear-algebra form of transversality in
complementary dimension.
-/
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

/-- Simultaneous chart at a transverse crossing: if two parametrised sheets `f` and `g` of
complementary dimension meet at `f 0 = g 0` with surjective coproduct of derivatives, then a
neighbourhood of that point carries a chart `Φ` of the ambient manifold in which the two sheets
are the two coordinate axes, `Φ (x, 0) = f x` and `Φ (0, z) = g z`.
-/
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

/-- The clean form of the simultaneous chart: the chart can be shrunk so that in addition a point of
the chart lies on the first sheet exactly when its second coordinate vanishes, and on the second
sheet exactly when its first coordinate vanishes.
-/
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

/-- Clean crossing chart, stated for two embedded submanifolds given with parametrisations `c` and
`d`: at a transverse intersection point of complementary dimension there is a chart of the
ambient manifold in which the images of the two embeddings are the two coordinate factors,
cleanly.
-/
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

/-- Clean crossing chart at a transverse intersection point of two embedded submanifolds of
complementary dimension: a chart of the ambient manifold in which the two submanifolds become
the two coordinate factors, and in which membership of each submanifold is the vanishing of the
complementary coordinate (Guillemin–Pollack, Differential Topology, §2.3).
-/
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

/-- A transverse intersection point of two embedded submanifolds of complementary dimension is
isolated in their intersection: some open neighbourhood of it meets the intersection only in
that point.
-/
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

/-- Two embedded submanifolds of complementary dimension meeting everywhere transversally intersect
in a discrete set.
-/
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

/-- Two compact embedded submanifolds of complementary dimension meeting everywhere transversally in
a compact manifold intersect in a finite set (Guillemin–Pollack, Differential Topology, §1.5).
-/
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

end
