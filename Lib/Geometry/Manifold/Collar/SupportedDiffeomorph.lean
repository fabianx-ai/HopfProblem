/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Extending a compactly supported diffeomorphism by the identity

Let `Φ : PartialDiffeomorph I J X Y ∞` and let `d` be a diffeomorphism of `X` that is the
identity off a compact set `K ⊆ Φ.source`. Then `Φ ∘ d ∘ Φ⁻¹` on `Φ.target`, extended by the
identity elsewhere, is a diffeomorphism of the Hausdorff manifold `Y`
(`SupportedDiffeomorph.extension`); it is the identity off `Φ '' K`. This is the standard device
for transplanting a compactly supported diffeomorphism of a model into a manifold (cf. Milnor,
*Topology from the Differentiable Viewpoint*, §4, homogeneity lemma; Hirsch, *Differential
Topology*, Ch. 8, §1).

## Main definitions

* `SupportedDiffeomorph.extendMap` : the extension of a map by the identity.
* `SupportedDiffeomorph.extension` : the extension as a `Diffeomorph`.

## Tags

diffeomorphism, compact support, extension by the identity
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

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
