/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate
import Lib.Geometry.Manifold.Whitney.CleanStrips.StripModel

/-!
# Strip charts along a sheet

`StripNormalData A B S k` is a chart of `M` with model `(ℝ × A) × B` in which the sheet `S` is cut
out by the vanishing of the `B`-coordinate, the centre line is the image of `t ↦ ((t, 0), 0)`, and
the map `k : ℝ × ℝ → M` has nonvanishing normal derivative along `[0, 1]`. Read in the chart, `k`
traverses the centre line at unit speed and its derivative factors through the derivative of the
chart.

Given a second chart `Ψ : (ℝ × ℝ) × Z → M` whose zero section is a strip `f`, the file defines the
normal frame `StripNormalData.normalFrame` (the sheet directions `A` pushed into the normal factor
`Z` of `Ψ`), proves it smooth in the time and injective where `f` is given by `k` up to a
submersive reparametrisation, and computes the derivative of the sheet transition
`Ψ⁻¹ ∘ chart` on the sheet factor. These are the frame-field computations of the Whitney trick
(Milnor, *Lectures on the h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- A strip chart for a sheet `S` along a map `k : ℝ × ℝ → M`: a chart of `M` with model
`(ℝ × A) × B` in which `S` is cut out by the vanishing of the last coordinate, the centre line
is the image of `t ↦ ((t, 0), 0)`, and `k` has nonvanishing normal derivative along `[0, 1]`.
-/
structure StripNormalData (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (S : Set M) (k : (ℝ × ℝ) → M) where
  /-- The strip chart, with model `(ℝ × A) × B`. -/
  chart :
    PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M ∞
  /-- The centre line over `[0, 1]` lies in the source of the chart. -/
  line : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) chart.source
  /-- In the chart, the sheet `S` is the zero set of the `B`-coordinate. -/
  sheet : ∀ q ∈ chart.source, chart q ∈ S ↔ q.2 = 0
  /-- On the axis, `k` is the centre line read through the chart. -/
  center : ∀ t, k (t, 0) = chart (StripCoordinates.center t)
  /-- Along `[0, 1]` the normal coordinate of `k` has nonzero vertical derivative. -/
  normal_nonzero :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (TransverseCoordinates.normalCoordinate chart ∘ k) (t, 0) (0, 1) ≠ 0

/-- The map `k` read in the strip chart, `chart⁻¹ ∘ k`. -/
def StripNormalData.coordinateMap {A B E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) : (ℝ × ℝ) → StripCoordinates.Space A B :=
  d.chart.symm ∘ k

/-- Along `[0, 1]` the centre of the strip lies in the target of the chart. -/
theorem StripNormalData.center_mem_target {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    k (t, 0) ∈ d.chart.target := by
  rw [d.center t]
  exact d.chart.map_source' (d.line ht)

/-- Near each time in `[0, 1]` the axis of the coordinate map agrees with the centre line. -/
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

/-- At each time in `[0, 1]` the coordinate map sends `(t, 0)` to the centre `center t`. -/
theorem StripNormalData.coordinate_center {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.coordinateMap (t, 0) = StripCoordinates.center t :=
  (d.coordinate_center_germ ht).eq_of_nhds

/-- The coordinate map is smooth at the points of the axis over `[0, 1]`. -/
theorem StripNormalData.contDiffAt_coordinateMap {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) : ContDiffAt ℝ ∞ d.coordinateMap (t, 0) :=
  ((d.chart.contMDiffOn_invFun.contMDiffAt
          (d.chart.open_target.mem_nhds (d.center_mem_target ht))).comp
      (t, 0) hk).contDiffAt

/-- The coordinate map has horizontal derivative `center 1` along the axis, so it traverses the
centre line at unit speed.
-/
theorem StripNormalData.horizontal_coordinateDerivative {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    fderiv ℝ d.coordinateMap (t, 0) (1, 0) = StripCoordinates.center 1 :=
  StripCoordinates.horizontal_derivative_of_center_germ
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp)) (d.coordinate_center_germ ht)

/-- The coordinate map has nonzero normal component of its vertical derivative along the axis. -/
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

/-- Along the axis the derivative of `k` factors as the derivative of the chart composed with the
derivative of the coordinate map.
-/
theorem StripNormalData.mfderiv_eq_comp_fderiv_coordinateMap {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
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

/-- The frame of the normal bundle of `Ψ` along the strip at time `t`: the transverse directions of
the sheet pushed into the normal factor `Z` of the chart `Ψ`.
-/
def StripNormalData.normalFrame {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) : A →L[ℝ] Z :=
  (fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t)).comp
    StripCoordinates.sheetTransverseInclusion

/-- The normal frame depends smoothly on the time parameter where both charts are defined. -/
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

/-- The normal frame is smooth on an open neighbourhood of `[0, 1]` when the whole centre line lies
in the target of `Ψ`.
-/
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

/-- The normal frame is injective at each time of `[0, 1]`: the transverse directions of the sheet
inject into the normal directions of the strip chart, since the strip and the sheet are
transverse.
-/
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
      rw [d.mfderiv_eq_comp_fderiv_coordinateMap ht hk]
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

/-- The transition from the sheet coordinates `ℝ × A` to the chart `Ψ`, obtained by including the
sheet factor into the strip model and reading the result in `Ψ`.
-/
def StripNormalData.sheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  (Ψ.symm ∘ d.chart) ∘ (ContinuousLinearMap.inl ℝ (ℝ × A) B)

/-- The derivative of the sheet transition at `(t, 0)`. -/
def StripNormalData.sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    (ℝ × A) →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (d.sheetTransition Ψ) (t, 0)

/-- The transition `Ψ⁻¹ ∘ chart` between the two charts is smooth at the centre. -/
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

/-- The sheet transition is smooth at `(t, 0)` for `t` in `[0, 1]`. -/
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

/-- The sheet differential is the derivative of the chart transition restricted to the sheet factor.
-/
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

/-- The normal component of the sheet differential on the transverse factor `A` is the normal frame.
-/
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

/-- If the sheet is given near `q t` by the strip map `k` in coordinates `c`, then near `t` the axis
of the sheet transition is the curve `s ↦ (q s, 0)`.
-/
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

/-- Along such a germ the sheet differential sends the unit horizontal vector to the velocity of the
curve.
-/
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

end
