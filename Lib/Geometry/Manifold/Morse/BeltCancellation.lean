/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.RankThreeModel

/-!
# Belt-sphere cancellation

Belt intersection points and their signs for Morse surgery data, the Whitney cancellation of opposite-sign belt intersections, adapted windows and the cancellation rows of `MorseCancellation`, regular levels, punctured radial charts and local-degree boundary data.

Moved verbatim from the project stock file `Hopf/SingularHomology.lean` (integration 4,
`Lib/reports/integration-4/singhom-moves.md`); the families here are
`ManifoldMorse.MorseSurgeryData`, `AdaptedWindows`, `MorseCancellation`, `RegularLevel`, `PuncturedRadial`, `LocalDegree.BoundaryData`. The declarations keep their historical dotted names
and their order; the file order is the dependency order.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

universe u v

noncomputable section

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_belt_whitney_cancellation_of_opposite_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ K : Set D.UpperLevel,
              IsCompact K ∧
                Disjoint K ((Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}) ∧
                  ∃ A : ℝ × D.UpperLevel → D.UpperLevel,
                    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
                        𝓘(ℝ, RegularLevel.Model E) ∞ A ∧
                      (∀ y, A (0, y) = y) ∧
                        (∀ t,
                            ∃ e :
                              Diffeomorph 𝓘(ℝ, RegularLevel.Model E)
                                𝓘(ℝ, RegularLevel.Model E) D.UpperLevel D.UpperLevel ∞,
                              ∀ y, A (t, y) = e y) ∧
                          (∀ t y, y ∉ K → A (t, y) = y) ∧
                            ((fun y => A (1, y)) '' Set.range g) ∩
                                Set.range D.surgery.beltSphere =
                              (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨y₀, hy₀⟩ := hx₀
  obtain ⟨y₁, hy₁⟩ := hx₁
  have hne : x₀ ≠ x₁ := by
    intro heq
    rw [heq] at hsign
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    exact hs _ hsign
  obtain ⟨a, b, ha₀, ha₁, _, _, k₀, k₁, l₀, l₁, k, l, ⟨d⟩, ⟨e⟩, htube⟩ :=
    D.exists_belt_tubular_strip_pair hf hdim hindex hnull g hg hinj hi (fun x y hxy => ht x y hxy)
      x₀ x₁ y₀ y₁ hy₀ hy₁ hne
  obtain ⟨tube⟩ := htube 1 (by norm_num)
  have hcenter₀ : g x₀ = d.chart (StripCoordinates.center 0) :=
    ha₀.symm.trans ((k.center 0 (by simp)).symm.trans (d.center 0))
  have hcenter₁ : g x₁ = d.chart (StripCoordinates.center 1) :=
    ha₁.symm.trans ((k.center 1 (by simp)).symm.trans (d.center 1))
  have hcorner :=
    (D.opposite_beltIntersectionSigns_iff_Whitney_corners hf hdim hindex r g hg hinj hi ht tube d
          e x₀ x₁ hcenter₀ hcenter₁).mp
      hsign
  obtain ⟨K, hK, _, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    tube.exists_rankThree_relative_cancellation d e (isCompact_range g.continuous).isClosed
      D.belt_isClosedEmbedding.isClosed_range hcorner
  rw [ha₀, ha₁] at hcancel hdisjoint
  exact ⟨K, hK, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_signed_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ e :
              Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                D.UpperLevel D.UpperLevel ∞,
              ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
                SupportedDiffeomorph.IsotopicToIdentity e ∧
                  (∀ x, g' x = e (g x)) ∧
                    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' ∧
                      Function.Injective g' ∧
                        (∀ x,
                            Function.Injective
                              (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x)) ∧
                          (∀ x y,
                              NativeTransversality.At (𝓡 2) (𝓡 3)
                                𝓘(ℝ, RegularLevel.Model E) g' D.surgery.beltSphere x y) ∧
                            D.beltIntersectionPoints 2 g' =
                                D.beltIntersectionPoints 2 g \ { x₀, x₁ } ∧
                              (∀ x ∈ D.beltIntersectionPoints 2 g',
                                  (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                                ∀ x ∈ D.beltIntersectionPoints 2 g',
                                  D.beltIntersectionSign 2 r g' x =
                                    D.beltIntersectionSign 2 r g x := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨K, hK, hdis, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    D.exists_belt_whitney_cancellation_of_opposite_signs hf hdim hindex hnull r g hg hinj hi ht x₀
      x₁ hx₀ hx₁ hsign
  obtain ⟨e, he⟩ := hAt 1
  have hisotopy : SupportedDiffeomorph.IsotopicToIdentity e := ⟨A, hA, hA₀, he, hAt⟩
  have hfixe : ∀ y ∉ K, e y = y := fun y hy => (he y).symm.trans (hfix 1 y hy)
  have hfun : (fun y => A (1, y)) = e := funext he
  rw [hfun] at hcancel
  let g' : C(Hemisphere.Sphere 2, D.UpperLevel) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hg' : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' := e.contMDiff.comp hg
  have hinj' : Function.Injective g' := e.injective.comp hinj
  have hi' : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg.mdifferentiableAt (by simp))]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (hi x)
  have hfixR : ∀ y ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}, e y = y := by
    intro y hy
    exact hfixe y (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have hpre :=
    SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal e.toEquiv
      (g : Hemisphere.Sphere 2 → D.UpperLevel) hfixR hcancel
  have hp : (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁} = { x₀, x₁ } := by
    ext x
    change (g x = g x₀ ∨ g x = g x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinj.eq_iff hinj.eq_iff
  have hpoints : D.beltIntersectionPoints 2 g' = D.beltIntersectionPoints 2 g \ { x₀, x₁ } :=
    hpre.trans
      (congrArg (fun s : Set (Hemisphere.Sphere 2) => D.beltIntersectionPoints 2 g \ s) hp)
  have hgerm :
    ∀ x ∈ D.beltIntersectionPoints 2 g',
      (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g := by
    intro x hx
    have hxold : x ∈ D.beltIntersectionPoints 2 g \ { x₀, x₁ } := hpoints ▸ hx
    have hy : g x ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁}
      rw [hp]
      exact hxold.2
    exact
      SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hK.isClosed hfixe
        g.continuous (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have ht' :
    ∀ x y,
      NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g'
        D.surgery.beltSphere x y := by
    intro x y hxy
    have hx : x ∈ D.beltIntersectionPoints 2 g' := ⟨y, hxy⟩
    have hnear := hgerm x hx
    have hpoint : g' x = g x := hnear.eq_of_nhds
    have hder :
      (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E) =
        mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x :=
      hnear.mfderiv_eq
    change
      Function.Surjective
        ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E).coprod
          (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) D.surgery.beltSphere y :
            EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E))
    rw [hder]
    exact ht x y (hxy.trans hpoint)
  refine ⟨e, g', hisotopy, fun _ => rfl, hg', hinj', hi', ht', hpoints, hgerm, ?_⟩
  intro x hx
  have hnormal : (D.beltNormal ∘ g') =ᶠ[𝓝 x] (D.beltNormal ∘ g) := by
    filter_upwards [hgerm x hx] with z hz
    exact congrArg D.beltNormal hz
  have hder :
    (mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g') x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates) =
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x :=
    hnormal.mfderiv_eq
  have hjac : D.beltIntersectionJacobian 2 r g' x = D.beltIntersectionJacobian 2 r g x :=
    congrArg
      (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates =>
        SphereNormalCoordinates.normalJacobian r x L)
      hder
  exact congrArg SignType.sign hjac

def ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) : Prop :=
  letI := RegularLevel.chartedSpace hf D.upper_regular
  letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
    Function.Injective g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x)) ∧
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y

theorem ManifoldMorse.MorseSurgeryData.finite_points_of_isTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    {g : C(Hemisphere.Sphere 2, D.UpperLevel)}
    (hg : D.IsTransverseBeltSphere hf hdim hindex g) : (D.beltIntersectionPoints 2 g).Finite := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hs, hinj, _, ht⟩ := hg
  exact D.finite_beltIntersectionPoints hf 3 2 hindex g hs hinj ht

attribute [local instance 100] Classical.propDecidable in
abbrev ManifoldMorse.MorseSurgeryData.HandleDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  MorseHandle.UnitDisk d.chart.NegativeCoordinates ×
    MorseHandle.UnitDisk d.chart.PositiveCoordinates

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.handleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) : C(d.HandleDomain, M) :=
  d.chart.attachingHandleMap d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.handleFacePoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) : d.HandleDomain :=
  (⟨u, Metric.sphere_subset_closedBall u.property⟩, v)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.handleMap_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.handleMap (d.handleFacePoint u ⟨0, by simp⟩) = (d.surgery.attachingSphere u : M) := by
  rw [d.attaching_eq]
  rfl

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(MorseHandle.UnitDisk d.chart.NegativeCoordinates, M) :=
  HandleCoreAttachment.core d.handleMap

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.coreMap ⟨u, Metric.sphere_subset_closedBall u.property⟩ =
      (d.surgery.attachingSphere u : M) :=
  d.handleMap_core u

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_lower_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    f (d.coreMap u) ≤ f p - d.radius ^ 2 ↔ ‖(u : d.chart.NegativeCoordinates)‖ = 1 :=
  d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block (u, ⟨0, by simp⟩)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.coreMap := by
  apply d.coreMap.continuous.isClosedEmbedding
  intro x y hxy
  have heq :=
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).injective hxy
  exact congrArg Prod.fst heq

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f) :
    ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) ≃ₕ
      { y : M // f y ≤ f p + d.radius ^ 2 } :=
  (ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ f p - d.radius ^ 2} d.handleMap
        (isClosed_le hf continuous_const)
        (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
        (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)).trans
    d.attachmentHomeomorph.toHomotopyEquiv

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreCellPresentation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    EmbeddedCellAttachment d.chart.NegativeCoordinates
      ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
  EmbeddedCellAttachment.ofUnion _ d.coreMap (isClosed_le hf continuous_const)
    d.coreMap_isClosedEmbedding d.coreMap_lower_iff

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.cellOldHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    { y : M // f y ≤ f p - d.radius ^ 2 } ≃ₜ (d.coreCellPresentation hf).old
    where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreBoundaryMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1, { y : M // f y ≤ f p - d.radius ^ 2 }) :=
  (⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩ :
        C(d.LowerLevel, { y : M // f y ≤ f p - d.radius ^ 2 })).comp
    d.surgery.attachingSphere

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreCell_attaching_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.coreCellPresentation hf).attachingSphere =
      (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun.comp d.coreBoundaryMap := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact d.coreMap_boundary u

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.realizedLowerInclusion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) :
    C({ y : M // f y ≤ f p - d.radius ^ 2 }, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨fun x => d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩,
    d.attachmentHomeomorph.continuous.comp (continuous_inclusion (fun _ hx => Or.inl hx))⟩

theorem AdaptedWindows.forward_limit_below_regular_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f) (x : { y : M // f y = a })
    {p : M} (hlim : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) : f p < a := by
  obtain ⟨r, hr, q, hq, -, hqLim, hheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct (x : M)
  have hqp : q = p := tendsto_nhds_unique hqLim hlim
  have hh := (hheight (hreg x x.property)).1
  simpa only [hqp, x.property] using hh

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.place_one_handle_in_distinct_minimum_basins {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : ManifoldMorse.criticalPoints E f) (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧
        ∃ p r : ManifoldMorse.criticalPoints E f,
          MorseCancellation.nativeMorseIndex E f p = 0 ∧
            MorseCancellation.nativeMorseIndex E f r = 0 ∧
              p ≠ r ∧
                f p < S.toSurgeryWindows.lower q ∧
                  f r < S.toSurgeryWindows.lower q ∧
                    Filter.Tendsto
                        (fun t => S.flow t (d ((S.data q).surgery.attachingSphere u)).val)
                        Filter.atTop (𝓝 p.val) ∧
                      Filter.Tendsto
                          (fun t => S.flow t (d ((S.data q).surgery.attachingSphere v)).val)
                          Filter.atTop (𝓝 r.val) ∧
                        ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                          Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 r.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  let ι : C((S.data q).LowerLevel, { z : M // f z ≤ S.toSurgeryWindows.lower q }) :=
    ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := by
    intro h
    have hh : (S.data q).coreBoundaryMap u = (S.data q).coreBoundaryMap v := congrArg ι h
    exact hnot (hh ▸ Joined.refl _)
  obtain ⟨d, hd, ⟨p, hp, hpu⟩, ⟨r, hr, hrv⟩⟩ :=
    MorseCancellation.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu
  have hrq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α v)) hrv
  have hpr : p ≠ r := by
    intro h
    subst r
    let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
    have hnew : Joined (ι (d (α u))) (ι (d (α v))) :=
      MorseCancellation.joined_sublevel_of_common_forward_limit S.flow hf.continuous
        (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
        (ι (d (α u))) (ι (d (α v))) hpq hpu hrv
    exact
      hnot
        (((MorseCancellation.isotopicToIdentity_joined hd (α u)).map ι.continuous).trans
          (hnew.trans ((MorseCancellation.isotopicToIdentity_joined hd (α v)).map ι.continuous).symm))
  refine ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, ?_⟩
  intro w
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := fun h => hxy (congrArg α h)
  rcases MorseCancellation.unitSphere_eq_two_points_of_finrank_one hindex u v huv w with h | h
  · subst w
    exact Or.inl hpu
  · subst w
    exact Or.inr hrv

theorem MorseCancellation.fderiv_beltPassage_upper_fst {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s w : ℝ) (u : N) (v : P) :
    (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 = (ρ * w) • u := by
  have hfirst : HasDerivAt (fun t : ℝ => (BeltPassage.upper ρ t u v).1) (ρ • u) s := by
    simpa only [BeltPassage.upper, id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul ρ).smul_const u
  have hchain :
    fderiv ℝ (fun t => (BeltPassage.upper ρ t u v).1) s =
      (ContinuousLinearMap.fst ℝ N P).comp
        (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
    have hh :=
      fderiv_comp s (ContinuousLinearMap.fst ℝ N P).differentiableAt
        ((BeltPassage.contDiff_upper ρ u v).differentiable (by simp) s)
    rw [(ContinuousLinearMap.fst ℝ N P).fderiv] at hh
    exact hh
  have hh := congrArg (fun L : ℝ →L[ℝ] N => L w) hchain
  rw [hfirst.hasFDerivAt.fderiv] at hh
  change w • (ρ • u) = (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 at hh
  rw [smul_smul, mul_comm w ρ] at hh
  exact hh.symm

theorem MorseCancellation.injective_fderiv_beltPassage_upper {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ)
    {u : N} (hu : u ≠ 0) (v : P) :
    Function.Injective (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
  intro a b hab
  have hh := congrArg Prod.fst hab
  rw [fderiv_beltPassage_upper_fst, fderiv_beltPassage_upper_fst] at hh
  exact mul_left_cancel₀ hρ (smul_left_injective ℝ hu hh)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (nativeBeltArc S q u v) s) := by
  have ht := nativeBeltArc_coordinates_mem_target S q u v hs
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  change
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        ((S.data q).chart.splitChart.symm ∘
          (fun t => BeltPassage.upper (S.data q).radius t u.val v.val))
        s)
  rw [mfderiv_comp s ((S.data q).chart.splitChart.symm.mdifferentiableAt (by simp) ht)
      ((BeltPassage.contDiff_upper (S.data q).radius u.val
            v.val).contMDiff.mdifferentiableAt
        (by simp)),
    mfderiv_eq_fderiv]
  exact
    (PartialChart.bijective_mfderiv (S.data q).chart.splitChart.symm ht).injective.comp
      (injective_fderiv_beltPassage_upper (S.data q).radius_pos.ne' s hu v.val)

theorem RegularLevel.contMDiffWithinAt_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ g S x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt.comp_contMDiffWithinAt x hg
  · intro hg
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hg.continuousWithinAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp_contMDiffWithinAt x hg
    change ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) S x
    exact contDiff_snd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hcomp

theorem RegularLevel.contMDiffOn_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) :
    letI := chartedSpace hf hreg
    ContMDiffOn I 𝓘(ℝ, Model E) ∞ g S ↔ ContMDiffOn I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S := by
  let _ := chartedSpace hf hreg
  exact
    forall_congr'
      (fun x => forall_congr' (fun _ => contMDiffWithinAt_iff_inclusion hf hreg I g S x))

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeBeltLevelArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) :
    (S.data q).UpperLevel :=
  if hs : |s| ≤ 1 then ⟨nativeBeltArc S q u v s, nativeBeltArc_height S q u v hs⟩
  else (S.data q).surgery.beltSphere v

theorem MorseCancellation.nativeBeltLevelArc_coe {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (nativeBeltLevelArc S q u v s).val = nativeBeltArc S q u v s := by
  simp only [nativeBeltLevelArc, dif_pos hs]

theorem MorseCancellation.nativeBeltLevelArc_coe_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    (Subtype.val ∘ nativeBeltLevelArc S q u v) =ᶠ[𝓝 s] nativeBeltArc S q u v := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)

theorem MorseCancellation.nativeBeltLevelArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeBeltLevelArc S q u v)
      (Set.Ioo (-1 : ℝ) 1) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  apply
    (RegularLevel.contMDiffOn_iff_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
        (nativeBeltLevelArc S q u v) (Set.Ioo (-1 : ℝ) 1)).mpr
  apply (nativeBeltArc_contMDiffOn S q u v).congr
  intro s hs
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

theorem MorseCancellation.nativeBeltLevelArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) s) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hg := nativeBeltLevelArc_coe_germ S q u v hs
  apply
    RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
      (nativeBeltLevelArc S q u v) s
  · exact
      ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
            (Ioo_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq
        hg
  · rw [hg.mfderiv_eq]
    exact nativeBeltArc_derivative_injective S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltLevelArc_normal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (S.data q).beltNormal (nativeBeltLevelArc S q u v s) = ((S.data q).radius * s) • u.val := by
  change ((S.data q).chart.splitChart (nativeBeltLevelArc S q u v s).val).1 = _
  rw [nativeBeltLevelArc_coe S q u v hs]
  exact
    congrArg Prod.fst
      ((S.data q).chart.splitChart.right_inv' (nativeBeltArc_coordinates_mem_target S q u v hs))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltLevelArc_transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (hq : nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) 0 :
            ℝ →L[ℝ] RegularLevel.Model E).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let d := S.data q
  let γ := nativeBeltLevelArc S q u v
  let L : ℝ →L[ℝ] d.chart.NegativeCoordinates :=
    ContinuousLinearMap.toSpanSingleton ℝ (d.radius • u.val)
  have hpoint : γ 0 = d.surgery.beltSphere v :=
    Subtype.ext
      ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans (nativeBeltArc_zero S q u v))
  have hgerm : d.beltNormal ∘ γ =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with
      s hs
    change d.beltNormal (nativeBeltLevelArc S q u v s) = s • (d.radius • u.val)
    rw [nativeBeltLevelArc_normal S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩), smul_smul,
      mul_comm s d.radius]
  have hnormalDerivative :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ γ) 0 = L := by
    rw [hgerm.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv]
  have hγ :=
    (nativeBeltLevelArc_contMDiffOn S hf q u v).contMDiffAt
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  let A : ℝ →L[ℝ] RegularLevel.Model E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) γ 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  have hnγ :
    MDifferentiableAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (γ 0) := by
    rw [hpoint]
    exact hnormal.mdifferentiableAt (by simp)
  have hQA : Q.comp A = L := by
    have hh := mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh.symm.trans hnormalDerivative
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hLi : Function.Injective L := smul_left_injective ℝ (smul_ne_zero d.radius_pos.ne' hu)
  have hdim : Module.finrank ℝ ℝ = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [Module.finrank_self]
    exact ((nativeMorseIndex_eq_chart d.chart).symm.trans hq).symm
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) hdim).mp hLi
  have hQAs : Function.Surjective (Q.comp A) := hQA.symm ▸ hLs
  have hker : B.range = Q.ker := d.range_belt_derivative_eq_normal_kernel hf n v
  change Function.Surjective (A.coprod B)
  intro z
  obtain ⟨s, hs⟩ := hQAs (Q z)
  have hmem : z - A s ∈ Q.ker := by
    change Q (z - A s) = 0
    change Q (A s) = Q z at hs
    rw [map_sub, hs, sub_self]
  rw [← hker] at hmem
  obtain ⟨w, hw⟩ := hmem
  change B w = z - A s at hw
  refine ⟨(s, w), ?_⟩
  change A s + B w = z
  rw [hw]
  abel

theorem MorseCancellation.transverse_circle_of_arc_germ {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N}
    {γ : Circle → N} {ψ : ℝ → Circle} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ) (hgerm : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] α) (B : D →L[ℝ] G)
    (htrans : Function.Surjective ((mfderiv 𝓘(ℝ, ℝ) J α 0 : ℝ →L[ℝ] G).coprod B)) :
    Function.Surjective ((mfderiv (𝓡 1) J γ (ψ 0) : EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B) :=
  by
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (ψ 0)
  let P : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ψ 0
  let A₀ : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J α 0
  have hc := mfderiv_comp 0 (hγ.mdifferentiableAt (by simp)) (hψ.mdifferentiableAt (by simp))
  have heq : A.comp P = A₀ := hc.symm.trans hgerm.mfderiv_eq
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  refine ⟨(P a, b), ?_⟩
  have ha := congrArg (fun L : ℝ →L[ℝ] G => L a) heq
  change A (P a) + B b = y
  change A (P a) = A₀ a at ha
  rw [ha]
  exact hab

theorem MorseCancellation.surjective_coprod_comp_left {A A' B G : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] G) (R : B →L[ℝ] G)
    (P : A' →L[ℝ] A) (hP : Function.Surjective P) (htrans : Function.Surjective (L.coprod R)) :
    Function.Surjective ((L.comp P).coprod R) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  obtain ⟨a', ha⟩ := hP a
  refine ⟨(a', b), ?_⟩
  change L (P a') + R b = y
  rw [ha]
  exact hab

def MorseCancellation.euclideanTail (n : ℕ) :
    Hemisphere.Ambient (n + 1) →L[ℝ] Hemisphere.Ambient n :=
  ({    toFun := fun x => WithLp.toLp 2 (fun i : Fin n => x i.succ)
        map_add' := by intro x y; ext i; rfl
        map_smul' := by intro a x; ext i; rfl } :
      Hemisphere.Ambient (n + 1) →ₗ[ℝ] Hemisphere.Ambient n).toContinuousLinearMap

theorem MorseCancellation.euclideanTail_hemisphere {n : ℕ} (b : Bool) (x : Hemisphere.Ball n) :
    euclideanTail n (Hemisphere.point b x).val = x.val := by
  ext i
  rfl

theorem MorseCancellation.exists_belt_point_avoiding_smooth_image {E M D H Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace Y]
    [ChartedSpace H Y] [IsManifold I ∞ Y] [LindelofSpace Y] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] (g : Y → M)
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hdim : Module.finrank ℝ D < n) :
    ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
      (d.surgery.beltSphere v).val ∉ Set.range g := by
  let b :=
    (stdOrthonormalBasis ℝ d.chart.PositiveCoordinates).reindex
      (finCongr (Fact.out : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1))
  let L : d.chart.PositiveCoordinates ≃ₗᵢ[ℝ] Hemisphere.Ambient (n + 1) := b.repr
  let P : M → Hemisphere.Ambient n := fun x =>
    euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart x).2)
  let U : Set Y := g ⁻¹' d.chart.splitChart.source
  have hU : IsOpen U := d.chart.splitChart.open_source.preimage hg.continuous
  have hPg : ContMDiffOn I 𝓘(ℝ, Hemisphere.Ambient n) ∞ (P ∘ g) U := by
    have hc :
      ContMDiffOn I 𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
        (d.chart.splitChart ∘ g) U :=
      d.chart.splitChart.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
    let A :
      d.chart.NegativeCoordinates × d.chart.PositiveCoordinates →L[ℝ]
        Hemisphere.Ambient n :=
      (euclideanTail n).comp
        ((d.radius⁻¹ • L.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (ContinuousLinearMap.snd ℝ d.chart.NegativeCoordinates d.chart.PositiveCoordinates))
    have hQ :
      ContDiff ℝ ∞
        (fun z : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates =>
          euclideanTail n (d.radius⁻¹ • L z.2)) :=
      A.contDiff
    exact hQ.contMDiff.comp_contMDiffOn hc
  have hdense :=
    GeneralPosition.dense_compl_manifold_image hU hPg
      (show Module.finrank ℝ D < Module.finrank ℝ (Hemisphere.Ambient n) by
        simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hdim)
  obtain ⟨x, hxavoid, hxnorm⟩ := hdense.exists_dist_lt 0 (show (0 : ℝ) < 1 by norm_num)
  have hx : ‖x‖ < 1 := by simpa only [dist_zero_left] using hxnorm
  let xB : Hemisphere.Ball n := ⟨x, mem_closedBall_zero_iff.mpr hx.le⟩
  let w := Hemisphere.point Bool.true xB
  let v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1 :=
    ⟨L.symm w.val, by
      rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp w.property⟩
  have hcoord : d.chart.splitChart (d.surgery.beltSphere v).val = (0, d.radius • v.val) := by
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)
  have hproject : P (d.surgery.beltSphere v).val = x := by
    change
      euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart (d.surgery.beltSphere v).val).2) = x
    rw [hcoord]
    change euclideanTail n (d.radius⁻¹ • L (d.radius • (L.symm w.val))) = x
    rw [L.map_smul, L.apply_symm_apply, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
    exact euclideanTail_hemisphere Bool.true xB
  refine ⟨v, ?_⟩
  rintro ⟨y, hy⟩
  apply hxavoid
  refine ⟨y, ?_, ?_⟩
  · change g y ∈ d.chart.splitChart.source
    rw [hy]
    exact d.belt_mem_normalDomain v
  · change P (g y) = x
    rw [hy]
    exact hproject

theorem AdaptedWindows.exists_belt_point_reaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)] {a : ℝ} (hqa : f q < a)
    {d : ℕ}
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : d < n) :
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let K := MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  let G : K × V → M := fun z => g z.1 z.2
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ G :=
    MorseCancellation.contMDiff_discrete_family g hg
  have hrange : Set.range G = MorseCancellation.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancellation.range_discrete_family g
  obtain ⟨v, hv⟩ :=
    MorseCancellation.exists_belt_point_avoiding_smooth_image (S.data q) n G hG
      (show Module.finrank ℝ (Z × V) < n by
        simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim)
  have hforward := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
  obtain ⟨p, hp, _, _, hback, _, _⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct ((S.data q).surgery.beltSphere v).val
  have hap : a < f p :=
    lt_of_not_ge
      (fun h =>
        hv
          (hrange.symm ▸
            (show ((S.data q).surgery.beltSphere v).val ∈ MorseCancellation.backwardLowBasins S a from
              ⟨⟨p, hp⟩, h, hback⟩)))
  exact
    ⟨v,
      FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        hforward hap hqa⟩

theorem AdaptedWindows.joinedIn_level_minimum_basin_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    {a b : ℝ} (hpb : f p < b) (hba : b ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ q : ManifoldMorse.criticalPoints E f,
        f q ≤ a → MorseCancellation.nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxb : f x = b) (hyb : f y = b)
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val))
    (hxa : x ∈ FlowCancellation.levelBasin S.flow f a)
    (hya : y ∈ FlowCancellation.levelBasin S.flow f a) :
    JoinedIn
      {z : M |
        f z = b ∧
          Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
            z ∈ FlowCancellation.levelBasin S.flow f a}
      x y := by
  let _ := S.finite.fintype
  let K := MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancellation.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = MorseCancellation.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancellation.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange]
    exact MorseCancellation.isClosed_backwardLowBasins S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : z ∈ FlowCancellation.levelBasin S.flow f a) : z ∉ Set.range G := by
    rw [hrange]
    intro hlowz
    have hc : z ∈ (FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf ha]
      exact Or.inr hlowz
    exact hc hz
  let U : TopologicalSpace.Opens M :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)},
      S.isOpen_minimum_forward_basin hf p hp⟩
  let xU : U := ⟨x, hx⟩
  let yU : U := ⟨y, hy⟩
  have hjoined : Joined xU yU := (S.joinedIn_minimum_basin hf p hp hx hy).joined_subtype
  obtain ⟨η, -, havoid⟩ :=
    MorseCancellation.exists_smooth_path_avoiding_closed_image_in_open U hjoined.somePath G hG hclosed
      hdim' (hnot x hxa) (hnot y hya)
  have hcross (c : ℝ) (hbc : b ≤ c) (hca : c ≤ a) (u : unitInterval) :
    (η u).val ∈ FlowCancellation.levelBasin S.flow f c := by
    obtain ⟨q, hq, _, _, hback, _, _⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct (η u).val
    have hqa : a < f q :=
      lt_of_not_ge
        (fun h =>
          havoid u
            (hrange.symm ▸
              (show (η u).val ∈ MorseCancellation.backwardLowBasins S a from ⟨⟨q, hq⟩, h, hback⟩)))
    exact
      FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        (η u).property (hca.trans_lt hqa) (hpb.trans_le hbc)
  let _ := RegularLevel.chartedSpace hf hb
  let xL : { z : M // f z = b } := ⟨x, hxb⟩
  let yL : { z : M // f z = b } := ⟨y, hyb⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (continuous_subtype_val.comp η.continuous)
      (fun u => htarget.symm ▸ hcross b le_rfl hba u)
  have hlevelInverse (z : { w : M // f w = b }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y :=
    { toFun := fun u => (Φ.symm (η u).val).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_, ?_⟩⟩
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    have hlim : Filter.Tendsto (fun t => S.flow t (S.flow z.2 z.1.val)) Filter.atTop (𝓝 p.val) :=
      hflow.symm ▸ (η u).property
    exact (MorseCancellation.flow_time_atTop_limit_iff S.flow z.2 z.1.val p.val).mp hlim
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact
      (FlowCancellation.levelBasin_flow_iff S.flow f a z.2 z.1.val).mp
        (hflow.symm ▸ hcross a hba le_rfl u)

theorem AdaptedWindows.exists_belt_arc_closing_path_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hv : ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a)
    {d : ℕ}
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ,
      0 < r ∧
        r < 1 ∧
          (∀ s : ℝ,
              |s| ≤ r →
                MorseCancellation.nativeBeltArc S q u v s ∈
                  FlowCancellation.levelBasin S.flow f a) ∧
            (∀ s : ℝ,
                0 < |s| →
                  |s| ≤ r →
                    Filter.Tendsto (fun t => S.flow t (MorseCancellation.nativeBeltArc S q u v s))
                      Filter.atTop (𝓝 p.val)) ∧
              JoinedIn
                {z : M |
                  f z = S.toSurgeryWindows.upper q ∧
                    Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
                      z ∈ FlowCancellation.levelBasin S.flow f a}
                (MorseCancellation.nativeBeltArc S q u v r) (MorseCancellation.nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hmin⟩ :=
    S.exists_two_sided_belt_branch_in_minimum_basin hf p q hp u v hbranches
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f a) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (ha z hz))).1
  have hα0 :
    MorseCancellation.nativeBeltArc S q u v 0 ∈ FlowCancellation.levelBasin S.flow f a := by
    rw [MorseCancellation.nativeBeltArc_zero]
    exact hv
  have hc : ContinuousAt (MorseCancellation.nativeBeltArc S q u v) 0 :=
    ((MorseCancellation.nativeBeltArc_contMDiffOn S q u v).contMDiffAt
        (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num))).continuousAt
  have hnear :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      MorseCancellation.nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a :=
    hc.preimage_mem_nhds (hB.mem_nhds hα0)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  let r := Min.min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := hrε.trans_le hε1
  have hreach (s : ℝ) (hs : |s| ≤ r) :
    MorseCancellation.nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hs.trans_lt hrδ
  have hall (s : ℝ) (hs : 0 < |s|) (hsr : |s| ≤ r) :
    Filter.Tendsto (fun t => S.flow t (MorseCancellation.nativeBeltArc S q u v s)) Filter.atTop
      (𝓝 p.val) :=
    hmin s hs (hsr.trans_lt hrε)
  have hpb : f p < S.toSurgeryWindows.upper q :=
    (S.forward_limit_below_regular_level hf (S.data q).lower_regular
          ((S.data q).surgery.attachingSphere u) (hbranches u)).trans
      ((S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q))
  have hpr : |r| = r := abs_of_pos hr
  have hmr : |-r| = r := by rw [abs_neg, hpr]
  refine ⟨r, hr, hr1, hreach, hall, ?_⟩
  exact
    S.joinedIn_level_minimum_basin_reaching_level hf p hp hpb hba ha (S.data q).upper_regular hlow
      hdim (MorseCancellation.nativeBeltArc_height S q u v (by rw [hpr]; exact hr1.le))
      (MorseCancellation.nativeBeltArc_height S q u v (by rw [hmr]; exact hr1.le))
      (hall r (hpr.symm ▸ hr) hpr.le) (hall (-r) (hmr.symm ▸ hr) hmr.le) (hreach r hpr.le)
      (hreach (-r) hmr.le)

theorem MorseCancellation.single_belt_intersection_of_arc_and_minimum_range {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {X : Type*}
    {γ : X → (S.data q).UpperLevel} (hγi : Function.Injective γ) {z₀ : X}
    (hzero : γ z₀ = (S.data q).surgery.beltSphere v) {r : ℝ} (hr1 : r ≤ 1)
    (himage :
      ∀ z,
        γ z ∈ nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val)) :
    ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w := by
  intro z w
  constructor
  · intro hzw
    rcases himage z with hshort | hmin
    · obtain ⟨s, hs, hsz⟩ := hshort
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
        rw [← nativeBeltLevelArc_coe S q u v hs1]
        exact congrArg Subtype.val (hsz.trans hzw)
      obtain ⟨-, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
      refine ⟨hγi ?_, hvw⟩
      exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
    · have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
      rw [hzw] at hmin
      exact False.elim (hpq (Subtype.ext (tendsto_nhds_unique hmin hqz)))
  · rintro ⟨rfl, rfl⟩
    exact hzero

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_single_belt_circle_in_open_with_image {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hpq : p ≠ q) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : TopologicalSpace.Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Set.Icc (-r) r, MorseCancellation.nativeBeltArc S q u v s ∈ O)
    (hpath :
      JoinedIn
        {z : M |
          f z = S.toSurgeryWindows.upper q ∧
            Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧ z ∈ O}
        (MorseCancellation.nativeBeltArc S q u v r) (MorseCancellation.nativeBeltArc S q u v (-r)))
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
        Function.Injective γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
            (∀ z, (γ z).val ∈ O) ∧
              (∀ s ∈ Set.Icc (-r) r,
                  γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
                    MorseCancellation.nativeBeltLevelArc S q u v s) ∧
                (∀ z w,
                    γ z = (S.data q).surgery.beltSphere w ↔
                      z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w) ∧
                  ∀ z,
                    γ z ∈ MorseCancellation.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
                      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let α := MorseCancellation.nativeBeltLevelArc S q u v
  let U : TopologicalSpace.Opens (S.data q).UpperLevel :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val) ∧ z.val ∈ O},
      ((S.isOpen_minimum_forward_basin hf p hp).inter O.isOpen).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change Filter.Tendsto (fun t => S.flow t (α r).val) Filter.atTop (𝓝 p.val) ∧ (α r).val ∈ O
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v hpr]
    exact hpath.source_mem.2
  have hminus : α (-r) ∈ U := by
    change
      Filter.Tendsto (fun t => S.flow t (α (-r)).val) Filter.atTop (𝓝 p.val) ∧ (α (-r)).val ∈ O
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v hmr]
    exact hpath.target_mem.2
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) :=
    { toFun := fun t => ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩, (hpath.somePath_mem t).2⟩
      continuous_toFun := (hpath.somePath.continuous.subtype_mk _).subtype_mk _
      source' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.source.trans (MorseCancellation.nativeBeltLevelArc_coe S q u v hpr).symm))
      target' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.target.trans (MorseCancellation.nativeBeltLevelArc_coe S q u v hmr).symm)) }
  have hαi : Set.InjOn α (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    apply MorseCancellation.nativeBeltArc_injOn S q u v hx hy
    have hh := congrArg Subtype.val hxy
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v (abs_le.mpr hx),
      MorseCancellation.nativeBeltLevelArc_coe S q u v (abs_le.mpr hy)] at hh
    exact hh
  have hdimL : 3 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨γ, hγ, hγi, hγd, hshort, himage⟩ :=
    MorseCancellation.exists_embedded_circle_through_arc U hr hr1
      (MorseCancellation.nativeBeltLevelArc_contMDiffOn S hf q u v) hαi
      (fun _ hs => MorseCancellation.nativeBeltLevelArc_derivative_injective S hf q u v hs) hplus hminus
      η hdimL
  let z₀ := Circle.exp (2 * Real.pi / (2 * r + 1) * r)
  have hzero : γ z₀ = (S.data q).surgery.beltSphere v := by
    have hh := hshort 0 ⟨by linarith, hr.le⟩
    rw [zero_add] at hh
    apply Subtype.ext
    exact
      (congrArg Subtype.val hh).trans
        ((MorseCancellation.nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans
          (MorseCancellation.nativeBeltArc_zero S q u v))
  have himage' (z : Circle) :
    γ z ∈ MorseCancellation.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
    rcases himage (Set.mem_range_self z) with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  refine ⟨γ, hγ, hγi, hγd, ?_, hshort, ?_, himage'⟩
  · intro z
    rcases himage (Set.mem_range_self z) with hz | hz
    · obtain ⟨s, hs, hsz⟩ := hz
      rw [← hsz,
        MorseCancellation.nativeBeltLevelArc_coe S q u v
          (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
      exact hshortO s hs
    · exact hz.2
  · apply
      MorseCancellation.single_belt_intersection_of_arc_and_minimum_range S hf p q hpq u v hγi hzero
        hr1.le
    exact himage'

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_transverse_belt_circle_reaching_level_with_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hq : MorseCancellation.nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ d)
    (hdn : d < n) (hcut : 1 + d < Module.finrank ℝ E) (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ∃ γ : C(Circle, (S.data q).UpperLevel),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
          Function.Injective γ ∧
            (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
              (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f a) ∧
                ∃ z₀ : Circle,
                  (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
                    (Function.Surjective
                        ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
                              EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
                          (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
                            (S.data q).surgery.beltSphere v))) ∧
                      ∀ z,
                        Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
                          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  have hqa : f q < a := (S.toSurgeryWindows.value_lt_upper q).trans_le hba
  obtain ⟨v, hv⟩ := S.exists_belt_point_reaching_level hf q n hqa hlow hdn
  obtain ⟨r, hr, hr1, hreach, hmin, hpath⟩ :=
    S.exists_belt_arc_closing_path_reaching_level hf p q hp u v hbranches hba ha hv hlow hcut
  let O : TopologicalSpace.Opens M :=
    ⟨FlowCancellation.levelBasin S.flow f a,
      (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
          (fun z hz => S.descent z (ha z hz))).1⟩
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  obtain ⟨γ, hγ, hγi, hγd, hγreach, hshort, hsingle, himage⟩ :=
    S.exists_single_belt_circle_in_open_with_image hf p q hp hpq u v O hr hr1
      (fun s hs => hreach s (abs_le.mpr hs)) hpath hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] MorseCancellation.nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  have hendpoints (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
    rcases himage z with hshortz | hzmin
    · obtain ⟨s, hs, hsz⟩ := hshortz
      have hsr : |s| ≤ r := abs_le.mpr hs
      have hs1 : |s| ≤ 1 := hsr.trans hr1.le
      by_cases hs0 : s = 0
      · right
        have hz : (γ z).val = ((S.data q).surgery.beltSphere v).val := by
          rw [← hsz, MorseCancellation.nativeBeltLevelArc_coe S q u v hs1, hs0,
            MorseCancellation.nativeBeltArc_zero]
        rw [hz]
        exact (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
      · left
        rw [← hsz, MorseCancellation.nativeBeltLevelArc_coe S q u v hs1]
        exact hmin s (abs_pos.mpr hs0) hsr
    · exact Or.inl hzmin
  refine
    ⟨v, γ, hγ, hγi, hγd, hγreach, Circle.exp (2 * Real.pi / (2 * r + 1) * r), hsingle, ?_,
      hendpoints⟩
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v
  have hαtrans :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (MorseCancellation.nativeBeltLevelArc S q u v)
              0 :
            ℝ →L[ℝ] RegularLevel.Model E).coprod
        B) :=
    MorseCancellation.nativeBeltLevelArc_transverse S hf q hq n u v
  have ht :
    Function.Surjective
      ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (ψ 0) :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
        B) :=
    MorseCancellation.transverse_circle_of_arc_germ (D := EuclideanSpace ℝ (Fin n)) (J :=
      𝓘(ℝ, RegularLevel.Model E)) (α := MorseCancellation.nativeBeltLevelArc S q u v) (γ := γ)
      (ψ := ψ) hγ hψ heq B hαtrans
  have hp0 : ψ 0 = Circle.exp (2 * Real.pi / (2 * r + 1) * r) := by
    dsimp [ψ]
    rw [zero_add]
  rw [hp0] at ht
  exact ht

theorem AdaptedWindows.exists_native_level_basin_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ∃ D :
      PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { x : M // f x = a } { x : M // f x = b } ∞,
      D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
        D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
          ∀ x ∈ D.source, ∃ t : ℝ, S.flow t x.val = (D x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  let A := { x : M // f x = a }
  let B := { x : M // f x = b }
  obtain ⟨Φa, hsa, hta, hfa, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf ha S.smooth S.flow S.integral
      (fun x hx => S.descent x (ha x hx)) za
  obtain ⟨Φb, hsb, htb, hfb, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun x hx => S.descent x (hb x hx)) zb
  let U : Set A := {x | x.val ∈ FlowCancellation.levelBasin S.flow f b}
  let V : Set B := {x | x.val ∈ FlowCancellation.levelBasin S.flow f a}
  let P : A → B := fun x => (Φb.symm x.val).1
  let Q : B → A := fun y => (Φa.symm y.val).1
  have hU : IsOpen U := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f b) := htb ▸ Φb.open_target
    exact hh.preimage continuous_subtype_val
  have hV : IsOpen V := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f a) := hta ▸ Φa.open_target
    exact hh.preimage continuous_subtype_val
  have hPa (x : A) (t : ℝ) : Φa.symm (S.flow t x.val) = (x, t) := by
    have hs : (x, t) ∈ Φa.source := by rw [hsa]; trivial
    have hh : Φa.symm (Φa (x, t)) = (x, t) := Φa.left_inv' hs
    rwa [hfa] at hh
  have hPb (y : B) (t : ℝ) : Φb.symm (S.flow t y.val) = (y, t) := by
    have hs : (y, t) ∈ Φb.source := by rw [hsb]; trivial
    have hh : Φb.symm (Φb (y, t)) = (y, t) := Φb.left_inv' hs
    rwa [hfb] at hh
  have horbP (x : A) (hx : x ∈ U) : S.flow (-(Φb.symm x.val).2) x.val = (P x).val := by
    have hh : S.flow (Φb.symm x.val).2 (P x).val = x.val :=
      (hfb (Φb.symm x.val)).symm.trans (Φb.right_inv' (htb.symm ▸ hx))
    have hi := congrArg (S.flow (-(Φb.symm x.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have horbQ (y : B) (hy : y ∈ V) : S.flow (-(Φa.symm y.val).2) y.val = (Q y).val := by
    have hh : S.flow (Φa.symm y.val).2 (Q y).val = y.val :=
      (hfa (Φa.symm y.val)).symm.trans (Φa.right_inv' (hta.symm ▸ hy))
    have hi := congrArg (S.flow (-(Φa.symm y.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have hPU : Set.MapsTo P U V := by
    intro x hx
    have hxa : x.val ∈ FlowCancellation.levelBasin S.flow f a :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using x.property⟩
    change (P x).val ∈ FlowCancellation.levelBasin S.flow f a
    exact
      horbP x hx ▸
        (FlowCancellation.levelBasin_flow_iff S.flow f a (-(Φb.symm x.val).2) x.val).mpr
          hxa
  have hQV : Set.MapsTo Q V U := by
    intro y hy
    have hyb : y.val ∈ FlowCancellation.levelBasin S.flow f b :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using y.property⟩
    change (Q y).val ∈ FlowCancellation.levelBasin S.flow f b
    exact
      horbQ y hy ▸
        (FlowCancellation.levelBasin_flow_iff S.flow f b (-(Φa.symm y.val).2) y.val).mpr
          hyb
  have hQP (x : A) (hx : x ∈ U) : Q (P x) = x := by
    have hh := hPa x (-(Φb.symm x.val).2)
    rw [horbP x hx] at hh
    exact congrArg Prod.fst hh
  have hPQ (y : B) (hy : y ∈ V) : P (Q y) = y := by
    have hh := hPb y (-(Φa.symm y.val).2)
    rw [horbQ y hy] at hh
    exact congrArg Prod.fst hh
  have hPs :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ P U := by
    have hh :=
      Φb.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf ha).contMDiffOn
        (show Set.MapsTo (Subtype.val : A → M) U Φb.target from fun _ hx => htb.symm ▸ hx)
    exact contMDiff_fst.comp_contMDiffOn hh
  have hQs :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ Q V := by
    have hh :=
      Φa.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf hb).contMDiffOn
        (show Set.MapsTo (Subtype.val : B → M) V Φa.target from fun _ hy => hta.symm ▸ hy)
    exact contMDiff_fst.comp_contMDiffOn hh
  let D :
    PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) A B ∞ :=
    { toFun := P
      invFun := Q
      source := U
      target := V
      map_source' := hPU
      map_target' := hQV
      left_inv' := hQP
      right_inv' := hPQ
      open_source := hU
      open_target := hV
      contMDiffOn_toFun := hPs
      contMDiffOn_invFun := hQs }
  exact ⟨D, rfl, rfl, fun x hx => ⟨-(Φb.symm x.val).2, horbP x hx⟩⟩

theorem AdaptedWindows.belt_complement_reaches_lower_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (y : (S.data p).UpperLevel) (hy : y ∉ Set.range (S.data p).surgery.beltSphere) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hyreg : y.val ∉ ManifoldMorse.criticalPoints E f :=
    (S.data p).upper_regular y.val y.property
  have hbelow : f b < S.toSurgeryWindows.lower p := by
    rcases lt_trichotomy (f b) (f p) with h | h | h
    · exact (S.toSurgeryWindows.value_lt_upper ⟨b, hb⟩).trans (S.separated ⟨b, hb⟩ p h)
    · have heq : b = p.val := S.distinct hb p.property h
      subst b
      exact (hy ((S.belt_basin_iff hf p y).mp hforward)).elim
    · have hup : f y.val < f b := by
        rw [y.property]
        exact (S.separated p ⟨b, hb⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨b, hb⟩)
      exact (not_lt_of_ge hup.le (hheights hyreg).1).elim
  have hlow : S.toSurgeryWindows.lower p < f y.val := by
    rw [y.property]
    exact (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hlow.trans (hheights hyreg).2) hbelow

theorem AdaptedWindows.exists_belt_complement_lower_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨P, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hsrc (x : ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) :
    x.val ∈ P.source := hsource.symm ▸ S.belt_complement_reaches_lower_level hf p x.val x.property
  let D :
    C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel) :=
    ⟨fun x => P x.val,
      P.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc⟩
  refine ⟨D, fun x => horbit x.val (hsrc x), ?_⟩
  intro x y t hty
  obtain ⟨s, hs⟩ := horbit x.val (hsrc x)
  have hshared : S.flow 0 (D x).val = S.flow (s - t) y.val := by
    rw [S.flow.map_zero_apply]
    change (P x.val).val = S.flow (s - t) y.val
    rw [← hs, ← hty, ← S.flow.map_add, sub_add_cancel]
  apply Subtype.ext
  exact
    MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data p).lower_regular z hz)) (D x).property y.property hshared

def MorseCancellation.nativeUpperMeridianInComplement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (p : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    C(Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel))
    where
  toFun u := ⟨nativeUpperMeridian S p v s u, nativeUpperMeridian_avoids_belt S p v s hs u⟩
  continuous_toFun := (nativeUpperMeridian S p v s).continuous.subtype_mk _

theorem MorseCancellation.lower_transport_upperMeridian_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (p : ManifoldMorse.criticalPoints E f)
    (D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel))
    (hD : ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    D.comp (nativeUpperMeridianInComplement S p v s hs) = nativeLowerMeridian S p v s := by
  apply ContinuousMap.ext
  intro u
  exact
    hD (nativeUpperMeridianInComplement S p v s hs u) (nativeLowerMeridian S p v s u)
      (BeltPassage.time s) (nativeUpperMeridian_flow S p v s hs u)

theorem AdaptedWindows.exists_lower_transport_with_meridians {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          ∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
            (hs : 0 < (s : ℝ)),
            (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
              (S.data p).surgery.attachingSphere := by
  obtain ⟨D, horbit, hunique⟩ := S.exists_belt_complement_lower_transport hf p u v
  refine ⟨D, horbit, hunique, ?_⟩
  intro w s hs
  rw [MorseCancellation.lower_transport_upperMeridian_eq S p D hunique w s hs]
  exact MorseCancellation.nativeLowerMeridian_homotopic_attaching S p w s

theorem AdaptedWindows.exists_lower_passage_homology_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (H : C(ℝ × Hemisphere.Sphere 2, (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : Hemisphere.Sphere 2)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : Hemisphere.Sphere 2,
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          (∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
              (hs : 0 < (s : ℝ)),
              (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
                (S.data p).surgery.attachingSphere) ∧
            let G :=
              D.comp
                (PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            (∀ z : ({(τ, x₀)}ᶜ : Set (ℝ × Hemisphere.Sphere 2)),
                z.val.1 ∈ Set.Icc (0 : ℝ) 1 → ∃ t : ℝ, S.flow t (H z.val).val = (G z).val) ∧
              ∀ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
                SingularMayerVietoris.singularHomologyMap
                    (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
                  SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                    SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 := by
  obtain ⟨D, horbit, hunique, hmeridian⟩ := S.exists_lower_transport_with_meridians hf p u v
  refine ⟨D, horbit, hunique, hmeridian, ?_, ?_⟩
  · intro z hz
    have hh :=
      horbit
        (PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere)
          hτ x₀ hcross z)
    rw [PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross z hz] at hh
    exact hh
  · intro ε hε hεx
    exact
      PassageHomology.punctured_cylinder_trace_relation hτ x₀ hε hεx
        (D.comp
          (PassageHomology.puncturedPassageTrace H
            (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross))
        2 (by decide)

theorem PuncturedRadial.toSphere_fromSphere {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : N) 1) :
    toSphere (fromSphere r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : N)‖⁻¹ • (r • (u : N)) = (u : N)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    inv_smul_smul₀ hr.ne']

def PuncturedRadial.deformation {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : (ContinuousMap.id (Space N)).Homotopy ((fromSphere r hr).comp toSphere)
    where
  toFun q := ⟨blendVector r q, blendVector_ne_zero r hr q⟩
  continuous_toFun := (continuous_blendVector r).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blendVector, fromSphere, toSphere, RadialExtension.direction, div_eq_mul_inv,
      smul_smul]

def PuncturedRadial.sphereHomotopyEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ Space N
    where
  toFun := fromSphere r hr
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp (fromSphere r hr) = ContinuousMap.id (Metric.sphere (0 : N) 1) :=
      ContinuousMap.ext (toSphere_fromSphere r hr)
    rw [heq]
  right_inv := ⟨(deformation r hr).symm⟩

def LocalDegree.linearSphereEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : E) 1 ≃ₕ PuncturedRadial.Space F :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans
    (puncturedLinearHomeomorph L).toHomotopyEquiv

def LocalDegree.BoundaryData.normalizedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp b.map

def MorseCancellation.radialParameterChart (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) (EuclideanSpace ℝ (Fin 3))
      (ℝ × (Hemisphere.Sphere 2)) ∞ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let b := PassageHomology.cylinderPuncture τ u
  let T : Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toEquiv :=
        { toFun := fun z => b + z
          invFun := fun z => z - b
          left_inv := fun z => add_sub_cancel_left b z
          right_inv := by intro z; simp }
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact
    T.toPartialDiffeomorph.trans
      (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm

theorem MorseCancellation.radialParameterChart_zero_mem_source (τ : ℝ)
    (u : (Hemisphere.Sphere 2)) :
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ (radialParameterChart τ u).source := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Set.univ ∧
      PassageHomology.cylinderPuncture τ u + 0 ∈
        (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).target
  rw [add_zero, PassageHomology.radialCylinderChart_mem_target]
  exact
    ⟨Set.mem_univ _,
      norm_pos_iff.mp
        (by rw [PassageHomology.norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

theorem MorseCancellation.radialParameterChart_zero (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm
        (PassageHomology.cylinderPuncture τ u + 0) =
      (τ, u)
  rw [add_zero]
  have heq :
    PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u (τ, u) =
      PassageHomology.cylinderPuncture τ u :=
    rfl
  rw [← heq]
  exact
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).left_inv
      (PassageHomology.radialCylinderChart_mem_source (EuclideanSpace ℝ (Fin 3)) 2 u
        (τ, u))

theorem MorseCancellation.radialParameterChart_apply (τ : ℝ) (u : (Hemisphere.Sphere 2))
    (z : (EuclideanSpace ℝ (Fin 3))) (hz : PassageHomology.cylinderPuncture τ u + z ≠ 0) :
    radialParameterChart τ u z =
      (PassageHomology.radialCylinderHomeomorph (EuclideanSpace ℝ (Fin 3))).symm
        ⟨PassageHomology.cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact
    PassageHomology.radialCylinderChart_symm_eq (EuclideanSpace ℝ (Fin 3)) 2 u
      (PassageHomology.cylinderPuncture τ u + z) hz

theorem MorseCancellation.radialParameterChart_link (τ : ℝ) (u : (Hemisphere.Sphere 2)) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u (ε • w.val) =
      (PassageHomology.cylinderLink τ u ε hε hεu w).val := by
  have hz : PassageHomology.cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (PassageHomology.linkingSphere (PassageHomology.cylinderPuncture τ u) ε hε
          (by rwa [PassageHomology.norm_cylinderPuncture]) w).property.1
  exact radialParameterChart_apply τ u (ε • w.val) hz

end
