/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime
public import Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow
public import Lib.Geometry.Manifold.Flow.HeightTranslating.AbsorbingSublevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment.DescentModel

/-!
# A sublevel with a handle attached is a deformation retract of the next sublevel

Let `p` be a critical point of `f` on a compact manifold, `c` a signed Morse chart at `p`, and
`ρ > 0` small enough for the handle `c.attachingHandleMap ρ` to be defined. If a descent field
`V` of `f` agrees with `c.descentField` near the handle, the *attaching union*
`{f ≤ f p - ρ²} ∪ range (c.attachingHandleMap ρ)` is forward invariant under the flow of `V`
and is moved into its interior in positive time. If moreover `p` is the only critical point
with value in `[f p - ρ², f p + ρ²]`, the attaching union is a deformation retract of
`{f ≤ f p + ρ²}`: cf. Milnor, *Morse Theory*, Theorem 3.2 (crossing a critical level attaches a
cell), here with a handle and a homotopy equivalence whose underlying map is the inclusion.

## Main results

* `ManifoldMorse.SignedMorseChart.exists_local_attachingUnion_entry` : near a chart point of
  the attaching union the flow enters its interior for small positive times.
* `ManifoldMorse.SignedMorseChart.forwardInvariant_attachingUnion`,
  `ManifoldMorse.SignedMorseChart.interior_entry_attachingUnion` : forward invariance and strict
  absorption of the attaching union.
* `ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv` : the homotopy
  equivalence with `{x // f x ≤ f p + ρ ^ 2}`.

## References

* [John Milnor, *Morse Theory*][milnor63], §3, Theorem 3.2

## Tags

Morse theory, handle attachment, deformation retract
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### The attaching union is absorbing -/

attribute [local instance 100] Classical.propDecidable in
/-- The flow enters the attaching union locally. -/
theorem ManifoldMorse.SignedMorseChart.exists_local_attachingUnion_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {x : M} (hx : x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hAx : x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :
    ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioc 0 ε,
        F t x ∈
          interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hmodel := (c.mem_attachingUnion_iff_model ρ hρ hblock hx).mp hAx
  have hαc : Continuous (fun t : ℝ => MorseHandle.descentFlow t (c.splitChart x)) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : MorseHandle.descentFlow 0 (c.splitChart x) = e x :=
    MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), MorseHandle.descentFlow t (c.splitChart x) ∈ e.target :=
    hαc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hFc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), F t x ∈ e.source :=
    hFc.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds
        (by
          rw [F.map_zero_apply]
          exact hx))
  have heqF := c.eventually_flow_eq_descentModel hV F hcurve hx heq
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp ((heqF.and htarget).and hsource)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  have hdist : Dist.dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  obtain ⟨⟨heqt, htar⟩, hsrc⟩ := hεall hdist
  apply c.mem_interior_attachingUnion_of_model ρ hρ hblock hsrc
  have hcoord : c.splitChart (F t x) = MorseHandle.descentFlow t (c.splitChart x) := by
    rw [heqt]
    exact e.right_inv htar
  rw [hcoord]
  exact MorseHandle.descentFlow_mem_interior_lower_union_handle hρ ht.1 hmodel

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is forward invariant. -/
theorem ManifoldMorse.SignedMorseChart.forwardInvariant_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 ≤ t → F t x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) := by
  apply
    FlowConstruction.forwardInvariant_of_local F
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    left
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (MorseHandle.modelMap_mem_product hρ z))
    obtain ⟨ε, hε, hentry⟩ :=
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero, F.map_zero_apply]
      exact Or.inr hx
    · exact interior_subset (hentry t ⟨hpos, ht.2⟩)

attribute [local instance 100] Classical.propDecidable in
/-- The flow enters the attaching union's interior. -/
theorem ManifoldMorse.SignedMorseChart.interior_entry_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 < t →
          F t x ∈
            interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  apply
    FlowConstruction.interior_entry_of_local F
      (c.forwardInvariant_attachingUnion hf hV F hcurve hmono ρ hρ hblock hagreement)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hlow : f (F t x) < f p - ρ ^ 2 := by
      change f x ≤ f p - ρ ^ 2 at hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1.le
        exact hle.trans_lt hlt
      · exact (hbottom x heq t ht.1).trans_le hx
    apply mem_interior.mpr
    exact
      ⟨{y | f y < f p - ρ ^ 2}, fun y hy => Or.inl (show f y ≤ f p - ρ ^ 2 from le_of_lt hy),
        isOpen_lt hf continuous_const, hlow⟩
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (MorseHandle.modelMap_mem_product hρ z))
    exact
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)

/-! ### The deformation retraction -/

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is a deformation retract of the sublevel. -/
theorem ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₕ
        { x : M // f x ≤ f p + ρ ^ 2 },
      ∀ x, (e x).1 = x.1 := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x := by
    intro x hx t ht
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp : x = p := hband x hcrit ⟨hx.ge, by rw [hx]; linarith [sq_nonneg ρ]⟩
      rw [hxp] at hx
      nlinarith [sq_pos_of_pos hρ]
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  apply
    FlowConstruction.exists_absorbingSublevelHomotopyEquiv hf hV hdesc F hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
  · intro x hcrit hx
    have hxp := hband x hcrit hx
    subst x
    exact
      interior_mono Set.subset_union_right (c.mem_interior_range_attachingHandleMap ρ hρ hblock)
  · exact
      c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
  · exact
      c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom
