/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.Cubic.BasinBlock
public import Lib.Geometry.Manifold.Morse.Cubic.LevelOrbit
public import Lib.Geometry.Manifold.Morse.Cubic.AlignedRays
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The attaching sphere and the belt sphere as level sets of the basins

For a field `V` with flow `F` that is the model descent field in the block of radius `2r` of a
signed Morse chart at `p`, and which crosses the level `f = f p - r²` strictly downwards, a point
`x` of that level satisfies `F t x → p` as `t → -∞` iff it lies on the attaching sphere of radius
`r` (`MorseCancellation.native_attaching_core_basin_iff`); dually, on the level `f = f p + r²` the
points with `F t x → p` as `t → ∞` are exactly the belt sphere
(`MorseCancellation.native_belt_core_basin_iff`).  These are the left-hand and right-hand spheres
`S_L`, `S_R` of Milnor, *Lectures on the h-cobordism theorem*, §3, described as
traces of the unstable and stable manifolds.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The backward basin meets the attaching core. -/
theorem MorseCancellation.native_backward_basin_mem_attaching_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    ∃ u : PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_outgoing_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).1‖) Filter.atBot (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_le_atBot T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).1 ≠ 0 := fun hz => hnonzero (Prod.ext hz (hplane s hs))
  obtain ⟨u, t, ht, hu⟩ := exists_negative_core_ray_parameter hr hn hsmall
  have hmodel :
    MorseHandle.descentFlow t
        (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · exact hu
    · change Real.exp (-t) • (0 : c.PositiveCoordinates) = (c.splitChart (F s x)).2
      rw [smul_zero, hplane s hs]
  have hcore := native_attaching_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.attachingCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary
        (c.attachingCoreMap r hr hblock u).property hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core is the backward basin. -/
theorem MorseCancellation.native_attaching_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔
      ∃ u : PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock u : M) = x := by
  constructor
  · exact
      native_backward_basin_mem_attaching_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_attaching_core_backward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
/-- The forward basin meets the belt core. -/
theorem MorseCancellation.native_forward_basin_mem_belt_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_incoming_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).2‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_ge_atTop T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).2 ≠ 0 := fun hz => hnonzero (Prod.ext (hplane s hs) hz)
  obtain ⟨u, t, ht, hu⟩ := exists_positive_core_ray_parameter hr hn hsmall
  have hmodel :
    MorseHandle.descentFlow t
        ((0 : c.NegativeCoordinates), r • (u : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · change Real.exp t • (0 : c.NegativeCoordinates) = (c.splitChart (F s x)).1
      rw [smul_zero, hplane s hs]
    · exact hu
  have hcore := native_belt_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.beltCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary (c.beltCoreMap r hr hblock u).property
        hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
/-- The belt core is the forward basin. -/
theorem MorseCancellation.native_belt_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔
      ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock u : M) = x := by
  constructor
  · exact native_forward_basin_mem_belt_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_belt_core_forward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u
