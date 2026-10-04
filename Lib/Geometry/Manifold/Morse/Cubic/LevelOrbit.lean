/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.Cubic.SublevelFlow
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Orbits of a vector field crossing a level set

The derivative `x ↦ df_x (V x)` of a smooth function `f` along a smooth vector field `V` on a
manifold is smooth (`MorseCancellation.contMDiff_directionalDerivative`).  If it is negative on the
level set `f = c`, an orbit of the flow of `V` meets that level in at most one point
(`MorseCancellation.native_same_level_orbit_points`); cf. Milnor, *Morse Theory*, §3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- For a smooth function `f` and a smooth vector field `V` on a manifold `M`, the directional
derivative `x ↦ mvfderiv 𝓘(ℝ, E) f x (V x)` is smooth. -/
theorem MorseCancellation.contMDiff_directionalDerivative {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

/-- Let `f` and the vector field `V` be smooth, `F` a flow whose orbits are integral curves of `V`,
and suppose the derivative of `f` along `V` is negative on the level `f = c`. Then two points `x`,
`y` of that level on a common orbit (`F s x = F t y`) are equal. -/
theorem MorseCancellation.native_same_level_orbit_points {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x y : M} {s t : ℝ} (hx : f x = c)
    (hy : f y = c) (hxy : F s x = F t y) : x = y := by
  have hmove : F (s - t) x = y := by
    calc
      F (s - t) x = F (-t) (F s x) := by
        rw [← F.map_add]
        congr 1
        ring
      _ = F (-t) (F t y) := (congrArg (F (-t)) hxy)
      _ = y := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have htime :=
    FlowCancellation.flow_level_time_unique F hf.continuous
      (contMDiff_directionalDerivative hf hV).continuous
      (fun z u => FlowConstruction.hasDerivAt_comp_integralCurve hf (hF z) u) hboundary x
      (hmove ▸ hy) (show f (F 0 x) = c by rw [F.map_zero_apply]; exact hx)
  simpa only [htime, F.map_zero_apply] using hmove
