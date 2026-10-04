/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.PartialDiffeomorph
public import Lib.Geometry.Manifold.Morse.CriticalPoints
public import Lib.Analysis.Calculus.MorseLemma.MorseChart

/-!
# Signed Morse charts on a manifold

`ManifoldMorse.SignedMorseChart f x` bundles a partial diffeomorphism from a neighbourhood of
`x` to `ℝ^n` centered at `x` with weights `w i ∈ {-1, 1}` such that
`f = f x + ∑ i, w i * y i ^ 2` in these coordinates. Every critical point of a smooth Morse
function has one (`ManifoldMorse.nonempty_signedMorseChart`): the Morse lemma on a manifold
(Milnor, *Morse Theory*, Lemma 2.2).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- A signed Morse chart: a chart in which the function is a signed quadratic form. -/
structure ManifoldMorse.SignedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (x : M) where
  /-- The coefficients `w i` of the squares, indexed by `Fin (finrank ℝ E)`. -/
  weights : Fin (Module.finrank ℝ E) → ℝ
  /-- Every weight is `-1` or `1`. -/
  signs : ∀ i, weights i = -1 ∨ weights i = 1
  /-- The chart, a partial diffeomorphism from `M` to `ℝ^(finrank ℝ E)`. -/
  chart :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) M (Fin (Module.finrank ℝ E) → ℝ)
      ∞
  /-- The point `x` lies in the chart's source. -/
  mem_source : x ∈ chart.source
  /-- The chart sends `x` to `0`. -/
  center : chart x = 0
  /-- On the source, `f y = f x + ∑ i, w i * (chart y i) ^ 2`. -/
  equation : ∀ y ∈ chart.source, f y = f x + ∑ i, weights i * (chart y i) ^ 2
  /-- On the target, `f (chart.symm y) = f x + ∑ i, w i * y i ^ 2`. -/
  inverse_equation : ∀ y ∈ chart.target, f (chart.symm y) = f x + ∑ i, weights i * y i ^ 2

/-- A signed Morse chart exists near a Morse critical point. -/
theorem ManifoldMorse.nonempty_signedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (x : M)
    (hx : x ∈ criticalPoints E f) : Nonempty (SignedMorseChart (E := E) f x) := by
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc := (mem_criticalPoints_iff hf he hxS).mp hx
    obtain ⟨w, hw, d, hdx, -, hd₀, hdeq, hdinv⟩ :=
      SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn (contDiffOn_chartExpression hf he)
        e.open_target (e x) (e.map_source hxS) hc hH
    let c := (chartPartialDiffeomorph e he).trans d
    refine ⟨⟨w, hw, c, ⟨hxS, hdx⟩, hd₀, ?_, ?_⟩⟩
    · intro y hy
      have hyS : y ∈ e.source := hy.1
      have hyd : e y ∈ d.source := hy.2
      change f y = f x + ∑ i, w i * (d (e y) i) ^ 2
      simpa only [Function.comp_apply, e.left_inv hyS, e.left_inv hxS] using hdeq (e y) hyd
    · intro y hy
      have hyd : y ∈ d.target := hy.1
      change f (e.symm (d.symm y)) = f x + ∑ i, w i * y i ^ 2
      simpa only [Function.comp_apply, e.left_inv hxS] using hdinv y hyd
