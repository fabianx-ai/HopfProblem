/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms
import Lib.Geometry.Manifold.Morse.Cancellation.BandHeight

/-!
# Replacing a Morse function on a band

`FlowCancellation.bandReplacement f g c d` is `g` on `f ⁻¹' (Ioo c d)` and `f`
elsewhere. When `g` is smooth on an open set containing the closed band and has
the germ of `f` on the two boundary levels, the replacement is smooth and has
the germ of `f` off the open band and the germ of `g` on the closed band
(`contMDiff_bandReplacement`, `bandReplacement_germ_on_closed`,
`bandReplacement_germ_off_open`).

Applied to the band height of `Morse.Cancellation.BandHeight`, this gives a
global smooth function decreasing along `V` on the band and equal to `f` off it
(`exists_global_band_lyapunov`). If the band contains exactly the two critical
points `p ≠ q` of a Morse function `f`, the replacement is a Morse function
whose critical set is that of `f` minus `{p, q}` (`remove_morse_band_pair`).

This is the final step of Milnor, *Lectures on the h-cobordism theorem*,
Theorem 5.4: once the gradient-like field has no zero in the band, the function
is modified there to have no critical point.

## Tags

morse-theory, cancellation, level-set
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Band replacement -/

/-- The band replacement of a function. -/
def FlowCancellation.bandReplacement {X : Type*} (f g : X → ℝ) (c d : ℝ) (x : X) : ℝ := by
  classical exact if f x ∈ Set.Ioo c d then g x else f x

/-- The band replacement's germ on the boundary. -/
theorem FlowCancellation.bandReplacement_germ_boundary {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} {x : X} (heq : g =ᶠ[𝓝 x] f) :
    bandReplacement f g c d =ᶠ[𝓝 x] f ∧ bandReplacement f g c d =ᶠ[𝓝 x] g := by
  have hh : bandReplacement f g c d =ᶠ[𝓝 x] f := by
    filter_upwards [heq] with y hy
    simp only [bandReplacement, hy, ite_self]
  exact ⟨hh, hh.trans heq.symm⟩

/-- The band replacement's germ in the interior. -/
theorem FlowCancellation.bandReplacement_germ_interior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∈ Set.Ioo c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_Ioo.preimage hf).mem_nhds hx] with y hy
  exact if_pos hy

/-- The band replacement's germ in the exterior. -/
theorem FlowCancellation.bandReplacement_germ_exterior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∉ Set.Icc c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] f := by
  filter_upwards [((isClosed_Icc.preimage hf).isOpen_compl).mem_nhds hx] with y hy
  exact if_neg (fun h => hy ⟨h.1.le, h.2.le⟩)

/-- The band replacement's germ on a closed set. -/
theorem FlowCancellation.bandReplacement_germ_on_closed {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∈ Set.Icc c d) : bandReplacement f g c d =ᶠ[𝓝 x] g := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).2
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).2
  exact
    bandReplacement_germ_interior hf ⟨lt_of_le_of_ne hx.1 (Ne.symm hc), lt_of_le_of_ne hx.2 hd⟩

/-- The band replacement's germ off an open set. -/
theorem FlowCancellation.bandReplacement_germ_off_open {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∉ Set.Ioo c d) : bandReplacement f g c d =ᶠ[𝓝 x] f := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).1
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).1
  apply bandReplacement_germ_exterior hf
  intro h
  exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hc), lt_of_le_of_ne h.2 hd⟩

/-- The band replacement is smooth. -/
theorem FlowCancellation.contMDiff_bandReplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {c d : ℝ} {U : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (hU : IsOpen U)
    (hband : f ⁻¹' Set.Icc c d ⊆ U) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (bandReplacement f g c d) := by
  intro x
  by_cases hx : f x ∈ Set.Icc c d
  · exact
      ((hg x (hband hx)).contMDiffAt (hU.mem_nhds (hband hx))).congr_of_eventuallyEq
        (bandReplacement_germ_on_closed hf.continuous hboundary hx)
  · exact hf.contMDiffAt.congr_of_eventuallyEq (bandReplacement_germ_exterior hf.continuous hx)

/-- Equal germs give equal manifold derivatives. -/
theorem FlowCancellation.mvfderiv_eq_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f g : M → ℝ} {x : M} (heq : f =ᶠ[𝓝 x] g) :
    mvfderiv 𝓘(ℝ, E) f x (V x) = mvfderiv 𝓘(ℝ, E) g x (V x) := by
  unfold mvfderiv
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

/-- A global band Lyapunov function exists. -/
theorem FlowCancellation.exists_global_band_lyapunov {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ b : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
        (∀ x, f x ∈ Set.Icc c d → mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          ∀ x, f x ∉ Set.Ioo c d → b =ᶠ[𝓝 x] f := by
  obtain ⟨U, g, hU, hband, hg, hgneg, hgerm⟩ :=
    exists_smooth_band_height_germs hf hV F hcurve hcd hc hd hcross
  refine ⟨bandReplacement f g c d, contMDiff_bandReplacement hf hg hU hband hgerm, ?_, ?_⟩
  · intro x hx
    rw [mvfderiv_eq_of_germ (V := V) (bandReplacement_germ_on_closed hf.continuous hgerm hx)]
    exact hgneg x (hband hx)
  · intro x hx
    exact bandReplacement_germ_off_open hf.continuous hgerm hx

/-! ### Removing the pair -/

/-- A negative directional derivative excludes criticality. -/
theorem FlowCancellation.not_critical_of_directional_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {g : M → ℝ} {x : M}
    (hneg : mvfderiv 𝓘(ℝ, E) g x (V x) < 0) : x ∉ ManifoldMorse.criticalPoints E g := by
  intro hx
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 at hx
  unfold mvfderiv at hneg
  rw [hx] at hneg
  simp at hneg

/-- The band replacement removes the Morse pair. -/
theorem FlowCancellation.remove_morse_band_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x))
    {p q : M} (hpq : p ≠ q) (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpc : f p ∈ Set.Icc c d)
    (hqc : f q ∈ Set.Icc c d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hneg, hgerm⟩ := exists_global_band_lyapunov hf hV F hcurve hcd hc hd hcross
  have hreg (x : M) (hx : f x ∈ Set.Icc c d) : x ∉ ManifoldMorse.criticalPoints E g :=
    not_critical_of_directional_neg (hneg x hx)
  have hnew (x : M) :
    x ∈ ManifoldMorse.criticalPoints E g ↔
      x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q := by
    constructor
    · intro hx
      have hout : f x ∉ Set.Icc c d := fun h => hreg x h hx
      have he := hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)
      have hcrit : x ∈ ManifoldMorse.criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
        rw [← he.mfderiv_eq]
        exact hx
      exact ⟨hcrit, fun h => hout (h ▸ hpc), fun h => hout (h ▸ hqc)⟩
    · rintro ⟨hx, hxp, hxq⟩
      have hout : f x ∉ Set.Icc c d := fun h => (hpair x hx h).elim hxp hxq
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [(hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)).mfderiv_eq]
      exact hx
  have hmg : ManifoldMorse.IsMorse E g := by
    apply MorseCancellationPreservation.isMorse_of_critical_germs hm hg
    intro x hx
    apply hgerm x
    intro h
    exact hreg x ⟨h.1.le, h.2.le⟩ hx
  have heq :
    ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f \ { p, q } := by
    ext x
    simpa only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hnew x
  have hsub : { p, q } ⊆ ManifoldMorse.criticalPoints E f := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact Set.mem_singleton_iff.mp hx ▸ hq
  refine ⟨g, hg, hmg, ?_, hnew, hgerm⟩
  rw [heq, ← Set.ncard_pair hpq]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub (ManifoldMorse.finite_criticalPoints hf hm)

end
