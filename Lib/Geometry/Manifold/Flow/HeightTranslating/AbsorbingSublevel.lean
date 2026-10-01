/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime
public import Lib.Geometry.Manifold.Flow.HeightTranslating.FlowCollar
public import Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow

/-!
# Absorbing sets of a descent flow and the sublevel they retract

Let `f` be a smooth function on a compact manifold, `V` a smooth field with `df (V) < 0` off the
critical points, and `F` its flow, with `f` antitone along the orbits. On a compact set without
critical points `df (V)` is bounded above by a negative constant, so no orbit stays in it longer
than a uniform time. Consequently, if a closed set `A` with
`{f ≤ a} ⊆ A ⊆ {f ≤ b}` contains in its interior all critical points with values in `[a, b]`,
every point of `{f ≤ b}` enters `A` within a uniform time. If moreover `A` is forward invariant
and strictly absorbing, then `A` is a deformation retract of `{f ≤ b}`, and (if also `f`
strictly decreases off the level `b`) homeomorphic to it along the orbits. With
`A = {f ≤ a}` this is Milnor, *Morse Theory*, Theorem 3.1; with `A` a sublevel with a handle
attached it is the deformation in the proof of Theorem 3.2.

## Main results

* `FlowConstruction.exists_uniform_negative_speed`,
  `FlowConstruction.exists_uniform_residence_bound` : the uniform speed and residence time on a
  compact set of regular points.
* `FlowConstruction.exists_uniform_criticalNeighborhood_entry`,
  `FlowConstruction.exists_uniform_absorbing_entry` : uniform entry times.
* `FlowConstruction.exists_absorbingSublevelHomotopyEquiv` : a homotopy equivalence
  `A ≃ₕ {x // f x ≤ b}` whose underlying map is the inclusion.
* `FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits` : a homeomorphism
  `{x // f x ≤ b} ≃ₜ A` matching the frontiers along the orbits of `F`.

## References

* [John Milnor, *Morse Theory*][milnor63], §3, Theorems 3.1 and 3.2

## Tags

sublevel set, deformation retract, descent flow, absorbing set
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### Uniform absorption -/

/-- A uniform negative descent speed exists on a compact regular set. -/
theorem FlowConstruction.exists_uniform_negative_speed {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ δ > (0 : ℝ), ∀ x ∈ K, mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_mvfderiv_field hf hV).continuousOn
    refine ⟨-mvfderiv 𝓘(ℝ, E) f p (V p), neg_pos.mpr (hdesc p (hreg hp)), ?_⟩
    intro x hx
    have hle : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f p (V p) := hmax hx
    simpa only [neg_neg] using hle
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- A uniform residence bound in a regular band exists. -/
theorem FlowConstruction.exists_uniform_residence_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ T > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ K := by
  by_cases hne : K.Nonempty
  · obtain ⟨δ, hδ, hspeed⟩ := exists_uniform_negative_speed hf hV hdesc hK hreg
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuous.continuousOn
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hf.continuous.continuousOn
    let T := (f q - f p + 1) / δ
    have hpq : f p ≤ f q := hmax hp
    have hgap : 0 < f q - f p + 1 := by linarith
    have hT : 0 < T := div_pos hgap hδ
    have hδT : δ * T = f q - f p + 1 := by
      dsimp [T]
      field_simp [hδ.ne']
    refine ⟨T, hT, ?_⟩
    intro γ hγ
    by_contra! hstay
    have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
      hasDerivAt_comp_integralCurve hf hγ t
    have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
    have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
    have hlast : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
    have hbound :=
      (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
        hdiff.differentiableOn
        (fun t ht => by
          rw [(hd t).deriv]
          exact hspeed (γ t) (hstay t (interior_subset ht)))
        0 hzero T hlast hT.le
    simp only [Function.comp_apply, sub_zero, neg_mul] at hbound
    rw [hδT] at hbound
    have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
    have hhi : f (γ 0) ≤ f q := hmax (hstay 0 hzero)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro γ _
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩

/-- A uniform entry time into critical neighborhoods exists. -/
theorem FlowConstruction.exists_uniform_criticalNeighborhood_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {U : Set M} (hU : IsOpen U)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ U) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) < a ∨ F t x ∈ U := by
  let K := f ⁻¹' Set.Icc a b ∩ Uᶜ
  have hK : IsCompact K :=
    ((isClosed_Icc.preimage hf.continuous).inter hU.isClosed_compl).isCompact
  have hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    exact hx.2 (hcover x hcrit hx.1)
  obtain ⟨T, hT, hexit⟩ := exists_uniform_residence_bound hf hV hdesc hK hreg
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hout⟩ := hexit (fun s => F s x) (hcurve x)
  have hupper : f (F t x) ≤ b := by
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  refine ⟨t, ht, ?_⟩
  by_cases hlow : f (F t x) < a
  · exact Or.inl hlow
  · right
    by_contra hnot
    exact hout ⟨⟨le_of_not_gt hlow, hupper⟩, hnot⟩

/-- A uniform entry time into an absorbing set exists. -/
theorem FlowConstruction.exists_uniform_absorbing_entry {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M}
    (hlower : {x | f x ≤ a} ⊆ A)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc 0 T, F t x ∈ A := by
  obtain ⟨T, hT, hentry⟩ :=
    exists_uniform_criticalNeighborhood_entry hf hV hdesc F hcurve hmono isOpen_interior hcover
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hlow | hint⟩ := hentry x hx
  · exact ⟨t, ht, hlower (show f (F t x) ≤ a from le_of_lt hlow)⟩
  · exact ⟨t, ht, interior_subset hint⟩

/-- An absorbing sublevel is a deformation retract. -/
theorem FlowConstruction.exists_absorbingSublevelHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) :
    ∃ e : A ≃ₕ { x : M // f x ≤ b }, ∀ x, (e x).1 = x.1 := by
  obtain ⟨T, _, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hfinite : ∀ x ∈ {x | f x ≤ b}, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A := by
    intro x hx
    obtain ⟨t, ht, hm⟩ := hhit x hx
    exact ⟨t, ht.1, hm⟩
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hle.trans hx
  exact ⟨entryHomotopyEquiv F hA hforward hentry hfinite hupper hregion, fun _ => rfl⟩

/-! ### The sublevel homeomorphism -/

/-- An absorbing sublevel homeomorphism with boundary orbit control exists. -/
theorem FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    ∃ e : { x : M // f x ≤ b } ≃ₜ A,
      (∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b}) ∧
        (∀ x, x.val ∈ A → x.val ∈ frontier {y : M | f y ≤ b} → (e x).val = x.val) ∧
          (∀ y,
            y.val ∈ frontier A →
              ∀ t : ℝ,
                t ≤ 0 → F t y.val ∈ frontier {x : M | f x ≤ b} → (e.symm y).val = F t y.val) := by
  obtain ⟨T, hT, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hh.trans hx
  have hstrict : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 < t → F t x ∈ interior {x | f x ≤ b} := by
    intro x hx t ht
    change f x ≤ b at hx
    apply
      interior_maximal
        (show {x | f x < b} ⊆ {x | f x ≤ b} from fun x (hy : f x < b) =>
          (show f x ≤ b from hy.le))
        (isOpen_lt hf.continuous continuous_const)
    rcases lt_or_eq_of_le hx with hlt | heq
    · have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.le
      exact hh.trans_lt hlt
    · exact htop x heq t ht
  let d : FlowCollarData F A {x | f x ≤ b} :=
    { time := T + 1
      time_pos := by linarith
      closed_outer := isClosed_le hf.continuous continuous_const
      closed_inner := hA
      inner_subset := hupper
      forward_outer := hregion
      forward_inner := hforward
      strict_outer := hstrict
      strict_inner := hentry
      core_inside := by
        intro x hx
        obtain ⟨t, ht, hmem⟩ := hhit x hx
        have hh := hentry _ hmem (T + 1 - t) (by linarith [ht.2])
        rwa [← F.map_add, sub_add_cancel] at hh }
  have : CompactSpace ↥({x : M | f x ≤ b}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact
    ⟨d.homeomorph, d.homeomorph_mem_frontier_iff, d.homeomorph_fixed_on_common_frontier,
      fun y hy _ ht hfront => d.homeomorph_symm_eq_flow_of_mem_frontier y hy ht hfront⟩
