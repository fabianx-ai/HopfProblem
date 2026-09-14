/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Geometry.Manifold.Morse.Cancellation

/-!
# Rearrangement without a connecting orbit

`MorseRearrangement.exists_morse_rearrangement_of_no_connection` changes the
values at an isolated pair of critical points of an excellent Morse function
on a compact connected smooth manifold, when no descending orbit connects
the upper point to the lower point. It preserves the critical set, all Morse
indices, strict descent of the given field away from the critical set, and
the function germ outside the chosen band. The two new values may be chosen
arbitrarily inside that band.

## Outline of the proof

1. Compare level basins through orbit-preserving band bridges and prove
   compactness of their invariant sections.
2. Extend a cylinder plateau weight to a stationary pair weight
   (`MorseRearrangement.exists_stationary_pair_weight`).
3. Blend the height with the prescribed constant translations
   (`exists_rearranged_morse_function_of_stationary_weight`).
4. Use the absence of a connecting orbit to obtain the weight and transport
   the Morse indices through the resulting constant-shift germs.

## Main definitions and results

* `MorseRearrangement.exists_stationary_pair_weight`.
* `MorseRearrangement.exists_morse_rearrangement_of_no_connection`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.1.

## Tags

morse-theory, rearrangement, critical-values
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Shifting critical values -/

/-- A signed Morse chart of `f + k` obtained by shifting the chart height. -/
def MorseCancellation.shiftedSignedMorseChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    ManifoldMorse.SignedMorseChart (E := E) (fun x => f x + k) p
    where
  weights := c.weights
  signs := c.signs
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation x hx := by rw [c.equation x hx]; ring
  inverse_equation z hz := by rw [c.inverse_equation z hz]; ring

/-- Adding a constant preserves the Morse property. -/
theorem MorseCancellation.isMorseAt_add_const {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : ManifoldMorse.IsMorseAt E f p) (k : ℝ) :
    ManifoldMorse.IsMorseAt E (fun x => f x + k) p := by
  obtain ⟨e, he, hp, hgood⟩ := hm
  have hd : fderiv ℝ ((fun x => f x + k) ∘ e.symm) = fderiv ℝ (f ∘ e.symm) := by
    funext z
    exact fderiv_add_const k
  refine ⟨e, he, hp, ?_⟩
  rw [hd]
  exact hgood

/-- A function agreeing with `f + k` near `p` is Morse at `p`. -/
theorem MorseCancellation.isMorseAt_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hm : ManifoldMorse.IsMorseAt E f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ManifoldMorse.IsMorseAt E g p :=
  MorseCancellationPreservation.isMorseAt_of_same_germ (isMorseAt_add_const hm k) hgerm

/-- Adding a constant preserves the Morse index. -/
theorem MorseCancellation.nativeMorseIndex_add_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    nativeMorseIndex E (fun x => f x + k) p = nativeMorseIndex E f p := by
  rw [nativeMorseIndex_eq_chart (shiftedSignedMorseChart c k), nativeMorseIndex_eq_chart c]
  rfl

/-- A function with an `f + k` germ has the same Morse index. -/
theorem MorseCancellation.nativeMorseIndex_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) : nativeMorseIndex E g p = nativeMorseIndex E f p :=
  (nativeMorseIndex_congr_germ hgerm).trans (nativeMorseIndex_add_const c k)

/-- Functions differing by a constant germ have equal derivatives. -/
theorem MorseCancellation.mfderiv_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p := by
  calc
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun x => f x + k) p : E →L[ℝ] ℝ) := hgerm.mfderiv_eq
    _ = _ := by
      have hs : mvfderiv 𝓘(ℝ, E) (fun x => f x + k) p = mvfderiv 𝓘(ℝ, E) f p := by
        rw [mvfderiv_fun_add hf mdifferentiableAt_const, mvfderiv_const, add_zero]
      exact hs

/-! ### Basins across regular bands -/

/-- An orbit-bridging map between levels identifies their basins. -/
theorem FlowCancellation.levelBasin_eq_of_orbit_level_bridge {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ) (a b : ℝ) (D : X → X)
    (hlevel : D '' {x | f x = a} = {x | f x = b}) (horbit : ∀ x, ∃ t, F t x = D x) :
    levelBasin F f a = levelBasin F f b := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := horbit (F s x)
    have hDy : f (D (F s x)) = b := by
      have hh : D (F s x) ∈ D '' {y | f y = a} := Set.mem_image_of_mem D hs
      rw [hlevel] at hh
      exact hh
    exact ⟨t + s, by rw [F.map_add, ht]; exact hDy⟩
  · rintro ⟨s, hs⟩
    have hy : F s x ∈ D '' {y | f y = a} := by rw [hlevel]; exact hs
    obtain ⟨y, hy, heq⟩ := hy
    change f y = a at hy
    obtain ⟨t, ht⟩ := horbit y
    have hyB : y ∈ levelBasin F f a := ⟨0, by simpa only [F.map_zero_apply] using hy⟩
    have hh := (levelBasin_flow_iff F f a t y).mpr hyB
    rw [ht, heq] at hh
    exact (levelBasin_flow_iff F f a s x).mp hh

/-- The two boundary levels of a regular band have the same flow basin under the stated descending-flow hypotheses. -/
theorem FlowCancellation.levelBasin_eq_of_regular_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    levelBasin F f a = levelBasin F f b := by
  obtain ⟨D, hlevel, -, horbit⟩ :=
    FlowTimeChange.exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  exact levelBasin_eq_of_orbit_level_bridge F f a b D hlevel horbit

/-- An orbit-matching homeomorphism of sections carries the locus of a flow-invariant predicate on one section to its locus on the other. -/
theorem MorseCancellation.image_flow_invariant_section {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    e '' {x | P (ι x)} = {y | P (κ y)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := horbit x
    have hh := (hP t (ι x)).mpr hx
    rwa [ht] at hh
  · intro hy
    obtain ⟨t, ht⟩ := horbit (e.symm y)
    have heq : e (e.symm y) = y := e.apply_symm_apply y
    rw [heq] at ht
    refine ⟨e.symm y, ?_, heq⟩
    apply (hP t (ι (e.symm y))).mp
    rwa [ht]

/-- Compactness of a flow-invariant section. -/
theorem MorseCancellation.isCompact_flow_invariant_section_iff {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {y : B | P (κ y)} ↔ IsCompact {x : A | P (ι x)} := by
  rw [← image_flow_invariant_section F e ι κ horbit hP]
  exact e.isCompact_image

attribute [local instance 100] Classical.propDecidable in
/-- Under the Morse-block and strict boundary-descent hypotheses, the forward basin of the critical point has a compact section in the level `f p + r²`. -/
theorem MorseCancellation.isCompact_native_belt_basin {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} =
      Set.range (c.beltCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_belt_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.beltCoreMap r hr hblock).continuous

attribute [local instance 100] Classical.propDecidable in
/-- Under the Morse-block and strict boundary-descent hypotheses, the backward basin of the critical point has a compact section in the level `f p - r²`. -/
theorem MorseCancellation.isCompact_native_attaching_basin {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} =
      Set.range (c.attachingCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_attaching_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.attachingCoreMap r hr hblock).continuous

/-- Compactness of flow-invariant sections transfers across a regular band. -/
theorem FlowCancellation.isCompact_invariant_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) {P : M → Prop}
    (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {x : { y : M // f y = b } | P (x : M)} ↔
      IsCompact {x : { y : M // f y = a } | P (x : M)} := by
  have ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
  have hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨D, e, -, he, horbit⟩ :=
    FlowTimeChange.exists_orbit_preserving_native_band_bridge hf hV hdesc F hF hab hband ha
      hb
  apply
    MorseCancellation.isCompact_flow_invariant_section_iff F e.toHomeomorph Subtype.val Subtype.val _ hP
  intro x
  obtain ⟨t, ht⟩ := horbit x
  exact ⟨t, ht.trans (he x).symm⟩

/-- Compactness of forward-basin sections transfers across a regular band. -/
theorem FlowCancellation.isCompact_forward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (fun t x => MorseCancellation.flow_time_atTop_limit_iff F t x p)

/-- Compactness of backward-basin sections transfers across a regular band. -/
theorem FlowCancellation.isCompact_backward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (fun t x => MorseCancellation.flow_time_atBot_limit_iff F t x p)

/-! ### Cylinder weights -/

/-- Pull a function on the transverse label space back along the first component of the inverse cylinder chart. -/
def MorseRearrangement.nativeCylinderWeight {Z H N E M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H} [TopologicalSpace N]
    [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (θ : N → ℝ)
    (x : M) : ℝ :=
  θ (A.symm x).1

/-- The cylinder weight is smooth where the weight function is. -/
theorem MorseRearrangement.contMDiffOn_nativeCylinderWeight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (nativeCylinderWeight A θ) A.target :=
  hθ.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn A.contMDiffOn_invFun)

/-- The cylinder weight stays in `[0, 1]` when `θ` does. -/
theorem MorseRearrangement.nativeCylinderWeight_mem_Icc {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ∀ z, θ z ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    nativeCylinderWeight A θ x ∈ Set.Icc (0 : ℝ) 1 :=
  hθ _

/-- Flow lines read off in cylinder coordinates. -/
theorem MorseRearrangement.native_cylinder_flow_coordinates {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) {x : M} (hx : x ∈ A.target)
    (t : ℝ) : A.symm (F t x) = ((A.symm x).1, t + (A.symm x).2) := by
  have hright : A (A.symm x) = x := A.right_inv' hx
  have hexpr : F t x = A ((A.symm x).1, t + (A.symm x).2) := by
    calc
      F t x = F t (A (A.symm x)) := congrArg (F t) hright.symm
      _ = F (t + (A.symm x).2) (ι (A.symm x).1) := by rw [hformula, ← F.map_add]
      _ = A ((A.symm x).1, t + (A.symm x).2) := (hformula ((A.symm x).1, t + (A.symm x).2)).symm
  rw [hexpr]
  exact A.left_inv' (by rw [hsource]; trivial)

/-- The cylinder weight is invariant along the flow. -/
theorem MorseRearrangement.nativeCylinderWeight_flow {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) (θ : N → ℝ) {x : M}
    (hx : x ∈ A.target) (t : ℝ) : nativeCylinderWeight A θ (F t x) = nativeCylinderWeight A θ x :=
  by
  unfold nativeCylinderWeight
  rw [native_cylinder_flow_coordinates A hsource F ι hformula hx t]

/-- For a flow cylinder over a compact smooth label manifold, construct a smooth invariant weight in `[0, 1]` with zero and one germs over two disjoint closed label sets. -/
theorem MorseRearrangement.exists_native_cylinder_plateau_weight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace H]
    {I : ModelWithCorners ℝ Z H} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [T2Space N] [CompactSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = Set.univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1)) {S₀ S₁ : Set N} (hS₀ : IsClosed S₀) (hS₁ : IsClosed S₁)
    (hdisj : Disjoint S₀ S₁) :
    ∃ w : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w A.target ∧
        (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x ∈ A.target, ∀ t, w (F t x) = w x) ∧
            (∀ x ∈ A.target, (A.symm x).1 ∈ S₀ → w =ᶠ[𝓝 x] fun _ => 0) ∧
              (∀ x ∈ A.target, (A.symm x).1 ∈ S₁ → w =ᶠ[𝓝 x] fun _ => 1) := by
  obtain ⟨θ, hθ₀, hθ₁, hθrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hS₀ hS₁ hdisj (n := ⊤)
  refine
    ⟨nativeCylinderWeight A θ, contMDiffOn_nativeCylinderWeight A θ.contMDiff,
      nativeCylinderWeight_mem_Icc A hθrange, fun x hx t =>
      nativeCylinderWeight_flow A hsource F ι hformula θ hx t, ?_, ?_⟩
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 0 := hθ₀.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 1 := hθ₁.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint

/-! ### Basin weights near endpoints -/

attribute [local instance 100] Classical.propDecidable in
/-- Near the belt the positive coordinate is eventually nonzero on the upper basin. -/
theorem MorseCancellation.eventually_nonzero_positive_coordinate_on_upper_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : f p < a) :
    ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → (c.splitChart x).2 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_negative_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.1 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).ge_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
/-- The negative coordinate is eventually nonzero on the lower basin. -/
theorem MorseCancellation.eventually_nonzero_negative_coordinate_on_lower_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : a < f p) :
    ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → (c.splitChart x).1 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_positive_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.2 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).le_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
/-- The basin weight is eventually constant on the belt neighborhood. -/
theorem MorseCancellation.eventually_constant_basin_weight_of_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
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
    {a k : ℝ} (ha : f p < a) {w : M → ℝ}
    (hinv : ∀ x ∈ FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p + r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_positive_coordinate_on_upper_level_basin c hf hV F hF hmono
      heq ha,
    eventually_backward_exit_in_belt_neighborhood c hV F hF hr hblock hfield hU hcore] with x hne
    hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

attribute [local instance 100] Classical.propDecidable in
/-- The basin weight is eventually constant on the attaching neighborhood. -/
theorem MorseCancellation.eventually_constant_basin_weight_of_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
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
    {a k : ℝ} (ha : a < f p) {w : M → ℝ}
    (hinv : ∀ x ∈ FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p - r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_negative_coordinate_on_lower_level_basin c hf hV F hF hmono
      heq ha,
    eventually_forward_exit_in_attaching_neighborhood c hV F hF hr hblock hfield hU hcore] with x
    hne hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

/-! ### Extended basin weights -/

/-- Off the basin the flow stays on the same side of the level. -/
theorem MorseRearrangement.height_side_of_not_levelBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a : ℝ} {x : X}
    (hx : x ∉ FlowCancellation.levelBasin F f a) (t : ℝ) : f (F t x) < a ↔ f x < a := by
  have hc : Continuous (fun s : ℝ => f (F s x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  have hside (s u : ℝ) (hs : f (F s x) < a) : f (F u x) < a := by
    by_contra hu
    obtain ⟨v, hv⟩ :=
      intermediate_value_univ s u hc
        (show a ∈ Set.Icc (f (F s x)) (f (F u x)) from ⟨hs.le, le_of_not_gt hu⟩)
    exact hx ⟨v, hv⟩
  constructor
  · intro ht
    simpa only [F.map_zero_apply] using hside t 0 ht
  · intro hx
    exact hside 0 t (by simpa only [F.map_zero_apply] using hx)

attribute [local instance 100] Classical.propDecidable in
/-- The basin weight extended by flow transport across the band. -/
def MorseRearrangement.extendedBasinWeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  if x ∈ FlowCancellation.levelBasin F f a then w x else if f x < a then 1 else 0

/-- The extended basin weight computes the basin weight. -/
theorem MorseRearrangement.extendedBasinWeight_eq {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ) {x : X}
    (hx : x ∈ FlowCancellation.levelBasin F f a) : extendedBasinWeight F f a w x = w x := by
  classical simp only [extendedBasinWeight, if_pos hx]

/-- The extended basin weight under the flow. -/
theorem MorseRearrangement.extendedBasinWeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) (a : ℝ) (w : X → ℝ)
    (hinv : ∀ x ∈ FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) (x : X)
    (t : ℝ) : extendedBasinWeight F f a w (F t x) = extendedBasinWeight F f a w x := by
  classical
  by_cases hx : x ∈ FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _
        ((FlowCancellation.levelBasin_flow_iff F f a t x).mpr hx),
      extendedBasinWeight_eq _ _ _ _ hx]
    exact hinv x hx t
  · have htx : F t x ∉ FlowCancellation.levelBasin F f a := fun h =>
      hx ((FlowCancellation.levelBasin_flow_iff F f a t x).mp h)
    simp only [extendedBasinWeight, if_neg hx, if_neg htx,
      height_side_of_not_levelBasin F hf hx t]

/-- Extending a basin weight preserves its values in `[0, 1]` when the original weight has that range on the level basin. -/
theorem MorseRearrangement.extendedBasinWeight_mem_Icc {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ)
    (hw : ∀ x ∈ FlowCancellation.levelBasin F f a, w x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    extendedBasinWeight F f a w x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _ hx]
    exact hw x hx
  · simp only [extendedBasinWeight, if_neg hx]
    split_ifs <;> norm_num

/-- The extended weight's germ at the lower level. -/
theorem MorseRearrangement.extendedBasinWeight_lower_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : f p < a)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = 1) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, f x < a := hf (eventually_lt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_pos hfx]

/-- The extended weight's germ at the upper level. -/
theorem MorseRearrangement.extendedBasinWeight_upper_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : a < f p)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = 0) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 0 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, a < f x := hf (eventually_gt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_neg (not_lt_of_gt hfx)]

/-- An endpoint limit gives a constant germ. -/
theorem MorseRearrangement.constant_germ_of_endpoint_limit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {w : X → ℝ} (hinv : ∀ x t, w (F t x) = w x) {p x : X} {k : ℝ} {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p))
    (hgerm : w =ᶠ[𝓝 p] fun _ => k) : w =ᶠ[𝓝 x] fun _ => k := by
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_eventually_nhds.mpr hgerm)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (hinv y t).symm.trans hy

/-- The pair band's basin complement. -/
theorem MorseRearrangement.pair_band_basin_complement {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : X} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q) {x : X} (hx : f x ∈ Set.Icc l u)
    (hnot : x ∉ FlowCancellation.levelBasin F f a) :
    (f x < a ∧ Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) ∨
      (a < f x ∧ Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) := by
  obtain ⟨r, hr, s, hs, hrlim, hslim, -⟩ :=
    FlowCancellation.exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f r)) :=
    hf.continuousAt.tendsto.comp hrlim
  have hsheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f s)) :=
    hf.continuousAt.tendsto.comp hslim
  by_cases hxa : f x < a
  · have hrle : f r ≤ a :=
      isClosed_Iic.mem_of_tendsto hrheight
        (Filter.Eventually.of_forall
          (fun t => ((height_side_of_not_levelBasin F hf hnot t).mpr hxa).le))
    have hxr : f x ≤ f r := by
      simpa only [F.map_zero_apply] using (hmono x).ge_of_tendsto hrheight 0
    have hrp : r = p :=
      (hpair r hr ⟨hx.1.trans hxr, hrle.trans hau.le⟩).resolve_right
        (by
          intro heq
          rw [heq] at hrle
          exact (not_le_of_gt hq) hrle)
    exact Or.inl ⟨hxa, by simpa only [hrp] using hrlim⟩
  · have hneq : f x ≠ a := fun heq => hnot ⟨0, by simpa only [F.map_zero_apply] using heq⟩
    have hax : a < f x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hneq)
    have hsge : a ≤ f s :=
      isClosed_Ici.mem_of_tendsto hsheight
        (Filter.Eventually.of_forall
          (fun t =>
            le_of_not_gt (fun ht => hxa ((height_side_of_not_levelBasin F hf hnot t).mp ht))))
    have hsx : f s ≤ f x := by
      simpa only [F.map_zero_apply] using (hmono x).le_of_tendsto hsheight 0
    have hsq : s = q :=
      (hpair s hs ⟨hla.le.trans hsge, hsx.trans hx.2⟩).resolve_left
        (by
          intro heq
          rw [heq] at hsge
          exact (not_le_of_gt hp) hsge)
    exact Or.inr ⟨hax, by simpa only [hsq] using hslim⟩

/-- The extended basin weight is smooth on the pair band. -/
theorem MorseRearrangement.contMDiffOn_extendedBasinWeight_pair_band {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] (F : Flow ℝ M) {f : M → ℝ}
    (hf : Continuous f) {S : Set M} (hinj : Set.InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : M} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hB : IsOpen (FlowCancellation.levelBasin F f a)) {w : M → ℝ}
    (hw : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ w (FlowCancellation.levelBasin F f a))
    (hstationary : ∀ x ∈ FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    (hpw : ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = 1)
    (hqw : ∀ᶠ x in 𝓝 q, x ∈ FlowCancellation.levelBasin F f a → w x = 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (extendedBasinWeight F f a w) (f ⁻¹' Set.Icc l u) := by
  have hpgerm := extendedBasinWeight_lower_germ F hf.continuousAt hp hpw
  have hqgerm := extendedBasinWeight_upper_germ F hf.continuousAt hq hqw
  have hinvariant (x : M) (t : ℝ) := extendedBasinWeight_flow F hf a w hstationary x t
  intro x hx
  by_cases hxB : x ∈ FlowCancellation.levelBasin F f a
  · have heq : extendedBasinWeight F f a w =ᶠ[𝓝 x] w := by
      filter_upwards [hB.mem_nhds hxB] with y hy
      exact extendedBasinWeight_eq F f a w hy
    exact (((hw x hxB).contMDiffAt (hB.mem_nhds hxB)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · rcases pair_band_basin_complement F hf hinj hmono hstrict hla hau hp hq hpair hx hxB with
      ⟨-, hlim⟩ | ⟨-, hlim⟩
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hpgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hqgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

attribute [local instance 100] Classical.propDecidable in
/-- A stationary pair weight exists. -/
theorem MorseRearrangement.exists_stationary_pair_weight {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) {rp rq l a u : ℝ} (hrp : 0 < rp)
    (hrq : 0 < rq) (hla : l < a) (hau : a < u)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hbp :
      Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
          Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp) ⊆
        cp.splitChart.target)
    (hbq :
      Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
          Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq) ⊆
        cq.splitChart.target)
    (hfp :
      ∀
        z ∈
          Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
            Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp),
        ∀ᶠ y in 𝓝 (cp.splitChart.symm z), V y = cp.descentField y)
    (hfq :
      ∀
        z ∈
          Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
            Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq),
        ∀ᶠ y in 𝓝 (cq.splitChart.symm z), V y = cq.descentField y)
    (hpa : f p + rp ^ 2 ≤ a) (haq : a ≤ f q - rq ^ 2)
    (hbandp : ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ ManifoldMorse.criticalPoints E f)
    (hbandq : ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ ManifoldMorse.criticalPoints E f)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ W : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ W (f ⁻¹' Set.Icc l u) ∧
        (∀ x, W x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x t, W (F t x) = W x) ∧ (W =ᶠ[𝓝 p] fun _ => 1) ∧ (W =ᶠ[𝓝 q] fun _ => 0) := by
  have hpa' : f p < a := by nlinarith [sq_pos_of_pos hrp]
  have haq' : a < f q := by nlinarith [sq_pos_of_pos hrq]
  have hreg : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hbandp x (by rw [hx]; exact ⟨hpa, le_rfl⟩)
  have hboundp : ∀ x, f x = f p + rp ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandp x (by rw [hx]; exact ⟨le_rfl, hpa⟩))
  have hboundq : ∀ x, f x = f q - rq ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandq x (by rw [hx]; exact ⟨haq, le_rfl⟩))
  let L := { x : M // f x = a }
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let S₀ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 q)}
  let S₁ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)}
  have hS₁ : IsCompact S₁ :=
    (FlowCancellation.isCompact_forward_section_iff_of_regular_band hf hV hdesc F hF hpa
          hbandp p).mpr
      (MorseCancellation.isCompact_native_belt_basin cp hf hV F hF rp hrp hbp hfp hboundp)
  have hS₀ : IsCompact S₀ :=
    (FlowCancellation.isCompact_backward_section_iff_of_regular_band hf hV hdesc F hF haq
          hbandq q).mp
      (MorseCancellation.isCompact_native_attaching_basin cq hf hV F hF rq hrq hbq hfq hboundq)
  have hdisj : Disjoint S₀ S₁ :=
    Set.disjoint_left.mpr (fun x hx₀ hx₁ => hnoconnection x ⟨hx₀, hx₁⟩)
  obtain ⟨z, hz⟩ := intermediate_value_univ p q hf.continuous ⟨hpa'.le, haq'.le⟩
  obtain ⟨A, hAsource, hAtarget, hAformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg hV F hF
      (fun x hx => hdesc x (hreg x hx)) (⟨z, hz⟩ : L)
  obtain ⟨w, hw, hwrange, hwinv, hw₀, hw₁⟩ :=
    exists_native_cylinder_plateau_weight A hAsource F Subtype.val hAformula hS₀.isClosed
      hS₁.isClosed hdisj
  have hmono := FlowConstruction.antitone_flow_height hf F hF hzero hdesc
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hbasinp :=
    FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF hpa hbandp
  have hbasinq :=
    FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF haq hbandq
  have hcorep (v : PuncturedHandle.UnitSphere cp.PositiveCoordinates) :
    w =ᶠ[𝓝 (cp.beltCoreMap rp hrp hbp v : M)] fun _ => 1 := by
    let x : M := cp.beltCoreMap rp hrp hbp v
    have hx : x ∈ A.target := by
      rw [hAtarget, ← hbasinp]
      exact ⟨0, by simpa only [F.map_zero_apply] using (cp.beltCoreMap rp hrp hbp v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₁ x hx
    have hh := MorseCancellation.native_belt_core_forward_limit cp hV₁ F hF rp hrp hbp hfp v
    apply (MorseCancellation.flow_time_atTop_limit_iff F (A.symm x).2 ((A.symm x).1 : M) p).mp
    rw [hmap]
    exact hh
  have hcoreq (v : PuncturedHandle.UnitSphere cq.NegativeCoordinates) :
    w =ᶠ[𝓝 (cq.attachingCoreMap rq hrq hbq v : M)] fun _ => 0 := by
    let x : M := cq.attachingCoreMap rq hrq hbq v
    have hx : x ∈ A.target := by
      rw [hAtarget, hbasinq]
      exact
        ⟨0, by simpa only [F.map_zero_apply] using (cq.attachingCoreMap rq hrq hbq v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₀ x hx
    have hh := MorseCancellation.native_attaching_core_backward_limit cq hV₁ F hF rq hrq hbq hfq v
    apply (MorseCancellation.flow_time_atBot_limit_iff F (A.symm x).2 ((A.symm x).1 : M) q).mp
    rw [hmap]
    exact hh
  have hstationary : ∀ x ∈ FlowCancellation.levelBasin F f a, ∀ t, w (F t x) = w x := by
    simpa only [hAtarget] using hwinv
  have hpw : ∀ᶠ x in 𝓝 p, x ∈ FlowCancellation.levelBasin F f a → w x = 1 :=
    MorseCancellation.eventually_constant_basin_weight_of_belt_neighborhood cp hf.continuous hV₁ F hF
      hmono hrp hbp hfp hpa' hstationary (U := interior {x | w x = 1}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcorep v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 1}) hx)
  have hqw : ∀ᶠ x in 𝓝 q, x ∈ FlowCancellation.levelBasin F f a → w x = 0 :=
    MorseCancellation.eventually_constant_basin_weight_of_attaching_neighborhood cq hf.continuous hV₁ F
      hF hmono hrq hbq hfq haq' hstationary (U := interior {x | w x = 0}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcoreq v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 0}) hx)
  have hB : IsOpen (FlowCancellation.levelBasin F f a) := hAtarget ▸ A.open_target
  have hwB : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w (FlowCancellation.levelBasin F f a) :=
    hAtarget ▸ hw
  refine
    ⟨extendedBasinWeight F f a w, ?_, extendedBasinWeight_mem_Icc F f a w (fun x _ => hwrange x),
      extendedBasinWeight_flow F hf.continuous a w hstationary,
      extendedBasinWeight_lower_germ F hf.continuous.continuousAt hpa' hpw,
      extendedBasinWeight_upper_germ F hf.continuous.continuousAt haq' hqw⟩
  exact
    contMDiffOn_extendedBasinWeight_pair_band F hf.continuous hinj hmono
      (fun x hx => FlowConstruction.strictAnti_flow_height hf hV₁ F hF hzero hdesc hx) hla
      hau hpa' haq' hpair hB hwB hstationary hpw hqw

/-! ### Blended heights and rearrangement -/

attribute [local instance 100] Classical.propDecidable in
/-- A small Morse-field block exists around a signed Morse chart. -/
theorem MorseCancellation.exists_small_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ,
      0 < r ∧
        r ^ 2 < ε ∧
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
              c.splitChart.target ∧
            ∀
              z ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
              ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  obtain ⟨R, hR, hblock, hfield⟩ := exists_native_morse_field_block c heq
  obtain ⟨r, hr, hsmall⟩ :=
    exists_between (lt_min (half_pos hR) (lt_min hε (by norm_num : (0 : ℝ) < 1)))
  have h2r : 2 * r ≤ R := by linarith [hsmall.trans_le (min_le_left _ _)]
  have hrε : r < ε := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hr2 : r ^ 2 < ε := lt_trans (by nlinarith : r ^ 2 < r) hrε
  have hsub :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) R :=
    fun z hz =>
    ⟨Metric.closedBall_subset_closedBall h2r hz.1, Metric.closedBall_subset_closedBall h2r hz.2⟩
  exact ⟨r, hr, hr2, hsub.trans hblock, fun z hz => hfield z (hsub hz)⟩

/-- Outside the blend interval the blended height agrees with `f`. -/
theorem MorseRearrangement.blended_height_exterior_germ {M : Type*} [TopologicalSpace M]
    {f θ : M → ℝ} {P Q : ℝ → ℝ} {l u : ℝ} (hf : Continuous f)
    (hP : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id) (hQ : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) {x : M}
    (hx : f x ∉ Set.Ioo l u) : (fun y => blendHeight (θ y) P Q (f y)) =ᶠ[𝓝 x] f := by
  filter_upwards [hf.continuousAt.tendsto.eventually (hP _ hx),
    hf.continuousAt.tendsto.eventually (hQ _ hx)] with y hyP hyQ
  exact blendHeight_fixed hyP hyQ _

/-- The globally blended height is smooth. -/
theorem MorseRearrangement.contMDiff_globally_blended_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} {l u : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u)) (hP : ContDiff ℝ ∞ P)
    (hQ : ContDiff ℝ ∞ Q) (hPfix : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id)
    (hQfix : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)) := by
  intro x
  by_cases hx : f x ∈ Set.Ioo l u
  · have hnhds : f ⁻¹' Set.Icc l u ∈ 𝓝 x :=
      Filter.mem_of_superset ((isOpen_Ioo.preimage hf.continuous).mem_nhds hx)
        (fun _ hy => ⟨hy.1.le, hy.2.le⟩)
    have hw := (hθ x ⟨hx.1.le, hx.2.le⟩).contMDiffAt hnhds
    exact
      (hw.mul (hP.contMDiff.contMDiffAt.comp x (hf x))).add
        ((contMDiffAt_const.sub hw).mul (hQ.contMDiff.contMDiffAt.comp x (hf x)))
  · exact (hf x).congr_of_eventuallyEq (blended_height_exterior_germ hf.continuous hPfix hQfix hx)

/-- At weight one the blend is the `P` translation germ. -/
theorem MorseRearrangement.blended_height_one_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 1) (hP : P =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hP] with x hx hPx
  rw [hx, blendHeight_one]
  exact hPx

/-- At weight zero the blend is the `Q` translation germ. -/
theorem MorseRearrangement.blended_height_zero_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 0) (hQ : Q =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hQ] with x hx hQx
  rw [hx, blendHeight_zero]
  exact hQx

/-- The directional derivative of the blended height along the field. -/
theorem MorseRearrangement.blended_height_directional_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)))
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (hθ : ∀ x t, θ (F t x) = θ x)
    (x : M) :
    mvfderiv 𝓘(ℝ, E) (fun y => blendHeight (θ y) P Q (f y)) x (V x) =
      (θ x * deriv P (f x) + (1 - θ x) * deriv Q (f x)) * mvfderiv 𝓘(ℝ, E) f x (V x) := by
  have hw : HasDerivAt (fun t => θ (F t x)) 0 0 := by
    have heq : (fun t => θ (F t x)) = fun _ => θ x := funext (hθ x)
    rw [heq]
    exact hasDerivAt_const _ _
  have hdf := FlowConstruction.hasDerivAt_comp_integralCurve hf (hF x) 0
  have hdg := FlowConstruction.hasDerivAt_comp_integralCurve hg (hF x) 0
  have hh := hasDerivAt_blended_height hdf hw (hP _).hasDerivAt (hQ _).hasDerivAt
  have heq := hdg.unique hh
  have hdf0 := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  have hdg0 :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) y (V y))
      (F.map_zero_apply x)
  change
    mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) (F 0 x) (V (F 0 x)) =
      (θ (F 0 x) * deriv P (f (F 0 x)) + (1 - θ (F 0 x)) * deriv Q (f (F 0 x))) *
        mvfderiv 𝓘(ℝ, E) f (F 0 x) (V (F 0 x)) at heq
  rw [hdg0, hdf0, F.map_zero_apply] at heq
  exact heq

/-- A stationary weight gives a rearranged Morse function blending the translations. -/
theorem MorseRearrangement.exists_rearranged_morse_function_of_stationary_weight
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f θ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p q : M} {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Ioo l u → x = p ∨ x = q)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u))
    (hθrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) (hθinv : ∀ x t, θ (F t x) = θ x)
    (hpgerm : θ =ᶠ[𝓝 p] fun _ => 1) (hqgerm : θ =ᶠ[𝓝 q] fun _ => 0) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k) := by
  obtain ⟨P, -, hPtrans, -, -, hPpos, hPfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hp hp'
  obtain ⟨Q, -, hQtrans, -, -, hQpos, hQfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hq hq'
  let g : M → ℝ := fun x => blendHeight (θ x) P Q (f x)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_globally_blended_height hf hθ P.contMDiff.contDiff Q.contMDiff.contDiff hPfix hQfix
  have hgp : g =ᶠ[𝓝 p] fun x => f x + (p' - f p) :=
    blended_height_one_translation_germ hf.continuous.continuousAt hpgerm hPtrans
  have hgq : g =ᶠ[𝓝 q] fun x => f x + (q' - f q) :=
    blended_height_zero_translation_germ hf.continuous.continuousAt hqgerm hQtrans
  have hexterior (x : M) (hx : f x ∉ Set.Ioo l u) : g =ᶠ[𝓝 x] f :=
    blended_height_exterior_germ hf.continuous hPfix hQfix hx
  have hothers (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f) (hxp : x ≠ p)
    (hxq : x ≠ q) : g =ᶠ[𝓝 x] f := hexterior x (fun hb => (hpair x hx hb).elim hxp hxq)
  have hkeep (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f) :
    ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k := by
    by_cases hxp : x = p
    · subst x
      exact ⟨p' - f p, hgp⟩
    by_cases hxq : x = q
    · subst x
      exact ⟨q' - f q, hgq⟩
    exact ⟨0, by simpa only [add_zero] using hothers x hx hxp hxq⟩
  have hdescent (x : M) (hx : x ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) g x (V x) < 0 := by
    rw [blended_height_directional_derivative hf hg
        (P.contMDiff.contDiff.differentiable (by simp))
        (Q.contMDiff.contDiff.differentiable (by simp)) F hF hθinv x]
    exact
      mul_neg_of_pos_of_neg (positive_blended_slope (hθrange x) (hPpos _) (hQpos _)) (hdesc x hx)
  have hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      exact FlowCancellation.not_critical_of_directional_neg (hdescent x hnot) hx
    · intro hx
      obtain ⟨k, hk⟩ := hkeep x hx
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [MorseCancellation.mfderiv_of_add_const_germ (hf.mdifferentiableAt (by simp)) hk]
      exact hx
  have hmg : ManifoldMorse.IsMorse E g := by
    intro x
    by_cases hx : x ∈ ManifoldMorse.criticalPoints E f
    · obtain ⟨k, hk⟩ := hkeep x hx
      exact MorseCancellation.isMorseAt_of_add_const_germ (hm x) hk
    · have hreg : x ∉ ManifoldMorse.criticalPoints E g := by rwa [hcrit]
      exact MorseCancellationPreservation.isMorseAt_of_regular hg hreg
  refine ⟨g, hg, hmg, hcrit, ?_, ?_, hdescent, hexterior, hgp, hgq, hothers, hkeep⟩
  · have hh := hgp.self_of_nhds
    dsimp only at hh
    linarith
  · have hh := hgq.self_of_nhds
    dsimp only at hh
    linarith

/-- In the absence of a connecting orbit, prescribe new critical values for an isolated pair inside the band while preserving the critical set, Morse indices, descent field and exterior germs. -/
theorem MorseRearrangement.exists_morse_rearrangement_of_no_connection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q)
    (hfp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (hfq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u) (hpq : f p < f q)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            MorseCancellation.nativeMorseIndex E g x =
                              MorseCancellation.nativeMorseIndex E f x) := by
  obtain ⟨a, hpa, haq⟩ := exists_between hpq
  obtain ⟨rp, hrp, hrpa, hbp, hfieldp⟩ :=
    MorseCancellation.exists_small_native_morse_field_block cp hfp (sub_pos.mpr hpa)
  obtain ⟨rq, hrq, hrqa, hbq, hfieldq⟩ :=
    MorseCancellation.exists_small_native_morse_field_block cq hfq (sub_pos.mpr haq)
  have hpa' : f p + rp ^ 2 ≤ a := by linarith
  have haq' : a ≤ f q - rq ^ 2 := by linarith
  have hregular (x : M) (hx : f x ∈ Set.Ioo (f p) (f q)) :
    x ∉ ManifoldMorse.criticalPoints E f := by
    intro hcrit
    rcases hpair x hcrit ⟨hp.1.le.trans hx.1.le, hx.2.le.trans hq.2.le⟩ with heq | heq
    · rw [heq] at hx
      exact lt_irrefl _ hx.1
    · rw [heq] at hx
      exact lt_irrefl _ hx.2
  have hbandp :
    ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨by nlinarith [hx.1, sq_pos_of_pos hrp], hx.2.trans_lt haq⟩
  have hbandq :
    ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨hpa.trans_le hx.1, by nlinarith [hx.2, sq_pos_of_pos hrq]⟩
  obtain ⟨W, hW, hWrange, hWinv, hWp, hWq⟩ :=
    exists_stationary_pair_weight hf hV F hF hzero hdesc hinj cp cq hrp hrq (hp.1.trans hpa)
      (haq.trans hq.2) hpair hbp hbq hfieldp hfieldq hpa' haq' hbandp hbandq hnoconnection
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, -⟩ :=
    exists_rearranged_morse_function_of_stationary_weight hf hm F hF hdesc hp hq hp' hq'
      (fun x hx hband => hpair x hx ⟨hband.1.le, hband.2.le⟩) hW hWrange hWinv hWp hWq
  refine ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact MorseCancellation.nativeMorseIndex_of_add_const_germ cp hpgerm
  by_cases hxq : x = q
  · subst x
    exact MorseCancellation.nativeMorseIndex_of_add_const_germ cq hqgerm
  exact MorseCancellation.nativeMorseIndex_congr_germ (hothers x hx hxp hxq)


end
