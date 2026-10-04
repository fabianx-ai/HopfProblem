/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Gluing flow-box charts along an axis

Charts `Φ : D → M` in which a field `V` on `M` is the model field `W` on `D`
(`V = FlowConstruction.partialChartField Φ.symm W` on the target) are glued:

* `partialChartField_eq_of_forward_germ`, `isLocalDiffeomorphAt_of_chart_germ`,
  `exists_controlled_field_germ_chart`: the chart field depends only on the germ of the chart,
  and a chart can be shrunk to a closed ball around a point where `V' = V` near the image;
* `exists_native_field_chart_near_compact`: a map `f : D → M`, injective on a compact `K` and
  agreeing near every point of `K` with a chart of `W`, is itself a chart of `W` on a
  neighbourhood of `K`;
* `threeChartMap f₀ fₘ f₁ a b`: the map equal to `f₀` for `t ≤ a`, to `fₘ` on `(a, b)` and to
  `f₁` for `t ≥ b`, with its germs (`threeChartMap_left_germ`, `threeChartMap_middle_germ`,
  `threeChartMap_right_germ`, `threeChartMap_left_closed_germ`,
  `threeChartMap_right_closed_germ`);
* `exists_glued_three_native_field_charts`, `injective_closed_axis_of_regular_chart`,
  `exists_closed_axis_native_field_chart`: three charts of `W` on `ℝ × Z` covering the closed
  axis segment `[l, r] × {0}`, agreeing near the junctions `(a, 0)` and `(b, 0)`, glue to one
  chart of `W` containing the whole segment and agreeing with `Φ₀` near `(l, 0)` and with `Φ₁`
  near `(r, 0)`.

cf. Lee, *Introduction to Smooth Manifolds*, Theorem 9.22 (flow-box charts) and Milnor,
*Lectures on the h-cobordism theorem*, §5 (a coordinate neighbourhood of the whole trajectory).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Field chart gluing -/

/-- Partial chart fields with a forward germ agree. -/
theorem FieldChartGluing.partialChartField_eq_of_forward_germ {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (W : D → D) {p : D} (hpΦ : p ∈ Φ.source) (hpΨ : p ∈ Ψ.source) (heq : (Φ : D → M) =ᶠ[𝓝 p] Ψ) :
    FlowConstruction.partialChartField Φ.symm W (Φ p) =
      FlowConstruction.partialChartField Ψ.symm W (Φ p) := by
  have hval : Φ p = Ψ p := heq.eq_of_nhds
  have hyΨ : Φ p ∈ Ψ.target := hval.symm ▸ Ψ.map_source' hpΨ
  have hiΦ : Φ.symm (Φ p) = p := Φ.left_inv' hpΦ
  have hiΨ : Ψ.symm (Φ p) = p := by rw [hval]; exact Ψ.left_inv' hpΨ
  rw [FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W (Φ.map_source' hpΦ),
    FlowConstruction.partialChartField_eq_mfderiv_symm Ψ.symm W hyΨ]
  change
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Φ (Φ.symm (Φ p))
        ((NormedSpace.fromTangentSpace (Φ.symm (Φ p))).symm (W (Φ.symm (Φ p)))) =
      mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Ψ (Ψ.symm (Φ p))
        ((NormedSpace.fromTangentSpace (Ψ.symm (Φ p))).symm (W (Ψ.symm (Φ p))))
  rw [hiΦ, hiΨ, heq.mfderiv_eq]
  rfl

/-- A chart-germ map is a local diffeomorphism. -/
theorem FieldChartGluing.isLocalDiffeomorphAt_of_chart_germ {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {f : D → M} {p : D} (hp : p ∈ Φ.source) (heq : f =ᶠ[𝓝 p] Φ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictSource Φ hU
  exact ⟨Ψ, ⟨hp, hpU⟩, fun x hx => hUsub hx.2⟩

attribute [local instance 100] Classical.propDecidable in
/-- A native field chart near a compact set exists. -/
theorem FieldChartGluing.exists_native_field_chart_near_compact {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] (f : D → M) (W : D → D)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) {K : Set D} (hK : IsCompact K) (hinj : Set.InjOn f K)
    (hlocal :
      ∀ p ∈ K,
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
          p ∈ Φ.source ∧
            f =ᶠ[𝓝 p] Φ ∧
              ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      K ⊆ Φ.source ∧
        (∀ p, Φ p = f p) ∧
          ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y := by
  let U : Set D :=
    {p |
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
        p ∈ Φ.source ∧
          f =ᶠ[𝓝 p] Φ ∧ ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨Ψ, hp, heq, hfield⟩
    filter_upwards [Ψ.open_source.mem_nhds hp, heq.eventuallyEq_nhds] with q hq hqeq
    exact ⟨Ψ, hq, hqeq, hfield⟩
  have hloc (p : D) (hp : p ∈ K) : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
    obtain ⟨Ψ, hpΨ, heq, _⟩ := hlocal p hp
    exact isLocalDiffeomorphAt_of_chart_germ Ψ hpΨ heq
  obtain ⟨Φ, hKΦ, hΦU, hmap⟩ :=
    exists_partialDiffeomorph_near_compact hK hinj hloc hU hlocal
  refine ⟨Φ, hKΦ, fun p => congrFun hmap p, ?_⟩
  intro y hy
  have hp : Φ.symm y ∈ Φ.source := Φ.map_target' hy
  obtain ⟨Ψ, hpΨ, heq, hfield⟩ := hΦU hp
  have hΦeq : (Φ : D → M) =ᶠ[𝓝 (Φ.symm y)] Ψ := by rw [hmap]; exact heq
  have hi : Φ (Φ.symm y) = y := Φ.right_inv' hy
  have hΨval : Ψ (Φ.symm y) = y := hΦeq.eq_of_nhds.symm.trans hi
  have hyΨ : y ∈ Ψ.target := hΨval ▸ Ψ.map_source' hpΨ
  have hsame := partialChartField_eq_of_forward_germ Φ Ψ W hp hpΨ hΦeq
  rw [hi] at hsame
  exact (hfield y hyΨ).trans hsame.symm

/-- A controlled field germ chart exists. -/
theorem FieldChartGluing.exists_controlled_field_germ_chart {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (W : D → D) (V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) {c : D}
    (hc : c ∈ Φ.source) (hfield : ∀ᶠ y in 𝓝 (Φ c), V' y = V y) {O : Set D} (hO : IsOpen O)
    (hcO : c ∈ O) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (r : ℝ),
      0 < r ∧
        Metric.closedBall c r ⊆ Ψ.source ∧
          Ψ.source ⊆ Φ.source ∩ O ∧
            Ψ.target ⊆ Φ.target ∧
              (∀ z, Ψ z = Φ z) ∧
                ∀ y ∈ Ψ.target, V' y = FlowConstruction.partialChartField Ψ.symm W y := by
  obtain ⟨U, hUsub, hU, hcenter⟩ := mem_nhds_iff.mp hfield
  let R := PartialChart.restrictTarget Φ hU
  let Ψ := PartialChart.restrictSource R hO
  have hcΨ : c ∈ Ψ.source := by
    change (c ∈ Φ.source ∧ Φ c ∈ U) ∧ c ∈ O
    exact ⟨⟨hc, hcenter⟩, hcO⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds hcΨ)
  refine ⟨Ψ, r, hr, hball, fun z hz => ⟨hz.1.1, hz.2⟩, fun y hy => hy.1.1, fun _ => rfl, ?_⟩
  intro y hy
  exact (hUsub hy.1.2).trans (hmodel y hy.1.1)

/-! ### The three-chart gluing -/

/-- The three-chart glued map. -/
def FieldChartGluing.threeChartMap {Z M : Type*} (f₀ fₘ f₁ : (ℝ × Z) → M) (a b : ℝ)
    (p : ℝ × Z) : M :=
  if p.1 ≤ a then f₀ p else if b ≤ p.1 then f₁ p else fₘ p

/-- The three-chart map's left germ. -/
theorem FieldChartGluing.threeChartMap_left_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (hp : p.1 < a) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₀ := by
  filter_upwards [continuousAt_fst.eventually (eventually_lt_nhds hp)] with q hq
  simp only [threeChartMap, if_pos hq.le]

/-- The three-chart map's middle germ. -/
theorem FieldChartGluing.threeChartMap_middle_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (ha : a < p.1) (hb : p.1 < b) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] fₘ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds ha),
    continuousAt_fst.eventually (eventually_lt_nhds hb)] with q hqa hqb
  simp only [threeChartMap, if_neg (not_le_of_gt hqa), if_neg (not_le_of_gt hqb)]

/-- The three-chart map's right germ. -/
theorem FieldChartGluing.threeChartMap_right_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) {p : ℝ × Z} (hp : b < p.1) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₁ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds hp)] with q hq
  simp only [threeChartMap, if_neg (not_le_of_gt (hab.trans hq)), if_pos hq.le]

/-- The three-chart map's left closed germ. -/
theorem FieldChartGluing.threeChartMap_left_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₀ =ᶠ[𝓝 (a, (0 : Z))] fₘ)
    {s : ℝ} (hs : s ≤ a) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₀ := by
  rcases hs.lt_or_eq with hs | hs
  · exact threeChartMap_left_germ f₀ fₘ f₁ hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_lt_nhds hab)] with p hp hpb
    by_cases hpa : p.1 ≤ a
    · simp only [threeChartMap, if_pos hpa]
    · simp only [threeChartMap, if_neg hpa, if_neg (not_le_of_gt hpb)]
      exact hp.symm

/-- The three-chart map's right closed germ. -/
theorem FieldChartGluing.threeChartMap_right_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₁ =ᶠ[𝓝 (b, (0 : Z))] fₘ)
    {s : ℝ} (hs : b ≤ s) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₁ := by
  rcases hs.eq_or_lt with hs | hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_gt_nhds hab)] with p hp hpa
    by_cases hpb : b ≤ p.1
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_pos hpb]
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_neg hpb]
      exact hp.symm
  · exact threeChartMap_right_germ f₀ fₘ f₁ hab hs

/-- Three glued native field charts exist. -/
theorem FieldChartGluing.exists_glued_three_native_field_charts {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo a b, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ) (γ : ℝ → M)
    (hinj : Set.InjOn γ (Set.Icc l r)) (haxis₀ : ∀ s ∈ Set.Icc l a, Φ₀ (s, 0) = γ s)
    (haxisₘ : ∀ s ∈ Set.Ioo a b, Φₘ (s, 0) = γ s) (haxis₁ : ∀ s ∈ Set.Icc b r, Φ₁ (s, 0) = γ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ s ∈ Set.Icc l r, Φ (s, 0) = γ s) ∧
          (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
            ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
              ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let f := threeChartMap Φ₀ Φₘ Φ₁ a b
  have haxis (s : ℝ) (hs : s ∈ Set.Icc l r) : f (s, 0) = γ s := by
    by_cases hsa : s ≤ a
    · exact
        (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa).eq_of_nhds.trans
          (haxis₀ s ⟨hs.1, hsa⟩)
    · by_cases hbs : b ≤ s
      · exact
          (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs).eq_of_nhds.trans
            (haxis₁ s ⟨hbs, hs.2⟩)
      · exact
          (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa)
                (lt_of_not_ge hbs)).eq_of_nhds.trans
            (haxisₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩)
  have hfinj : Set.InjOn f (Set.Icc l r ×ˢ {(0 : Z)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [haxis s hs, haxis t ht] at heq
    exact congrArg (fun s : ℝ => (s, (0 : Z))) (hinj hs ht heq)
  have hlocal :
    ∀ p ∈ Set.Icc l r ×ˢ {(0 : Z)},
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
        p ∈ Ψ.source ∧
          f =ᶠ[𝓝 p] Ψ ∧
            ∀ y ∈ Ψ.target, V y = FlowConstruction.partialChartField Ψ.symm W y := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsa : s ≤ a
    · exact
        ⟨Φ₀, hsource₀ s ⟨hs.1, hsa⟩, threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa,
          hfield₀⟩
    · by_cases hbs : b ≤ s
      · exact
          ⟨Φ₁, hsource₁ s ⟨hbs, hs.2⟩, threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs,
            hfield₁⟩
      · exact
          ⟨Φₘ, hsourceₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩,
            threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa) (lt_of_not_ge hbs), hfieldₘ⟩
  obtain ⟨Φ, hsource, hmap, hfield⟩ :=
    exists_native_field_chart_near_compact f W V
      (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hfinj hlocal
  refine ⟨Φ, hsource, fun s hs => (hmap (s, 0)).trans (haxis s hs), hfield, ?_, ?_⟩
  · filter_upwards [threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hla] with p hp
    exact (hmap p).trans hp
  · filter_upwards [threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbr] with p hp
    exact (hmap p).trans hp

/-- A regular chart's closed axis is injective. -/
theorem FieldChartGluing.injective_closed_axis_of_regular_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) {l r : ℝ} (γ : ℝ → M)
    (hsource : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φ.source)
    (hregular : ∀ s ∈ Set.Ioo l r, γ s = Φ (s, 0)) (hleft : γ l ∉ Φ.target)
    (hright : γ r ∉ Φ.target) (hne : γ l ≠ γ r) : Set.InjOn γ (Set.Icc l r) := by
  have htarget (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s ∈ Φ.target := by
    rw [hregular s hs]
    exact Φ.map_source' (hsource s hs)
  have hleftOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ l) : s = l := by
    by_cases hsl : s = l
    · exact hsl
    by_cases hsr : s = r
    · subst s
      exact (hne heq.symm).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hleft (heq ▸ htarget s hi)).elim
  have hrightOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ r) : s = r := by
    by_cases hsr : s = r
    · exact hsr
    by_cases hsl : s = l
    · subst s
      exact (hne heq).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hright (heq ▸ htarget s hi)).elim
  intro s hs t ht heq
  by_cases hsl : s = l
  · subst s
    exact (hleftOnly t ht heq.symm).symm
  by_cases hsr : s = r
  · subst s
    exact (hrightOnly t ht heq.symm).symm
  by_cases htl : t = l
  · subst t
    exact hleftOnly s hs heq
  by_cases htr : t = r
  · subst t
    exact hrightOnly s hs heq
  have hs' : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
  have ht' : t ∈ Set.Ioo l r := ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
  rw [hregular s hs', hregular t ht'] at heq
  exact congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn (hsource s hs') (hsource t ht') heq)

/-- A closed-axis native field chart exists. -/
theorem FieldChartGluing.exists_closed_axis_native_field_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l < a) (hab : a < b) (hbr : b < r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ)
    (haxis₀ : ∀ s ∈ Set.Ioc l a, Φ₀ (s, 0) = Φₘ (s, 0))
    (haxis₁ : ∀ s ∈ Set.Ico b r, Φ₁ (s, 0) = Φₘ (s, 0)) (hleft : Φ₀ (l, 0) ∉ Φₘ.target)
    (hright : Φ₁ (r, 0) ∉ Φₘ.target) (hne : Φ₀ (l, 0) ≠ Φ₁ (r, 0)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
          Φ (l, 0) = Φ₀ (l, 0) ∧
            Φ (r, 0) = Φ₁ (r, 0) ∧
              (∀ s ∈ Set.Ioo l r, Φ (s, 0) = Φₘ (s, 0)) ∧
                ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
                  ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let γ : ℝ → M := fun s => threeChartMap Φ₀ Φₘ Φ₁ a b (s, 0)
  have hγ₀ (s : ℝ) (hs : s ≤ a) : γ s = Φ₀ (s, 0) :=
    (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hs).eq_of_nhds
  have hγ₁ (s : ℝ) (hs : b ≤ s) : γ s = Φ₁ (s, 0) :=
    (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hs).eq_of_nhds
  have hγₘ (s : ℝ) (hs : s ∈ Set.Ioo a b) : γ s = Φₘ (s, 0) :=
    (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ hs.1 hs.2).eq_of_nhds
  have hregular (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s = Φₘ (s, 0) := by
    by_cases hsa : s ≤ a
    · exact (hγ₀ s hsa).trans (haxis₀ s ⟨hs.1, hsa⟩)
    by_cases hbs : b ≤ s
    · exact (hγ₁ s hbs).trans (haxis₁ s ⟨hbs, hs.2⟩)
    exact hγₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩
  have hinj : Set.InjOn γ (Set.Icc l r) :=
    injective_closed_axis_of_regular_chart Φₘ γ hsourceₘ hregular
      (by rw [hγ₀ l hla.le]; exact hleft) (by rw [hγ₁ r hbr.le]; exact hright)
      (by rw [hγ₀ l hla.le, hγ₁ r hbr.le]; exact hne)
  obtain ⟨Φ, hsource, haxis, hfield, hg₀, hg₁⟩ :=
    exists_glued_three_native_field_charts Φ₀ Φₘ Φ₁ W V hfield₀ hfieldₘ hfield₁ hla.le hab hbr.le
      hsource₀ (fun s hs => hsourceₘ s ⟨hla.trans hs.1, hs.2.trans hbr⟩) hsource₁ hgerm₀ hgerm₁ γ
      hinj (fun s hs => (hγ₀ s hs.2).symm) (fun s hs => (hγₘ s hs).symm)
      (fun s hs => (hγ₁ s hs.1).symm)
  have hlr : l ≤ r := (hla.trans (hab.trans hbr)).le
  refine
    ⟨Φ, hsource, hfield, (haxis l ⟨le_rfl, hlr⟩).trans (hγ₀ l hla.le),
      (haxis r ⟨hlr, le_rfl⟩).trans (hγ₁ r hbr.le), ?_, hg₀, hg₁⟩
  exact fun s hs => (haxis s ⟨hs.1.le, hs.2.le⟩).trans (hregular s hs)

end
