/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating.AttachingUnion

/-!
# Attaching a handle across an isolated critical level

Let `f : M → ℝ` be a smooth function on a compact manifold, `p` a critical point carrying a
signed Morse chart `c`, and `V` a gradient-like (descending) vector field with flow `F` that
agrees with the model descent field of `c` near the handle. If `p` is the only critical point
with value in `[f p - ρ², f p + ρ²]`, then the sublevel set `{f ≤ f p + ρ²}` is homeomorphic to
`{f ≤ f p - ρ²}` with the model handle `c.attachingHandleMap ρ` attached, by a homeomorphism
that is the identity on the upper level and follows the flow lines from the frontier of the
attaching union to the upper level. This is the handle-attachment step of Morse theory
(cf. Milnor, *Morse theory*, §3; Milnor, *Lectures on the h-cobordism theorem*, §3).

## Main results

* `ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits`:
  the homeomorphism, with level and orbit control, from a given flow.
* `ManifoldMorse.SignedMorseChart.FollowsModelBoundaryOrbits`: the homeomorphism moves frontier
  points along the model descent flow of the chart.
* `ManifoldMorse.SignedMorseChart.exists_isolated_fieldCompatibleBlock_lt`: a product block in
  the chart on which the field is the model field and which isolates the critical level.
* `ManifoldMorse.exists_morse_boundary_attachment_with_model_orbits_lt`: for a Morse function
  and a critical point that is alone on its level, all of the above for arbitrarily small `ρ`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65]

## Tags

Morse theory, handle attachment, gradient-like vector field
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Attaching unions of a signed Morse chart -/

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is homeomorphic to the model with level and orbit control. -/
theorem ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
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
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 },
      (∀ x,
          f (e x) = f p + ρ ^ 2 ↔
            x.val ∈
              frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
        (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (∀ x,
            x.val ∈
                frontier
                  ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
              ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hboundary (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) (t : ℝ) (ht : 0 < t) : f (F t x) < f x := by
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp := hband x hcrit (hx ▸ hb)
      exact hne (hx.symm.trans (congrArg f hxp))
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x :=
    hboundary _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have htop : ∀ x, f x = f p + ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p + ρ ^ 2 := by
    intro x hx t ht
    rw [← hx]
    exact
      hboundary _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ]) x hx t ht
  have hhome :=
    FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits hf hV hdesc F
      hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
      (fun x hcrit hx => by
        have hxp := hband x hcrit hx
        subst x
        exact
          interior_mono Set.subset_union_right
            (c.mem_interior_range_attachingHandleMap ρ hρ hblock))
      (c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement)
      (c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom)
      htop
  obtain ⟨e, hfront, hfixed, horbit⟩ := hhome
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro x
    have hx := hfront (e.symm x)
    rw [e.apply_symm_apply,
      FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop] at hx
    exact hx.symm
  · intro x hx
    let y : { x : M // f x ≤ f p + ρ ^ 2 } := ⟨x.val, hx.le⟩
    have hy : y.val ∈ frontier {z : M | f z ≤ f p + ρ ^ 2} := by
      rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
      exact hx
    have heq : e y = x := Subtype.ext (hfixed y x.property hy)
    have hh := congrArg e.symm heq
    rw [e.symm_apply_apply] at hh
    exact congrArg (fun z : { z : M // f z ≤ f p + ρ ^ 2 } => z.val) hh.symm
  · intro x hx t ht hlevel
    apply horbit x hx t ht
    rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
    exact hlevel

attribute [local instance 100] Classical.propDecidable in
/-- A homotopy follows the model boundary orbits of the chart. -/
def ManifoldMorse.SignedMorseChart.FollowsModelBoundaryOrbits {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 }) :
    Prop :=
  ∀ x,
    x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
      x.val ∈ c.splitChart.source →
        ∀ t : ℝ,
          t ≤ 0 →
            (∀ s ∈ Set.uIcc 0 t,
                MorseHandle.descentFlow s (c.splitChart x.val) ∈
                  Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                    Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ)) →
              f (c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))) =
                  f p + ρ ^ 2 →
                (e x).val =
                  c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))

attribute [local instance 100] Classical.propDecidable in
/-- The flow follows the model boundary orbits. -/
theorem ManifoldMorse.SignedMorseChart.followsModelBoundaryOrbits_of_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (horbit :
      ∀ x,
        x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
          ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) :
    c.FollowsModelBoundaryOrbits ρ hρ hblock e := by
  intro x hx hsource t ht hpath hlevel
  have hmodel :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hcurve hsource (fun s hs => hblock (hpath s hs))
      (fun s hs => heq _ (hpath s hs))
  exact (horbit x hx t ht (hmodel ▸ hlevel)).trans hmodel

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block inside a prescribed set exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_closed_productBlock_in {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {W : Set M} (hW : IsOpen W)
    (hpW : p ∈ W) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hmem : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target ∩ e.symm ⁻¹' W :=
    ⟨hzero, by simpa only [Set.mem_preimage, hinv] using hpW⟩
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp ((e.isOpen_inter_preimage_symm hW).mem_nhds hmem)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
/-- A field-compatible block of the signed chart exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_fieldCompatibleBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) :
    ∃ ρ > (0 : ℝ),
      ∃ W : Set M,
        IsOpen W ∧
          p ∈ W ∧
            (∀ x ∈ W, V x = c.descentField x) ∧
              Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp heq
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hW hpW
  refine ⟨r / 2, half_pos hr, W, hW, hpW, hWeq, ?_⟩
  rw [show 2 * (r / 2) = r by ring]
  exact hblock

/-- If `K` is finite and `p` is the only point of `K` with value `f p`, then for every `R > 0`
there is `0 < ρ < R` such that `p` is the only point of `K` with value in
`[f p - ρ ^ 2, f p + ρ ^ 2]`. -/
theorem ManifoldMorse.exists_isolating_radius {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (p : X) (hunique : ∀ x ∈ K, f x = f p → x = p) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∀ x ∈ K, f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  have hfin : (f '' (K \ { p })).Finite := (hK.subset Set.sdiff_subset).image f
  have hnot : f p ∉ f '' (K \ { p }) := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (Set.mem_singleton_iff.mpr (hunique x hx.1 heq))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl (f p) hnot
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro x hx hval
  by_contra hxp
  have hd : Dist.dist (f x) (f p) < δ := by
    rw [Real.dist_eq]
    have ha : |f x - f p| ≤ ρ ^ 2 := abs_le.mpr ⟨by linarith [hval.1], by linarith [hval.2]⟩
    exact ha.trans_lt hρsq
  exact hball hd ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, rfl⟩

attribute [local instance 100] Classical.propDecidable in
/-- An isolated field-compatible block below a level exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_isolated_fieldCompatibleBlock_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ),
      ρ < ε ∧
        ∃ W : Set M,
          IsOpen W ∧
            p ∈ W ∧
              (∀ x ∈ W, V x = c.descentField x) ∧
                (Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                      Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                    c.splitChart.target ∩ c.splitChart.symm ⁻¹' W) ∧
                  ∀ x ∈ ManifoldMorse.criticalPoints E f,
                    f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨R, hR, W, hW, hpW, heqW, hblock⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρbound, hband⟩ :=
    ManifoldMorse.exists_isolating_radius hfinite p hunique (lt_min hR hε)
  have hρR : ρ < R := hρbound.trans_le (min_le_left _ _)
  have hρε : ρ < ε := hρbound.trans_le (min_le_right _ _)
  refine ⟨ρ, hρ, hρε, W, hW, hpW, heqW, ?_, hband⟩
  intro z hz
  apply hblock
  have hr : 2 * ρ ≤ 2 * R := mul_le_mul_of_nonneg_left hρR.le (by norm_num)
  exact ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩

/-! ### Constant perturbations -/

attribute [local instance 100] Classical.propDecidable in
/-- A Morse boundary attachment with model orbits exists below a level. -/
theorem ManifoldMorse.exists_morse_boundary_attachment_with_model_orbits_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      ρ < ε ∧
        ∃ c : SignedMorseChart (E := E) f p,
          ∃ hblock :
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
              c.splitChart.target,
            ∃ e :
              ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
                { x : M // f x ≤ f p + ρ ^ 2 },
              (∀ x,
                  f (e x) = f p + ρ ^ 2 ↔
                    x.val ∈
                      frontier
                        ({y | f y ≤ f p - ρ ^ 2} ∪
                          Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
                (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
                  (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
                    (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
                      (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
                        c.FollowsModelBoundaryOrbits ρ hρ hblock e ∧
                          ∀ x ∈ criticalPoints E f,
                            f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨ρ, hρ, hρε, W, hW, _, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt (finite_criticalPoints hf hm) hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hcurve ρ hρ hblock
      hagreement hband
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    have hxp := hband x hcrit (hx ▸ hb)
    exact hne (hx.symm.trans (congrArg f hxp))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hstrict :=
      FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hstrict
  refine
    ⟨ρ, hρ, hρε, c, hblock, e, hfront, hfixed,
      FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono hbottom,
      hlower, hupper, ?_, hband⟩
  apply
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hcurve ρ hρ hblock (e := e)
      (horbit := horbit)
  intro z hz
  filter_upwards [hW.mem_nhds (hblockW hz).2] with y hy
  exact heqW y hy
