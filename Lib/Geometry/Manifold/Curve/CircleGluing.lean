/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Gluing two arcs into a smoothly embedded circle

Two smooth arcs in a manifold `N` whose endpoint germs match are glued into a single smooth
embedded circle.  The construction runs in three steps.

* `CircleGluing.periodicExtension` extends a function on a fundamental interval to a
  `T`-periodic function on `ℝ`, and records when the extension is smooth and immersed.
* `CircleGluing.joinedArc` concatenates two arcs `α`, `β` at the parameter `2 * r`, and
  `CircleGluing.joinedLoop` closes the concatenation up into a periodic map `ℝ → N`; the
  lemmas `joinedLoop_injOn`, `joinedLoop_contMDiff`, `joinedLoop_derivative_injective` give the
  conditions under which the loop is injective on a period, smooth and immersed.
* `CircleGluing.periodicCircle` descends a periodic map `ℝ → N` through
  `Circle.exp : ℝ → Circle` to a map `Circle → N`, using that `Circle.exp` is a local
  diffeomorphism (`CircleGluing.circleExp_localDiffeomorph`); `periodicCircle_injective`,
  `periodicCircle_contMDiff` and `periodicCircle_derivative_injective` transfer injectivity,
  smoothness and immersivity from the periodic map to the circle map.

Together these give a smooth embedded circle in `N` traversing the two arcs, the input to the
cancellation arguments of Milnor, *Lectures on the h-cobordism theorem*, §§5-6.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5-6.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- Injectivity of the derivative of a curve is preserved by translating the parameter. -/
theorem CircleGluing.injective_mfderiv_curve_translate {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α : ℝ → N} {s c : ℝ} (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (s + c))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (s + c))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (t + c)) s) := by
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s :=
    (contMDiff_id.add (contMDiff_const (c := c)) :
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t + c)).mdifferentiableAt
      (by simp)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => id t + c) s = _
    rw [fderiv_add_const, fderiv_id]
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => t + c)) s)
  rw [mfderiv_comp s hα ht]
  intro x y hxy
  apply hi
  have hdx : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x = x :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L x) hd
  have hdy : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y = y :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L y) hd
  change
    mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x) =
      mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y) at hxy
  rw [hdx, hdy] at hxy
  exact hxy

/-- The `T`-periodic extension of `f` obtained by reducing the parameter into `[0, T)`. -/
def CircleGluing.periodicExtension {N : Type*} {T : ℝ} (hT : 0 < T) (f : ℝ → N) (t : ℝ) :
    N :=
  f (toIcoMod hT 0 t)

/-- The periodic extension is `T`-periodic. -/
theorem CircleGluing.periodicExtension_periodic {N : Type*} {T : ℝ} (hT : 0 < T)
    (f : ℝ → N) : Function.Periodic (periodicExtension hT f) T := fun t =>
  congrArg f (toIcoMod_add_right hT 0 t)

/-- If `f` matches its own translate by `T` near `0`, the periodic extension agrees with `f`
near every point of the fundamental interval `[0, T)`. -/
theorem CircleGluing.periodicExtension_germ_in_fundamental_interval {N : Type*} {T : ℝ}
    (hT : 0 < T) {f : ℝ → N} (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) T) : periodicExtension hT f =ᶠ[𝓝 x] f := by
  by_cases hx0 : x = 0
  · subst x
    filter_upwards [hmatch, Ioo_mem_nhds (neg_lt_zero.mpr hT) hT] with t ht htn
    change f (toIcoMod hT 0 t) = f t
    by_cases ht0 : 0 ≤ t
    · rw [(toIcoMod_eq_self hT).mpr ⟨ht0, by simpa only [zero_add] using htn.2⟩]
    · have hmod : toIcoMod hT 0 t = t + T := by
        apply (toIcoMod_eq_iff hT).mpr
        refine ⟨⟨by linarith [htn.1], by linarith⟩, -1, ?_⟩
        simp
      rw [hmod]
      exact ht
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    filter_upwards [Ioo_mem_nhds hxpos hx.2] with t ht
    change f (toIcoMod hT 0 t) = f t
    rw [(toIcoMod_eq_self hT).mpr ⟨ht.1.le, by simpa only [zero_add] using ht.2⟩]

/-- Near any point, the periodic extension is a translate of `f`. -/
theorem CircleGluing.periodicExtension_germ {N : Type*} {T : ℝ} (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) (x : ℝ) :
    ∃ c : ℝ, x + c ∈ Set.Ico (0 : ℝ) T ∧ periodicExtension hT f =ᶠ[𝓝 x] (fun t => f (t + c)) := by
  let n : ℤ := toIcoDiv hT 0 x
  let c : ℝ := -(n • T)
  have hx : x + c = toIcoMod hT 0 x := by
    change x - n • T = toIcoMod hT 0 x
    rfl
  have hxc : x + c ∈ Set.Ico (0 : ℝ) T := by
    rw [hx]
    simpa only [zero_add] using toIcoMod_mem_Ico hT 0 x
  have hg := periodicExtension_germ_in_fundamental_interval hT hmatch hxc
  have ht : Filter.Tendsto (fun t : ℝ => t + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).continuousAt
  refine ⟨c, hxc, ?_⟩
  filter_upwards [hg.comp_tendsto ht] with t ht
  have heq : periodicExtension hT f (t + c) = periodicExtension hT f t :=
    congrArg f (toIcoMod_sub_zsmul hT 0 t n)
  exact heq.symm.trans ht

/-- The periodic extension of a map that is smooth on `[0, T)` and matches its translate by `T`
near `0` is smooth on all of `ℝ`. -/
theorem CircleGluing.periodicExtension_contMDiff {N : Type*} {T : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) J ∞ f t) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (periodicExtension hT f) := by
  intro x
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  exact
    ((hf (x + c) hc).comp x (contMDiff_id.add contMDiff_const).contMDiffAt).congr_of_eventuallyEq
      heq

/-- Under the same hypotheses, the periodic extension is an immersion if `f` is one on
`[0, T)`. -/
theorem CircleGluing.periodicExtension_derivative_injective {N : Type*} {T : ℝ}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, MDifferentiableAt 𝓘(ℝ, ℝ) J f t)
    (hi : ∀ t ∈ Set.Ico (0 : ℝ) T, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (x : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicExtension hT f) x) := by
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  rw [heq.mfderiv_eq]
  exact CircleGluing.injective_mfderiv_curve_translate (hf (x + c) hc) (hi (x + c) hc)

attribute [local instance 100] Classical.propDecidable in
/-- The concatenation of `α` on `[0, 2r]` (as `t ↦ α (t - r)`) with `β` on `(2r, 2r+1]` (as
`t ↦ β (t - 2r)`). -/
def CircleGluing.joinedArc {N : Type*} (α β : ℝ → N) (r t : ℝ) : N :=
  if t ≤ 2 * r then α (t + (-r)) else β (t + (-2 * r))

/-- Before the seam, the concatenation is the translate of `α`. -/
theorem CircleGluing.joinedArc_left {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : t ≤ 2 * r) :
    joinedArc α β r t = α (t + (-r)) :=
  if_pos ht

/-- After the seam, the concatenation is the translate of `β`. -/
theorem CircleGluing.joinedArc_right {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : 2 * r < t) :
    joinedArc α β r t = β (t + (-2 * r)) :=
  if_neg (not_le.mpr ht)

/-- Near a parameter strictly before the seam, the concatenation is the translate of `α`. -/
theorem CircleGluing.joinedArc_left_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : t < 2 * r) : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact joinedArc_left hs.le

/-- Near a parameter strictly after the seam, the concatenation is the translate of `β`. -/
theorem CircleGluing.joinedArc_right_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : 2 * r < t) : joinedArc α β r =ᶠ[𝓝 t] (fun s => β (s + (-2 * r))) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact joinedArc_right hs

/-- At the seam `2r`, the concatenation is still the translate of `α`, because `β` agrees with
that translate near `0`. -/
theorem CircleGluing.joinedArc_seam_germ {N : Type*} {α β : ℝ → N} {r : ℝ}
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) :
    joinedArc α β r =ᶠ[𝓝 (2 * r)] (fun s => α (s + (-r))) := by
  have ht : Filter.Tendsto (fun t : ℝ => t + (-2 * r)) (𝓝 (2 * r)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t + (-2 * r)) := continuous_id.add continuous_const
    simpa only [show 2 * r + (-2 * r) = 0 by ring] using hc.continuousAt.tendsto (x := 2 * r)
  filter_upwards [h0.comp_tendsto ht] with t ht
  change β (t + (-2 * r)) = α (t + (-2 * r) + r) at ht
  by_cases htr : t ≤ 2 * r
  · exact joinedArc_left htr
  · rw [joinedArc_right (lt_of_not_ge htr), ht]
    congr 1
    ring

/-- The concatenation matches its translate by the period `2r + 1` near `0`, because `β` agrees
with `t ↦ α (t - 1 - r)` near `1`. -/
theorem CircleGluing.joinedArc_periodic_germ {N : Type*} {α β : ℝ → N} {r : ℝ} (hr : 0 < r)
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    (fun t => joinedArc α β r (t + (2 * r + 1))) =ᶠ[𝓝 (0 : ℝ)] joinedArc α β r := by
  have ht : Filter.Tendsto (fun t : ℝ => t + 1) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => t + 1) := continuous_id.add continuous_const
    simpa only [zero_add] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [h1.comp_tendsto ht,
    Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show 0 < 2 * r by linarith)] with t ht htn
  change β (t + 1) = α (t + 1 + (-1 - r)) at ht
  rw [joinedArc_right (by linarith [htn.1]), joinedArc_left htn.2.le,
    show t + (2 * r + 1) + (-2 * r) = t + 1 by ring, ht]
  congr 1
  ring

/-- The concatenation is injective on one period when both arcs are injective and `β` meets the
arc `α '' [-r, r]` only at its endpoints. -/
theorem CircleGluing.joinedArc_injOn {N : Type*} {α β : ℝ → N} {r : ℝ}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedArc α β r) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  have hleft {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hle : t ≤ 2 * r) :
    t + (-r) ∈ Set.Icc (-r) r := ⟨by linarith [ht.1], by linarith⟩
  have hright {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hlt : 2 * r < t) :
    t + (-2 * r) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
  by_cases hxl : x ≤ 2 * r <;> by_cases hyl : y ≤ 2 * r
  · rw [joinedArc_left hxl, joinedArc_left hyl] at hxy
    have heq := hα (hleft hx hxl) (hleft hy hyl) hxy
    linarith
  · rw [joinedArc_left hxl, joinedArc_right (lt_of_not_ge hyl)] at hxy
    exact False.elim (havoid _ (hright hy (lt_of_not_ge hyl)) ⟨_, hleft hx hxl, hxy⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_left hyl] at hxy
    exact False.elim (havoid _ (hright hx (lt_of_not_ge hxl)) ⟨_, hleft hy hyl, hxy.symm⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_right (lt_of_not_ge hyl)] at hxy
    have heq :=
      hβ (Set.Ioo_subset_Icc_self (hright hx (lt_of_not_ge hxl)))
        (Set.Ioo_subset_Icc_self (hright hy (lt_of_not_ge hyl))) hxy
    linarith

/-- The concatenation is smooth at every parameter of one period. -/
theorem CircleGluing.joinedArc_contMDiffAt {N : Type*} {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    ContMDiffAt 𝓘(ℝ, ℝ) J ∞ (joinedArc α β r) t := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have hs :=
      (hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).comp t
        (contMDiff_id.add contMDiff_const).contMDiffAt
    apply hs.congr_of_eventuallyEq
    rcases htle.eq_or_lt with rfl | hlt
    · exact joinedArc_seam_germ h0
    · exact joinedArc_left_germ hlt
  · exact
      (hβ.comp (contMDiff_id.add contMDiff_const)).contMDiffAt.congr_of_eventuallyEq
        (joinedArc_right_germ (lt_of_not_ge htle))

/-- The concatenation is an immersion at every parameter of one period. -/
theorem CircleGluing.joinedArc_derivative_injective {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedArc α β r) t) := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have heq : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
      rcases htle.eq_or_lt with rfl | hlt
      · exact joinedArc_seam_germ h0
      · exact joinedArc_left_germ hlt
    rw [heq.mfderiv_eq]
    exact
      CircleGluing.injective_mfderiv_curve_translate
        ((hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).mdifferentiableAt (by simp)) (hiα _ htα)
  · have htβ : t + (-2 * r) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    rw [(joinedArc_right_germ (α := α) (β := β) (lt_of_not_ge htle)).mfderiv_eq]
    exact
      CircleGluing.injective_mfderiv_curve_translate (hβ.mdifferentiableAt (by simp)) (hiβ _ htβ)

/-- The `(2r+1)`-periodic extension of the concatenation `joinedArc α β r`. -/
def CircleGluing.joinedLoop {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) : ℝ → N :=
  periodicExtension (show 0 < 2 * r + 1 by linarith) (joinedArc α β r)

/-- The glued loop is periodic of period `2r + 1`. -/
theorem CircleGluing.joinedLoop_periodic {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) :
    Function.Periodic (joinedLoop hr α β) (2 * r + 1) :=
  periodicExtension_periodic _ _

/-- On the first part of a period the glued loop traverses `α` on `[-r, r]`. -/
theorem CircleGluing.joinedLoop_left {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) {s : ℝ}
    (hs : s ∈ Set.Icc (-r) r) : joinedLoop hr α β (s + r) = α s := by
  change joinedArc α β r (toIcoMod _ 0 (s + r)) = α s
  rw [(toIcoMod_eq_self _).mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    joinedArc_left (by linarith [hs.2])]
  congr 1
  ring

/-- On the second part of a period the glued loop traverses `β` on `[0, 1]`. -/
theorem CircleGluing.joinedLoop_right {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    joinedLoop hr α β (2 * r + s) = β s := by
  by_cases hs1 : s = 1
  · subst s
    have hper := (joinedLoop_periodic hr α β) 0
    rw [zero_add] at hper
    have hz : joinedLoop hr α β 0 = α (-r) := by
      simpa only [neg_add_cancel] using joinedLoop_left hr α β (s := -r) ⟨le_rfl, by linarith⟩
    exact hper.trans (hz.trans h1.symm)
  · change joinedArc α β r (toIcoMod _ 0 (2 * r + s)) = β s
    rw [(toIcoMod_eq_self _).mpr
        ⟨by linarith [hs.1], by
          have hlt : s < 1 := lt_of_le_of_ne hs.2 hs1
          linarith⟩]
    by_cases hs0 : s = 0
    · subst s
      rw [add_zero, joinedArc_left le_rfl]
      simpa only [show 2 * r + (-r) = r by ring] using h0.symm
    · rw [joinedArc_right
          (by
            have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
            linarith)]
      congr 1
      ring

/-- The image of the glued loop is the union of the two arcs. -/
theorem CircleGluing.joinedLoop_range {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) :
    Set.range (joinedLoop hr α β) = α '' Set.Icc (-r) r ∪ β '' Set.Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    let q := toIcoMod (show 0 < 2 * r + 1 by linarith) 0 t
    have hq : q ∈ Set.Ico (0 : ℝ) (2 * r + 1) := by
      simpa only [zero_add] using toIcoMod_mem_Ico (show 0 < 2 * r + 1 by linarith) 0 t
    change joinedArc α β r q ∈ _
    by_cases hqr : q ≤ 2 * r
    · rw [joinedArc_left hqr]
      exact Or.inl ⟨_, ⟨by linarith [hq.1], by linarith⟩, rfl⟩
    · rw [joinedArc_right (lt_of_not_ge hqr)]
      exact Or.inr ⟨_, ⟨by linarith, by linarith [hq.2]⟩, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s + r, joinedLoop_left hr α β hs⟩
    · exact ⟨2 * r + s, joinedLoop_right hr h0 h1 hs⟩

/-- The glued loop is injective on one period. -/
theorem CircleGluing.joinedLoop_injOn {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedLoop hr α β) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  apply joinedArc_injOn hα hβ havoid hx hy
  change joinedArc α β r (toIcoMod _ 0 x) = joinedArc α β r (toIcoMod _ 0 y) at hxy
  rw [(toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hx),
    (toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hy)] at hxy
  exact hxy

/-- The glued loop is smooth. -/
theorem CircleGluing.joinedLoop_contMDiff {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (joinedLoop hr α β) :=
  periodicExtension_contMDiff _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => joinedArc_contMDiffAt hrR hα hβ h0 ht)

/-- The glued loop is an immersion. -/
theorem CircleGluing.joinedLoop_derivative_injective {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r))))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedLoop hr α β) t) :=
  periodicExtension_derivative_injective _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => (joinedArc_contMDiffAt hrR hα hβ h0 ht).mdifferentiableAt (by simp))
    (fun _ ht => joinedArc_derivative_injective hrR hα hβ h0 hiα hiβ ht) t

/-- `Circle.exp : ℝ → Circle` is an immersion. -/
theorem CircleGluing.circleExp_derivative_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hd :
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
      t := by
    simpa only [Circle.coe_exp, Complex.real_smul, id_eq, one_mul] using
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).cexp.comp_ofReal
  have hdne : (Complex.exp ((t : ℂ) * Complex.I) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hi0 : Function.Injective (fderiv ℝ (fun s : ℝ => (Circle.exp s : ℂ)) t) := by
    rw [hd.hasFDerivAt.fderiv]
    exact smul_left_injective ℝ hdne
  let c : Circle → ℂ := fun z => (z : ℂ)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ c := contMDiff_coe_sphere
  have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (c ∘ (fun s : ℝ => Circle.exp s)) t) := by
    rw [mfderiv_eq_fderiv]
    exact hi0
  rw [mfderiv_comp t (hc.mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hi
  intro x y hxy
  exact hi (congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (Circle.exp t)) hxy)

/-- `Circle.exp` is a local diffeomorphism at every point. -/
theorem CircleGluing.circleExp_localDiffeomorph (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hi : Function.Injective L := circleExp_derivative_injective t
  have hs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) (by simp)).mp
      hi
  apply
    isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ t)
      (contMDiff_circleExp (m := ∞)).contMDiffOn
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

/-- A map out of `Circle` is smooth as soon as its composite with `Circle.exp` is, since
`Circle.exp` is a surjective local diffeomorphism. -/
theorem CircleGluing.contMDiff_of_comp_circleExp {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff 𝓘(ℝ, ℝ) J ∞ (γ ∘ Circle.exp)) :
    ContMDiff (𝓡 1) J ∞ γ := by
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  let h := circleExp_localDiffeomorph t
  have hs : ContMDiffAt (𝓡 1) J ∞ ((γ ∘ Circle.exp) ∘ h.localInverse) (Circle.exp t) :=
    (hγ.contMDiffAt (x := h.localInverse (Circle.exp t))).comp _ h.localInverse_contMDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [h.localInverse_eventuallyEq_right] with y hy
  exact (congrArg γ hy).symm

/-- A `T`-periodic map `ℝ → N` seen as a map `Circle → N`. -/
def CircleGluing.periodicCircle {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (z : Circle) : N :=
  hper.lift ((AddCircle.homeomorphCircle hT).symm z)

/-- The defining property: the induced map on `Circle` recovers `f` along the exponential. -/
theorem CircleGluing.periodicCircle_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (t : ℝ) :
    periodicCircle hT hper (Circle.exp (2 * Real.pi / T * t)) = f t := by
  have heq : Circle.exp (2 * Real.pi / T * t) = AddCircle.homeomorphCircle hT (t : AddCircle T) :=
    by rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rw [heq, periodicCircle, Homeomorph.symm_apply_apply, Function.Periodic.lift_coe]

/-- Composing the induced map with `Circle.exp` rescales the parameter by `T / 2π`. -/
theorem CircleGluing.periodicCircle_comp_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) :
    periodicCircle hT hper ∘ Circle.exp = (fun t => f (T / (2 * Real.pi) * t)) := by
  funext t
  have heq : 2 * Real.pi / T * (T / (2 * Real.pi) * t) = t := by field_simp [hT, Real.pi_ne_zero]
  have hh := periodicCircle_exp hT hper (T / (2 * Real.pi) * t)
  rw [heq] at hh
  exact hh

/-- The induced map on `Circle` is injective when `f` is injective on one period. -/
theorem CircleGluing.periodicCircle_injective {N : Type*} {T : ℝ} {f : ℝ → N} (hT : 0 < T)
    (hper : Function.Periodic f T) (hi : Set.InjOn f (Set.Ico (0 : ℝ) T)) :
    Function.Injective (periodicCircle hT.ne' hper) := by
  let _ : Fact (0 < T) := ⟨hT⟩
  let e := AddCircle.homeomorphCircle hT.ne'
  intro z w hzw
  let x := AddCircle.equivIco T 0 (e.symm z)
  let y := AddCircle.equivIco T 0 (e.symm w)
  have hx : (x.val : AddCircle T) = e.symm z := AddCircle.coe_equivIco
  have hy : (y.val : AddCircle T) = e.symm w := AddCircle.coe_equivIco
  have hval : f x.val = f y.val := by
    change hper.lift (e.symm z) = hper.lift (e.symm w) at hzw
    rw [← hx, ← hy, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at hzw
    exact hzw
  have hxy : x.val = y.val :=
    hi (by simpa only [zero_add] using x.property) (by simpa only [zero_add] using y.property)
      hval
  apply e.symm.injective
  rw [← hx, ← hy, hxy]

/-- The induced map on `Circle` has the same image as `f`. -/
theorem CircleGluing.periodicCircle_range {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) : Set.range (periodicCircle hT hper) = Set.range f := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    have hh := congrFun (periodicCircle_comp_exp hT hper) t
    exact ⟨T / (2 * Real.pi) * t, hh.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp (2 * Real.pi / T * t), periodicCircle_exp hT hper t⟩

/-- The induced map on `Circle` is smooth when `f` is. -/
theorem CircleGluing.periodicCircle_contMDiff {N : Type*} {T : ℝ} {f : ℝ → N} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0) (hper : Function.Periodic f T)
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) : ContMDiff (𝓡 1) J ∞ (periodicCircle hT hper) := by
  apply contMDiff_of_comp_circleExp
  rw [periodicCircle_comp_exp]
  exact hf.comp (contDiff_const.mul contDiff_id).contMDiff

/-- Injectivity of the derivative of a curve is preserved by rescaling the parameter by a
nonzero constant. -/
theorem CircleGluing.injective_mfderiv_curve_const_mul {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N} {s a : ℝ} (ha : a ≠ 0)
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (a * s))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (a * s))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (a * t)) s) := by
  have hd : HasDerivAt (fun t : ℝ => a * t) a s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul a
  have hmul : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => a * t) s) := by
    rw [mfderiv_eq_fderiv]
    have hh : Function.Injective (fderiv ℝ (fun t : ℝ => a * t) s) := by
      rw [hd.hasFDerivAt.fderiv]
      exact smul_left_injective ℝ ha
    exact hh
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => a * t)) s)
  rw [mfderiv_comp s hα hd.differentiableAt.mdifferentiableAt]
  intro x y hxy
  exact hmul (hi hxy)

/-- The induced map on `Circle` is an immersion when `f` is. -/
theorem CircleGluing.periodicCircle_derivative_injective {N : Type*} {T : ℝ} {f : ℝ → N}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0)
    (hper : Function.Periodic f T) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hi : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (z : Circle) :
    Function.Injective (mfderiv (𝓡 1) J (periodicCircle hT hper) z) := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hc : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicCircle hT hper ∘ Circle.exp) t) := by
    rw [periodicCircle_comp_exp]
    exact
      injective_mfderiv_curve_const_mul
        (div_ne_zero hT (mul_ne_zero (by norm_num) Real.pi_ne_zero))
        (hf.mdifferentiableAt (by simp)) (hi _)
  rw [mfderiv_comp t ((periodicCircle_contMDiff hT hper hf).mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hc
  have hs := ((circleExp_localDiffeomorph t).mfderivToContinuousLinearEquiv (by simp)).surjective
  intro x y hxy
  obtain ⟨u, hu⟩ := hs x
  obtain ⟨v, hv⟩ := hs y
  have hux : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u = x := hu
  have hvy : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v = y := hv
  have huv : u = v :=
    hc
      (by
        change
          mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u) =
            mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v)
        rw [hux, hvy]
        exact hxy)
  exact hux.symm.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) huv).trans hvy)

end
