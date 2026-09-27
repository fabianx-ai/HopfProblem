/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.Suspension
import Lib.Geometry.Manifold.Morse.Connection.TimeChange

/-!
# Realising a level isotopy by the flow

* `mfderiv_height_div_const`, `mvfderiv_height_div_const`, `criticalPoints_height_div_const`,
  `descending_height_div_const_iff`, `exists_normalized_whole_level_cylinder`: after a time
  change, a whole regular level `{f = c}` has a flow cylinder chart `A (p, t) = G t p` with
  `f (A (p, t)) = c - r t` for `t ∈ [0, 1]`.
* `nativeSuspensionField_height`, `nativeSuspensionField_ne_zero`,
  `nativeSuspensionField_eq_vertical_of_flow_germ`, `nativeSuspensionField_eq_vertical_off_base`,
  `nativeSuspensionField_eq_vertical_below`, `nativeSuspensionField_eq_vertical_above`,
  `nativeSuspensionFlow_fixed_line`, `exists_compact_native_level_suspension`: the suspension
  field of a compactly supported isotopy is vertical outside `K × [1/3, 2/3]`.
* `mvfderiv_native_model_pullback`, `mvfderiv_native_level_height`: the height derivative of a
  pulled-back field.
* `exists_native_whole_level_holonomy`: a supported relative isotopy `D` of the level is
  realised by a new descent field `V'`, equal to `V` outside a compact subset of the band, whose
  flow `G` satisfies `G 1 (A (x, 0)) = A (D x, 1)`; `native_whole_level_exterior_tails` and
  `exists_native_regular_level_isotopy_realization` (for `D` isotopic to the identity).
* `whole_level_basins_of_holonomy`, `unique_connection_of_level_basin_intersection`: the new
  flow has the old backward basins on the level and the `D`-transported forward basins; if
  these meet in a single point `z` of the level, the new flow has a unique connecting orbit.

cf. Milnor, *Lectures on the h-cobordism theorem*, §4 and §5 (the isotopy of the level surface
that moves the descending sphere off the ascending one is realised by the gradient-like field).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Normalized level cylinders -/

/-- The derivative of height divided by a constant. -/
theorem FlowTimeChange.mfderiv_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x = r⁻¹ • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : (fun y => f y / r) = r⁻¹ • f := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact (hf.hasMFDerivAt.const_smul r⁻¹).mfderiv

/-- The manifold derivative of the scaled height. -/
theorem FlowTimeChange.mvfderiv_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v = mvfderiv 𝓘(ℝ, E) f x v / r := by
  have heq : (fun y => f y / r) = (fun y => r⁻¹ * f y) := by
    ext y
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq, mvfderiv_fun_mul mdifferentiableAt_const hf]
  have hconst : mvfderiv 𝓘(ℝ, E) (fun _ : M => r⁻¹) x = 0 := by simp [mvfderiv, mfderiv_const]
  simp [hconst, div_eq_mul_inv, mul_comm]

/-- The scaled height's critical points. -/
theorem FlowTimeChange.criticalPoints_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {r : ℝ} (hr : r ≠ 0) :
    ManifoldMorse.criticalPoints E (fun y => f y / r) =
      ManifoldMorse.criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_height_div_const (hf.mdifferentiableAt (by simp))]
  exact smul_eq_zero.trans (or_iff_right (inv_ne_zero hr))

/-- Descending the scaled height is the scaled descent. -/
theorem FlowTimeChange.descending_height_div_const_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) {r : ℝ} (hr : 0 < r)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v < 0 ↔ mvfderiv 𝓘(ℝ, E) f x v < 0 := by
  rw [mvfderiv_height_div_const hf r]
  rw [div_lt_iff₀ hr, MulZeroClass.zero_mul]

/-- A normalized whole-level cylinder exists. -/
theorem FlowTimeChange.exists_normalized_whole_level_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ (r : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M) (A :
      PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ y : M // f y = c } × ℝ) M ∞),
      0 < r ∧
        r < c - a ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
              (∀ y, W y = 0 ↔ V y = 0) ∧
                (∀ y,
                    y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
                  (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 y, W x = V x) ∧
                    (∀ y,
                        Set.range (fun t => G t y) = Set.range (fun t => F t y) ∧
                          (∀ p,
                              Filter.Tendsto (fun t => G t y) Filter.atTop (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                            ∀ p,
                              Filter.Tendsto (fun t => G t y) Filter.atBot (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                      A.source = Set.univ ∧
                        A.target = FlowCancellation.levelBasin G f c ∧
                          (∀ p, A p = G p.2 p.1) ∧
                            (∀ p, p.2 ∈ Set.Icc (0 : ℝ) 1 → f (A p) = c - r * p.2) ∧
                              ∀ y ∈ A.target,
                                W y =
                                  VectorField.mpullback 𝓘(ℝ, E)
                                    (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) A.symm
                                    FlowSuspension.nativeVerticalField y := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let r : ℝ := (c - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr ha) (by norm_num)
  have hrbound : r < c - a := by dsimp [r]; linarith
  let g : M → ℝ := fun y => f y / r
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g := hf.div_const r
  have hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f :=
    criticalPoints_height_div_const hf hr.ne'
  have hdescent :
    ∀ y, y ∉ ManifoldMorse.criticalPoints E g → mvfderiv 𝓘(ℝ, E) g y (V y) < 0 := by
    intro y hy
    rw [hcrit] at hy
    exact
      (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (V y)).mpr (hdesc y hy)
  have hregular :
    ∀ y, g y ∈ Set.Icc (a / r) (b / r) → y ∉ ManifoldMorse.criticalPoints E g := by
    intro y hy
    rw [hcrit]
    exact
      hband y ⟨(div_le_div_iff_of_pos_right hr).mp hy.1, (div_le_div_iff_of_pos_right hr).mp hy.2⟩
  obtain ⟨U, W, G, hU, hIU, hW, hG, hzero, hneg, hspeed, hgerm, -, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hg hV hdescent F hF hregular
  have hnegf (y : M) (hy : y ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f y (W y) < 0 :=
    (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (W y)).mp
      (hneg y (hcrit ▸ hy))
  obtain ⟨A, hsource, htarget, hformula, hfield⟩ :=
    FlowSuspension.exists_native_level_flow_cylinder_with_field hf hreg hW G hG
      (fun y hy => hnegf y (hreg y hy)) z
  have hc : c / r ∈ Set.Icc (a / r) (b / r) :=
    ⟨div_le_div_of_nonneg_right ha.le hr.le, div_le_div_of_nonneg_right hb.le hr.le⟩
  refine
    ⟨r, W, G, A, hr, hrbound, hW, hG, hzero, hnegf, (fun y hy => hgerm y (hcrit ▸ hy)), hgeometry,
      hsource, htarget, hformula, ?_, hfield⟩
  intro p ht
  have hi : g p.1 = c / r := by change f p.1 / r = c / r; rw [p.1.property]
  have he : c / r - p.2 = (c - r * p.2) / r := by field_simp
  have hend : g p.1 - p.2 ∈ Set.Icc (a / r) (b / r) := by
    rw [hi, he]
    constructor
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [ht.2]
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [mul_nonneg hr.le ht.1]
  have hh := native_local_height_translation hg G hG hU hIU hspeed p.1 p.2 (hi ▸ hc) hend
  rw [hi, he] at hh
  rw [hformula]
  exact (div_left_inj' hr.ne').mp hh

/-! ### The native suspension field -/

/-- The native suspension field's height is one. -/
theorem FlowSuspension.nativeSuspensionField_height {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) : (nativeSuspensionField Ψ p).2 = 1 := by
  let q := Ψ.symm p
  have hproj : (Prod.snd : N × ℝ → ℝ) ∘ Ψ = Prod.snd := funext hheight
  have hc :=
    mfderiv_comp q
      (show MDifferentiableAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : N × ℝ → ℝ) (Ψ q) from
        mdifferentiableAt_snd)
      (Ψ.contMDiff.mdifferentiableAt (by simp))
  rw [hproj, mfderiv_snd, mfderiv_snd] at hc
  have hv := congrArg (fun L : (Z × ℝ) →L[ℝ] ℝ => L (0, 1)) hc
  change (1 : ℝ) = (nativeSuspensionField Ψ p).2 at hv
  exact hv.symm

/-- The native suspension field is nonvanishing. -/
theorem FlowSuspension.nativeSuspensionField_ne_zero {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) : nativeSuspensionField Ψ p ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : Z × ℝ => v.2) hz
  rw [nativeSuspensionField_height Ψ hheight p] at hh
  exact one_ne_zero hh

/-- The suspension field is vertical where the flow germ is trivial. -/
theorem FlowSuspension.nativeSuspensionField_eq_vertical_of_flow_germ {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (p : N × ℝ)
    (heq : (fun t : ℝ => nativeSuspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t : ℝ => (p.1, p.2 + t))) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hw := nativeSuspensionFlow_integralCurve Ψ p 0
  have hv := nativeVerticalField_integralCurve (Z := Z) p 0
  have hh := hw.mfderiv.symm.trans (heq.mfderiv_eq.trans hv.mfderiv)
  have hval := congrArg (fun L : ℝ →L[ℝ] (Z × ℝ) => L 1) hh
  change
    (1 : ℝ) • nativeSuspensionField Ψ (nativeSuspensionFlow Ψ 0 p) =
      (1 : ℝ) • nativeVerticalField (p.1, p.2 + 0) at hval
  have h0 : nativeSuspensionFlow Ψ (0 : ℝ) p = p := by
    change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + 0) = p
    rw [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  rw [one_smul, one_smul, h0] at hval
  convert! hval using 1

/-- The suspension field is vertical off the base. -/
theorem FlowSuspension.nativeSuspensionField_eq_vertical_off_base {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {K : Set N}
    (hfix : ∀ p, p.1 ∉ K → Ψ p = p) (p : N × ℝ) (hp : p.1 ∉ K) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hfix p hp)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  apply Filter.Eventually.of_forall
  intro t
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hfix (p.1, p.2 + t) hp

/-- The suspension field is vertical below the support. -/
theorem FlowSuspension.nativeSuspensionField_eq_vertical_below {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {a : ℝ}
    (hleft : ∀ p, p.2 ≤ a → Ψ p = p) (p : N × ℝ) (hp : p.2 < a) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hleft p hp.le)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_lt_nhds (sub_pos.mpr hp)] with t ht
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hleft (p.1, p.2 + t) (by dsimp; linarith)

/-- The suspension field is vertical above the support. -/
theorem FlowSuspension.nativeSuspensionField_eq_vertical_above {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (D : N → N)
    {b : ℝ} (hheight : ∀ p, (Ψ p).2 = p.2) (hright : ∀ p, b ≤ p.2 → Ψ p = (D p.1, p.2))
    (p : N × ℝ) (hp : b < p.2) : nativeSuspensionField Ψ p = nativeVerticalField p := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have htime : q.2 = p.2 := (hheight q).symm.trans (congrArg Prod.snd hq)
  have hbase : D q.1 = p.1 := by
    have hh := hright q (by rw [htime]; exact hp.le)
    rw [hq] at hh
    exact (congrArg Prod.fst hh).symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_gt_nhds (show b - p.2 < (0 : ℝ) by linarith)] with t ht
  change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
  rw [hright (q.1, q.2 + t) (by dsimp; rw [htime]; linarith), hbase, htime]

/-- The suspended flow fixes vertical lines off the support. -/
theorem FlowSuspension.nativeSuspensionFlow_fixed_line {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {x : N}
    (hfix : ∀ s : ℝ, Ψ (x, s) = (x, s)) (s t : ℝ) :
    nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  have hi : Ψ.symm (x, s) = (x, s) := by
    have hh := congrArg Ψ.symm (hfix s)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  change Ψ ((Ψ.symm (x, s)).1, (Ψ.symm (x, s)).2 + t) = _
  rw [hi]
  exact hfix (s + t)

/-- A compactly supported native level suspension exists. -/
theorem FlowSuspension.exists_compact_native_level_suspension {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] [T2Space N]
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N} (hK : IsCompact K)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞,
      IsCompact (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) ∧
        (∀ p, (Ψ p).2 = p.2) ∧
          (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
            (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
              ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
                  (fun p : N × ℝ =>
                    (⟨p, nativeSuspensionField Ψ p⟩ :
                      TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) ∧
                (∀ p,
                    IsMIntegralCurve (fun t : ℝ => nativeSuspensionFlow Ψ t p)
                      (nativeSuspensionField Ψ)) ∧
                  (∀ p, (nativeSuspensionField Ψ p).2 = 1) ∧
                    (∀ p, nativeSuspensionField Ψ p ≠ 0) ∧
                      (∀ p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3),
                          nativeSuspensionField Ψ p = nativeVerticalField p) ∧
                        (∀ p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3),
                            ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q) ∧
                          (∀ x, nativeSuspensionFlow Ψ 1 (x, 0) = (D x, 1)) ∧
                            (∀ t p, (nativeSuspensionFlow Ψ t p).2 = p.2 + t) ∧
                              (∀ x ∉ K, ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t)) ∧
                                ∀ x ∈ S,
                                  ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  obtain ⟨Ψ, hheight, hleft, hright, hout, hfixed⟩ := exists_native_base_suspension D I
  have hC : IsCompact (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) := hK.prod CompactIccSpace.isCompact_Icc
  have hfield (p : N × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hp ⟨hx, ht⟩
      by_cases hlo : p.2 < 1 / 3
      · exact nativeSuspensionField_eq_vertical_below Ψ hleft p hlo
      · have hhi : 2 / 3 < p.2 := lt_of_not_ge (fun hh => ht ⟨le_of_not_gt hlo, hh⟩)
        exact nativeSuspensionField_eq_vertical_above Ψ D hheight hright p hhi
    · exact nativeSuspensionField_eq_vertical_off_base Ψ hout p hx
  have hgerm (p : N × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q := by
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hfield q hq
  refine
    ⟨Ψ, hC, hheight, hleft, hright, contMDiff_nativeSuspensionField Ψ,
      nativeSuspensionFlow_integralCurve Ψ, nativeSuspensionField_height Ψ hheight,
      nativeSuspensionField_ne_zero Ψ hheight, hfield, hgerm, ?_,
      nativeSuspensionFlow_height Ψ hheight, ?_, ?_⟩
  · intro x
    have hzero : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    rw [← hzero, nativeSuspensionFlow_chart, zero_add]
    exact hright (x, 1) (by norm_num)
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hout (x, u) hx) s t
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hfixed (x, u) hx) s t

/-- The manifold derivative of the native model pullback. -/
theorem FlowSuspension.mvfderiv_native_model_pullback {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (W : (z : X) → TangentSpace I z) {x : M}
    (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x (VectorField.mpullback 𝓘(ℝ, E) I A.symm W x) =
      mvfderiv I (f ∘ A) (A.symm x) (W (A.symm x)) := by
  rw [native_model_pullback_eq_mfderiv_symm A.symm W hx]
  exact
    (mvfderiv_comp_apply_of_eq (A.symm x) (hf.mdifferentiableAt (by simp))
        ((A.contMDiffOn_toFun.contMDiffAt
              (A.open_source.mem_nhds (A.map_target' hx))).mdifferentiableAt
          (by simp))
        (A.right_inv' hx) (W (A.symm x))).symm

/-- The manifold derivative of the native level height. -/
theorem FlowSuspension.mvfderiv_native_level_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b s : ℝ}
    (hheight : ∀ p ∈ A.source, f (A p) = b - s * p.2)
    (W : (p : N × ℝ) → TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p) {x : M} (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm W x) =
      -s * (W (A.symm x)).2 := by
  let q := A.symm x
  have heq : (f ∘ A) =ᶠ[𝓝 q] (fun p : N × ℝ => b - s * p.2) := by
    filter_upwards [A.open_source.mem_nhds (A.map_target' hx)] with p hp
    exact hheight p hp
  have hd :
    mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q =
      mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : N × ℝ => b - s * p.2) q :=
    heq.mfderiv_eq
  rw [mvfderiv_native_model_pullback A hf W hx]
  change mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q (W q) = _
  rw [hd]
  have hsnd :
    HasMFDerivAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : N × ℝ → ℝ) q
      (ContinuousLinearMap.snd ℝ Z ℝ) :=
    hasMFDerivAt_snd q
  have hh :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) b q).sub
      ((hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) s q).mul hsnd)
  have hh' :
    mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : N × ℝ => b - s * p.2) q =
      (0 : (Z × ℝ) →L[ℝ] ℝ) - (s • ContinuousLinearMap.snd ℝ Z ℝ + q.2 • (0 : (Z × ℝ) →L[ℝ] ℝ)) :=
    hh.mfderiv
  rw [hh']
  change (0 : ℝ) - (s * (W q).2 + q.2 * (0 : ℝ)) = -s * (W q).2
  ring

/-- A native whole-level holonomy exists. -/
theorem FlowSuspension.exists_native_whole_level_holonomy {Z E N M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N] [T2Space N] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b s : ℝ}
    (hs : 0 < s) (hheight : ∀ p, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A p) = b - s * p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ A.target,
        V x = VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N} (hK : IsCompact K)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (C : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (Ψ :
      Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞),
      IsCompact C ∧
        C ⊆ A.target ∩ f ⁻¹' Set.Ioo (b - s) b ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
              (∀ x, V' x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (V' x) < 0) ∧
                  (∀ x ∉ C, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                    (∀ x ∈ A.target, ∀ t, G t x ∈ A.target) ∧
                      (∀ x ∉ A.target, ∀ t, G t x = H t x) ∧
                        (∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) ∧
                          (∀ x, G 1 (A (x, 0)) = A (D x, 1)) ∧
                            (∀ x ∈ S, ∀ u t : ℝ, G t (A (x, u)) = A (x, u + t)) ∧
                              (∀ p, (Ψ p).2 = p.2) ∧
                                (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
                                  (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
                                    ∀ x ∈ A.target,
                                      V' x =
                                        VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
                                          A.symm (nativeSuspensionField Ψ) x := by
  obtain
    ⟨Ψ, hL, hΨheight, hleft, hright, hW, hF, hWheight, hWzero, hfix, -, hend, -, -, hfixed⟩ :=
    exists_compact_native_level_suspension D hK I
  let L : Set (N × ℝ) := K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)
  have hLA : L ⊆ A.source := by rw [hsource]; exact Set.subset_univ L
  have hvertical (p : N × ℝ) (_ : p ∈ A.source) : nativeVerticalField (Z := Z) p ≠ 0 := by
    intro hz
    have hh := congrArg (fun v : Z × ℝ => v.2) hz
    exact one_ne_zero hh
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ :=
    exists_native_model_field_replacement A V hV nativeVerticalField (nativeSuspensionField Ψ) hW
      hmodel hvertical (fun p _ => hWzero p) hL hLA hfix
  let C := A '' L
  have hC : IsCompact C := hL.image_of_continuousOn (A.contMDiffOn_toFun.continuousOn.mono hLA)
  have hslab (p : N × ℝ) (hp : p ∈ L) : p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hCsub : C ⊆ A.target ∩ f ⁻¹' Set.Ioo (b - s) b := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨A.map_source' (hLA hp), ?_⟩
    change f (A p) ∈ Set.Ioo (b - s) b
    rw [hheight p (hslab p hp)]
    constructor <;> nlinarith [(hslab p hp).1, (hslab p hp).2]
  let R :=
    PartialChart.restrictSource A
      (isOpen_univ.prod (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)))
  have hRheight (p : N × ℝ) (hp : p ∈ R.source) : f (R p) = b - s * p.2 := hheight p hp.2.2
  have hnegC (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V' x) = -s := by
    rcases hx with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hLA hp, Set.mem_univ _, hslab p hp⟩
    rw [hnew (A p) (A.map_source' (hLA hp))]
    change
      mvfderiv 𝓘(ℝ, E) f (R p)
          (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) R.symm (nativeSuspensionField Ψ)
            (R p)) =
        -s
    rw [mvfderiv_native_level_height R hf hRheight _ (R.map_source' hpR), hWheight, mul_one]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : N × ℝ) (t : ℝ) : nativeSuspensionFlow Ψ t p ∈ A.source := by
    rw [hsource]
    exact Set.mem_univ _
  have hfull (p : N × ℝ) (t : ℝ) : G t (A p) = A (nativeSuspensionFlow Ψ t p) :=
    native_model_flow_all_time A hV'₁ G hG (nativeSuspensionFlow Ψ) (nativeSuspensionField Ψ) hF
      hnew (hstay p) t
  have hinv :=
    native_model_target_invariant A hV'₁ G hG (nativeSuspensionFlow Ψ) (nativeSuspensionField Ψ)
      hF hnew (fun p _ => hstay p)
  have hcomp := flow_complement_invariant G hinv
  refine
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, ?_, hgerm, hinv, ?_, hfull, ?_, ?_, hΨheight, hleft,
      hright, hnew⟩
  · intro x hx
    by_cases hc : x ∈ C
    · rw [hnegC x hc]
      exact neg_neg_of_pos hs
    · rw [(hgerm x hc).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (u : ℝ) : V' (G u x) = V (G u x) :=
      (hgerm (G u x) (fun h => hcomp x hx u (hCsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (hV.of_le (by simp)) H G hH hG
          (fun u _ => hagree u) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (hV.of_le (by simp)) H G hH hG
          (fun u _ => hagree u) t ht
  · intro x
    rw [hfull, hend]
  · intro x hx u t
    rw [hfull, hfixed x hx u t]

/-- The whole-level exterior tails of the holonomy. -/
theorem FlowSuspension.native_whole_level_exterior_tails {Z N M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] [TopologicalSpace M] (A : N × ℝ → M) (ι : N → M)
    (H G : Flow ℝ M) (hformula : ∀ p, A p = H p.2 (ι p.1)) (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hleft : ∀ p, p.2 ≤ 1 / 3 → Ψ p = p) (hright : ∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2))
    (hfull : ∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) :
    (∀ x, ∀ t : ℝ, t ≤ 0 → G t (A (x, 0)) = H t (A (x, 0))) ∧
      ∀ x, ∀ t : ℝ, 0 ≤ t → G t (A (x, 1)) = H t (A (x, 1)) := by
  constructor
  · intro x t ht
    have h0 : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    have hf : nativeSuspensionFlow Ψ t (x, 0) = (x, t) := by
      rw [← h0, nativeSuspensionFlow_chart, zero_add]
      exact hleft (x, t) (by linarith)
    rw [hfull, hf, hformula, hformula, H.map_zero_apply]
  · intro x t ht
    have h1 : Ψ (D.symm x, (1 : ℝ)) = (x, 1) := by
      rw [hright (D.symm x, 1) (by norm_num), D.apply_symm_apply]
    have hf : nativeSuspensionFlow Ψ t (x, 1) = (x, 1 + t) := by
      rw [← h1, nativeSuspensionFlow_chart]
      rw [hright (D.symm x, 1 + t) (by linarith), D.apply_symm_apply]
    rw [hfull, hf, hformula, hformula, ← H.map_add]
    congr 1
    ring

/-- A regular level isotopy is realized by a suspension. -/
theorem FlowSuspension.exists_native_regular_level_isotopy_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = c } { y : M // f y = c } ∞,
      SupportedDiffeomorph.IsotopicToIdentity D →
        ∃ (r : ℝ) (C : Set M) (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
          0 < r ∧
            r < c - a ∧
              IsCompact C ∧
                C ⊆ f ⁻¹' Set.Ioo a b ∧
                  ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                      (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                    (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
                      (∀ y,
                          Set.range (fun t => H t y) = Set.range (fun t => F t y) ∧
                            (∀ p,
                                Filter.Tendsto (fun t => H t y) Filter.atTop (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                              ∀ p,
                                Filter.Tendsto (fun t => H t y) Filter.atBot (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                            (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                          (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
                            (∀ y, V' y = 0 ↔ V y = 0) ∧
                              (∀ y,
                                  y ∉ ManifoldMorse.criticalPoints E f →
                                    mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
                                (∀ y ∈ ManifoldMorse.criticalPoints E f,
                                    ∀ᶠ x in 𝓝 y, V' x = V x) ∧
                                  (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
                                    (∀ x : { y : M // f y = c }, G 1 x = H 1 (D x)) ∧
                                      (∀ x : { y : M // f y = c }, f (H 1 x) = c - r) ∧
                                        (∀ x : { y : M // f y = c },
                                            ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
                                          ∀ x : { y : M // f y = c },
                                            ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let L := { y : M // f y = c }
  let _ : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro D hD
  obtain ⟨B, hB, hBzero, hBone, hBslices⟩ := hD
  let I : SupportedDiffeomorph.SupportedRelativeIsotopy D Set.univ ∅ :=
    { family := B
      smooth := hB
      zero := hBzero
      one := hBone
      slices := fun t => by
        obtain ⟨d, hd⟩ := hBslices t
        exact ⟨d, fun x => (hd x).symm⟩
      fixedOutside := fun _ x hx => (hx (Set.mem_univ x)).elim
      fixedOn := fun _ _ hx => hx.elim }
  obtain
    ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm, hgeometry, hsource, -, hformula,
      hheight, hmodel⟩ :=
    FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF ha hb hband hreg
      z
  obtain
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm, -, -, hfull, hend, -, -, hleft, hright,
      -⟩ :=
    exists_native_whole_level_holonomy A hsource hf hr (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩)
      W hW hmodel H hH D isCompact_univ I
  have hCband : C ⊆ f ⁻¹' Set.Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Set.Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft hright hfull
  have hA0 (x : L) : A (x, 0) = (x : M) := by rw [hformula, H.map_zero_apply]
  have hA1 (x : L) : A (x, 1) = H 1 x := hformula (x, 1)
  refine
    ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV', hG, fun y =>
      (hzero y).trans (hWzero y), fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_,
      ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht

/-- The whole-level basins of the holonomy. -/
theorem FlowSuspension.whole_level_basins_of_holonomy {X M : Type*} [TopologicalSpace M]
    (F H G : Flow ℝ M) (ι : X → M) (D : X → X)
    (hHtop :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hHbot :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hend : ∀ x, G 1 (ι x) = H 1 (ι (D x))) (hleft : ∀ x, ∀ t : ℝ, t ≤ 0 → G t (ι x) = H t (ι x))
    (hright : ∀ x, ∀ t : ℝ, 0 ≤ t → G t (H 1 (ι x)) = H t (H 1 (ι x))) :
    (∀ x p,
        Filter.Tendsto (fun t => G t (ι x)) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t (ι x)) Filter.atBot (𝓝 p)) ∧
      ∀ x p,
        Filter.Tendsto (fun t => G t (ι x)) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => F t (ι (D x))) Filter.atTop (𝓝 p) := by
  constructor
  · intro x p
    have heq : (fun t => G t (ι x)) =ᶠ[Filter.atBot] (fun t => H t (ι x)) := by
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft x t ht
    exact (Filter.tendsto_congr' heq).trans (hHbot (ι x) p)
  · intro x p
    have heq : (fun t => G t (H 1 (ι (D x)))) =ᶠ[Filter.atTop] (fun t => H t (H 1 (ι (D x)))) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright (D x) t ht
    calc
      Filter.Tendsto (fun t => G t (ι x)) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => G t (G 1 (ι x))) Filter.atTop (𝓝 p) :=
        (MorseCancellation.flow_time_atTop_limit_iff G 1 (ι x) p).symm
      _ ↔ Filter.Tendsto (fun t => G t (H 1 (ι (D x)))) Filter.atTop (𝓝 p) := by rw [hend]
      _ ↔ Filter.Tendsto (fun t => H t (H 1 (ι (D x)))) Filter.atTop (𝓝 p) :=
        (Filter.tendsto_congr' heq)
      _ ↔ Filter.Tendsto (fun t => H t (ι (D x))) Filter.atTop (𝓝 p) :=
        (MorseCancellation.flow_time_atTop_limit_iff H 1 (ι (D x)) p)
      _ ↔ Filter.Tendsto (fun t => F t (ι (D x))) Filter.atTop (𝓝 p) := hHtop (ι (D x)) p

/-- A unique connection is determined by basin intersection. -/
theorem FlowSuspension.unique_connection_of_level_basin_intersection {M : Type*}
    [TopologicalSpace M] (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c) (D : { x : M // f x = c } → { x : M // f x = c })
    (hback :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hforward :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) ↔
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q))
    (z : { y : M // f y = c }) (hzback : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 p))
    (hzforward : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 q))
    (hunique :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) →
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q) → x = z) :
    Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 p) ∧
      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 q) ∧
        ∀ x,
          Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) →
            Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) → ∃ t, G t z = x := by
  refine ⟨(hback z).mpr hzback, (hforward z).mpr hzforward, ?_⟩
  intro x hxback hxforward
  obtain ⟨s, hs⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits G hf hxback hxforward hpc hqc
  let u : { y : M // f y = c } := ⟨G s x, hs⟩
  have hub : Filter.Tendsto (fun t => G t u) Filter.atBot (𝓝 p) :=
    (MorseCancellation.flow_time_atBot_limit_iff G s x p).mpr hxback
  have huf : Filter.Tendsto (fun t => G t u) Filter.atTop (𝓝 q) :=
    (MorseCancellation.flow_time_atTop_limit_iff G s x q).mpr hxforward
  have huz : u = z := hunique u ((hback u).mp hub) ((hforward u).mp huf)
  have hv : G s x = (z : M) := congrArg Subtype.val huz
  refine ⟨-s, ?_⟩
  rw [← hv, ← G.map_add, neg_add_cancel, G.map_zero_apply]

end
