/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The Morse block of a gradient-like flow near a critical point

Let `c` be a signed Morse chart of `f` at `p` and `V` a vector field with flow `F` which agrees
with the descent field of `c` near `p`.  In the split coordinates `(z₋, z₊)` of the chart the flow
is the linear model `MorseHandle.descentFlow`, and on a small box `‖z₋‖, ‖z₊‖ ≤ r`:

* a point with `z₋ ≠ 0` leaves the box forwards through a level below `f p`, a point with
  `z₊ ≠ 0` leaves it backwards through a level above `f p`
  (`MorseCancellation.exists_forward_morse_model_exit`, `exists_native_forward_morse_exit` and the
  backward twins);
* points of the plane `z₋ = 0` converge to `p` as `t → ∞`, points of `z₊ = 0` as `t → -∞`
  (`native_morse_positive_plane_limit`, `native_morse_negative_plane_limit`);
* hence, if `f` is non-increasing along the flow, the forward (backward) basin of `p` meets the
  box exactly in the plane `z₋ = 0` (`z₊ = 0`): `exists_native_morse_basin_block`,
  `exists_descending_morse_basin_block`;
* the attaching sphere and the belt sphere of radius `r` flow by the linear model and converge to
  `p` backwards, respectively forwards (`native_attaching_core_flow`,
  `native_attaching_core_backward_limit`, `native_belt_core_flow`, `native_belt_core_forward_limit`).

These are the local stable and unstable discs of a critical point, cf. Milnor, *Lectures on the
h-cobordism theorem*, §3–§4 (the discs `D_L`, `D_R` of a gradient-like field).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The forward flow exits a Morse model block. -/
theorem MorseCancellation.exists_forward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ T : ℝ,
      0 < T ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
            MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          MorseHandle.quadratic (MorseHandle.descentFlow T z) < 0 := by
  let T := Real.log (r / ‖z.1‖)
  have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.1‖ := (one_lt_div hn).mpr hzn
  have hT : 0 < T := Real.log_pos hratio
  have hexp : Real.exp T = r / ‖z.1‖ := Real.exp_log (div_pos hr hn)
  have hnorm : ‖(MorseHandle.descentFlow T z).1‖ = r := by
    rw [MorseHandle.norm_descentFlow_fst, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall : ‖(MorseHandle.descentFlow T z).2‖ < r :=
    (MorseHandle.norm_snd_descentFlow_le hT.le z).trans_lt hzp
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      calc
        Real.exp t * ‖z.1‖ ≤ Real.exp T * ‖z.1‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
    · exact
        mem_closedBall_zero_iff.mpr
          ((MorseHandle.norm_snd_descentFlow_le ht.1 z).trans hzp.le)
  · change
      -‖(MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(MorseHandle.descentFlow T z).2‖ ^ 2 <
        0
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hsmall
    linarith

/-- The backward flow exits a Morse model block. -/
theorem MorseCancellation.exists_backward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ T : ℝ,
      T < 0 ∧
        (∀ t ∈ Set.Icc T (0 : ℝ),
            MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          0 < MorseHandle.quadratic (MorseHandle.descentFlow T z) := by
  let T := -Real.log (r / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.2‖ := (one_lt_div hn).mpr hzp
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = r / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hr hn)]
  have hnorm : ‖(MorseHandle.descentFlow T z).2‖ = r := by
    rw [MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(MorseHandle.descentFlow t z).1‖ < r := by
    rw [MorseHandle.norm_descentFlow_fst]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans_lt hzn
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · exact mem_closedBall_zero_iff.mpr (hsmall t ht.2).le
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
  · change
      0 <
        -‖(MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (hsmall T hT.le)
    linarith

attribute [local instance 100] Classical.propDecidable in
/-- A native Morse field block exists. -/
theorem MorseCancellation.exists_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀
            z ∈
              Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) r,
            ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hcont :
    Filter.Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
      (𝓝 p) := by
    have hh :
      Filter.Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
        (𝓝 (c.splitChart.symm 0)) :=
      c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0
    rwa [hcenter] at hh
  have htarget :
    ∀ᶠ z in 𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates), z ∈ c.splitChart.target :=
    c.splitChart.open_target.mem_nhds h0
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ x in 𝓝 y, V x = c.descentField x :=
    eventually_eventually_nhds.mpr heq
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (htarget.and (hcont.eventually hgerm))
  have hblock (z)
    (hz :
      z ∈
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r) :=
    hsub
      (by
        rw [closedBall_prod_same] at hz
        convert! hz using 1)
  exact ⟨r, hr, fun z hz => (hblock z hz).1, fun z hz => (hblock z hz).2⟩

attribute [local instance 100] Classical.propDecidable in
/-- The native forward flow exits the Morse block. -/
theorem MorseCancellation.exists_native_forward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).1 ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ f (F T x) < f p := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_forward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :
    MorseHandle.descentFlow s (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [Set.uIcc_of_le hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨hT.le, le_rfl⟩))]
  change
    -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 <
      0 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
/-- The native backward flow exits the Morse block. -/
theorem MorseCancellation.exists_native_backward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).2 ≠ 0) :
    ∃ T : ℝ, T < 0 ∧ f p < f (F T x) := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_backward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :
    MorseHandle.descentFlow s (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [Set.uIcc_of_ge hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨le_rfl, hT.le⟩))]
  change
    0 <
      -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
/-- The native flow's forward limit lies on the positive plane. -/
theorem MorseCancellation.native_morse_positive_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hp : ‖(c.splitChart x).2‖ < r)
    (hzero : (c.splitChart x).1 = 0) : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
    MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst, hzero, norm_zero,
        MulZeroClass.mul_zero]
      exact hr.le
    · exact
        mem_closedBall_zero_iff.mpr
          ((MorseHandle.norm_snd_descentFlow_le ht (c.splitChart x)).trans hp.le)
  have hflow :=
    c.flow_eqOn_descentModel hV F hF hx isPreconnected_Ici (le_refl (0 : ℝ))
      (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst :
    Filter.Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) Filter.atTop
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hsecond :
    Filter.Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) Filter.atTop
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simpa only [Function.comp_def, zero_smul] using
      (Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot).smul_const (c.splitChart x).2
  have hlim :
    Filter.Tendsto (fun t => MorseHandle.descentFlow t (c.splitChart x)) Filter.atTop
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hn :
    Filter.Tendsto (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atTop (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hn
  apply hn.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
/-- The native flow's backward limit lies on the negative plane. -/
theorem MorseCancellation.native_morse_negative_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hzero : (c.splitChart x).2 = 0) : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Set.Iic (0 : ℝ)) :
    MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans hn.le
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd, hzero, norm_zero,
        MulZeroClass.mul_zero]
      exact hr.le
  have hflow :=
    c.flow_eqOn_descentModel hV F hF hx isPreconnected_Iic (le_refl (0 : ℝ))
      (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst :
    Filter.Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) Filter.atBot
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simpa only [zero_smul] using Real.tendsto_exp_atBot.smul_const (c.splitChart x).1
  have hsecond :
    Filter.Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) Filter.atBot
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hlim :
    Filter.Tendsto (fun t => MorseHandle.descentFlow t (c.splitChart x)) Filter.atBot
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hh :
    Filter.Tendsto (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atBot (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
/-- A native Morse basin block exists. -/
theorem MorseCancellation.exists_native_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀ x ∈ c.splitChart.source,
            ‖(c.splitChart x).1‖ < r →
              ‖(c.splitChart x).2‖ < r →
                (Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
                  (Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) :=
  by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  refine ⟨r, hr, hbox, ?_⟩
  intro x hx hn hp
  constructor
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ :=
        exists_native_forward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f p)) :=
        hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).le_of_tendsto hheight T)) hexit
    · exact native_morse_positive_plane_limit c hV F hF hr hbox hfield hx hp
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ :=
        exists_native_backward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
        hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).ge_of_tendsto hheight T)) hexit
    · exact native_morse_negative_plane_limit c hV F hF hr hbox hfield hx hn

attribute [local instance 100] Classical.propDecidable in
/-- A descending Morse basin block exists. -/
theorem MorseCancellation.exists_descending_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀ x ∈ c.splitChart.source,
            ‖(c.splitChart x).1‖ < r →
              ‖(c.splitChart x).2‖ < r →
                (Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
                  (Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) :=
  exists_native_morse_basin_block c hf.continuous hV F hF
    (FlowConstruction.antitone_flow_height hf F hF hzero hdesc) heq

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core's backward limit is the critical point. -/
theorem MorseCancellation.native_attaching_core_backward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
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
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Filter.Tendsto (fun t => F t (c.attachingCoreMap r hr hblock u)) Filter.atBot (𝓝 p) := by
  have hu : ‖(u : c.NegativeCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hn : ‖r • (u : c.NegativeCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hcoords :
    (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) ∈ c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, hn]
      linarith
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
  have hcoord :
    c.splitChart
        (c.splitChart.symm (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) =
      (r • (u : c.NegativeCoordinates), 0) :=
    c.splitChart.right_inv' hcoords
  have hh :=
    native_morse_negative_plane_limit c hV F hF (x :=
      c.splitChart.symm (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)))
      (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
      (by rw [hcoord]; change ‖r • (u : c.NegativeCoordinates)‖ < 2 * r; rw [hn]; linarith)
      (by rw [hcoord])
  simpa only [c.attachingCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The belt core's forward limit is the critical point. -/
theorem MorseCancellation.native_belt_core_forward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
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
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Filter.Tendsto (fun t => F t (c.beltCoreMap r hr hblock v)) Filter.atTop (𝓝 p) := by
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hn : ‖r • (v : c.PositiveCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one]
  have hcoords :
    ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)) ∈ c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
    · rw [mem_closedBall_zero_iff, hn]
      linarith
  have hcoord :
    c.splitChart
        (c.splitChart.symm ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates))) =
      (0, r • (v : c.PositiveCoordinates)) :=
    c.splitChart.right_inv' hcoords
  have hh :=
    native_morse_positive_plane_limit c hV F hF (x :=
      c.splitChart.symm ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)))
      (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
      (by rw [hcoord]; change ‖r • (v : c.PositiveCoordinates)‖ < 2 * r; rw [hn]; linarith)
      (by rw [hcoord])
  simpa only [c.beltCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core is flowed by the native field. -/
theorem MorseCancellation.native_attaching_core_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
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
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) {t : ℝ} (ht : t ≤ 0) :
    F t (c.attachingCoreMap r hr hblock u) =
      c.splitChart.symm (MorseHandle.descentFlow t (r • (u : c.NegativeCoordinates), 0)) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (r • (u : c.NegativeCoordinates), 0)
  have hn : ‖z.1‖ = r := by
    change ‖r • (u : c.NegativeCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property,
      mul_one]
  have hstay (s : ℝ) (hs : s ≤ 0) :
    MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hs) hr.le
      nlinarith
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      change Real.exp (-s) * ‖(0 : c.PositiveCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, MulZeroClass.mul_zero]
      positivity
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow :=
    c.flow_eqOn_descentModel hV F hF (x := c.splitChart.symm z) (c.splitChart.map_target' hz)
      isPreconnected_Iic (le_refl (0 : ℝ)) (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
      (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.attachingCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The belt core is flowed by the native field. -/
theorem MorseCancellation.native_belt_core_flow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
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
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) {t : ℝ} (ht : 0 ≤ t) :
    F t (c.beltCoreMap r hr hblock v) =
      c.splitChart.symm (MorseHandle.descentFlow t (0, r • (v : c.PositiveCoordinates))) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (0, r • (v : c.PositiveCoordinates))
  have hn : ‖z.2‖ = r := by
    change ‖r • (v : c.PositiveCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp v.property,
      mul_one]
  have hstay (s : ℝ) (hs : 0 ≤ s) :
    MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      change Real.exp s * ‖(0 : c.NegativeCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, MulZeroClass.mul_zero]
      positivity
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)) hr.le
      nlinarith
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow :=
    c.flow_eqOn_descentModel hV F hF (x := c.splitChart.symm z) (c.splitChart.map_target' hz)
      isPreconnected_Ici (le_refl (0 : ℝ)) (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
      (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.beltCoreMap_coe] using hh

/-- A negative core ray parameter exists. -/
theorem MorseCancellation.exists_negative_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : PuncturedHandle.UnitSphere A) (t : ℝ), t < 0 ∧ Real.exp t • (r • (u : A)) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : PuncturedHandle.UnitSphere A :=
    ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩
  have hratio : 0 < ‖z‖ / r := div_pos hn hr
  have hratio1 : ‖z‖ / r < 1 := (div_lt_one hr).mpr hzr
  have hcoef : Real.exp (Real.log (‖z‖ / r)) * r * ‖z‖⁻¹ = 1 := by
    rw [Real.exp_log hratio]
    field_simp
  refine ⟨u, Real.log (‖z‖ / r), Real.log_neg hratio hratio1, ?_⟩
  change Real.exp (Real.log (‖z‖ / r)) • (r • (‖z‖⁻¹ • z)) = z
  rw [smul_smul, smul_smul, hcoef, one_smul]

/-- A positive core ray parameter exists. -/
theorem MorseCancellation.exists_positive_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : PuncturedHandle.UnitSphere A) (t : ℝ),
      0 < t ∧ Real.exp (-t) • (r • (u : A)) = z := by
  obtain ⟨u, t, ht, heq⟩ := exists_negative_core_ray_parameter hr hz hzr
  exact ⟨u, -t, neg_pos.mpr ht, by simpa only [neg_neg] using heq⟩
