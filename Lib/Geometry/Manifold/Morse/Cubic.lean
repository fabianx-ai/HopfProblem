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
# The cubic model of a cancelling pair

The chart-level cubic birth–death model behind Morse cancellation (Milnor,
*Lectures on the h-cobordism theorem*, Thm 4.1): adapted surgery windows and
basin blocks, the cubic model function, its endpoint charts, the cubic descent
field, split coordinates and field alignment, aligned rays, the cubic axis
parameter and the cubic model orbit, together with the local function
replacement on a compact support.

This module and `Morse.CubicFlow` hold the material of the former
`Morse/Cancellation.lean` that the rearrangement modules import; the
declarations are placed per subject subject to the import order
`Cubic → CubicFlow → Rearrangement → Connection → Cancellation`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Thm 4.1.
* [milnor63] J. Milnor, *Morse Theory*, §3.

## Tags

morse-theory, cancellation, cubic-model, h-cobordism
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

/-! ### Adapted surgery windows and basin blocks -/

attribute [local instance 100] Classical.propDecidable in
/-- Adapted surgery windows exist around a critical point. -/
theorem MorseCancellation.nonempty_adaptedSurgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) :
    Nonempty (AdaptedWindows E f) := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  let : Finite (ManifoldMorse.criticalPoints E f) := hfinite.to_subtype
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex :
    ∀ p : ManifoldMorse.criticalPoints E f,
      ∃ d : ManifoldMorse.MorseSurgeryData E f p.val,
        d.radius < r p / 3 ∧
          ∀ x ∈ ManifoldMorse.criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      ManifoldMorse.exists_morseSurgeryData_lt hf hm p.property
        (fun x hx hfx => hinj hx p.property hfx) (div_pos (hr p) (by norm_num))
  choose d hd hisolated using hex
  have hsq (p : ManifoldMorse.criticalPoints E f) : 9 * (d p).radius ^ 2 < (r p) ^ 2 := by
    have hsmall : 3 * (d p).radius < r p := by linarith [hd p]
    have hsum : 0 < r p + 3 * (d p).radius :=
      add_pos (hr p) (mul_pos (by norm_num) (d p).radius_pos)
    nlinarith [mul_pos (sub_pos.mpr hsmall) hsum]
  have hwide (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + 9 * (d p).radius ^ 2 < f q - 9 * (d q).radius ^ 2 := by
    linarith [hgap p q hpq, hsq p, hsq q]
  have hintervals :
    Pairwise
      (fun p q : ManifoldMorse.criticalPoints E f =>
        Disjoint (Set.Icc (f p - 9 * (d p).radius ^ 2) (f p + 9 * (d p).radius ^ 2))
          (Set.Icc (f q - 9 * (d q).radius ^ 2) (f q + 9 * (d q).radius ^ 2))) := by
    intro p q hpq
    have hne : f p ≠ f q := fun h => hpq (Subtype.ext (hinj p.property q.property h))
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [hwide p q hlt, hx.2, hy.1]
    · linarith [hwide q p hgt, hy.2, hx.1]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmodel⟩ :=
    exists_disjoint_surgery_block_field hf hm
      (fun p : ManifoldMorse.criticalPoints E f => p.val) (fun p => p.property)
      (fun p => (d p).chart) (fun p => (d p).radius) (fun p => (d p).radius_pos)
      (fun p => (d p).block) hintervals
  refine
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hmodel }⟩
  intro p q hpq
  nlinarith [hwide p q hpq, sq_nonneg (d p).radius, sq_nonneg (d q).radius]

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

/-! ### Strict descent and level basins -/

/-- A locally strict descent flow exists. -/
theorem FlowCancellation.exists_local_strict_flow_descent {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {x : X} (hx : D x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ StrictAntiOn (fun t : ℝ => f (F t x)) (Set.Icc (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => D (F t x)) :=
    hD.comp (F.continuous continuous_id continuous_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0, D (F t x) < 0 := by
    have hx0 : D (F 0 x) < 0 := by simpa only [F.map_zero_apply] using hx
    exact hcont.continuousAt (eventually_lt_nhds hx0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hfc : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hfc.continuousOn
  intro t ht
  rw [(hder x t).deriv]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_lt]
  have ht' := interior_subset ht
  constructor <;> linarith [ht'.1, ht'.2]

/-- The flow strictly enters a sublevel locally. -/
theorem FlowCancellation.exists_local_strict_sublevel_entry {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioc (0 : ℝ) ε, f (F t x) < c := by
  rcases hx.lt_or_eq with hx | hx
  · have he : ∀ᶠ t : ℝ in 𝓝 0, f (F t x) < c := by
      have hfc : Continuous (fun t : ℝ => f (F t x)) :=
        hf.comp (F.continuous continuous_id continuous_const)
      have hx0 : f (F 0 x) < c := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (eventually_lt_nhds hx0)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro t ht
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  · obtain ⟨ε, hε, hanti⟩ := exists_local_strict_flow_descent F hf hD hder (hboundary x hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have hh :=
      hanti (show (0 : ℝ) ∈ Set.Icc (-ε) ε from ⟨by linarith, hε.le⟩)
        (show t ∈ Set.Icc (-ε) ε from ⟨by linarith [ht.1], ht.2⟩) ht.1
    simpa only [F.map_zero_apply, hx] using hh

/-- A sublevel with forward-invariant boundary is forward invariant. -/
theorem FlowCancellation.forwardInvariant_sublevel_of_boundary {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ c := by
  apply FlowConstruction.forwardInvariant_of_local F (isClosed_le hf continuous_const)
  intro x hx
  obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | htpos
  · simpa only [← ht0, F.map_zero_apply] using hx
  · exact (hentry t ⟨htpos, ht.2⟩).le

/-- The sublevel interior is determined by the boundary. -/
theorem FlowCancellation.interior_sublevel_eq_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : interior {x | f x ≤ c} = {x | f x < c} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hle : f x ≤ c := (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) hx
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ c} := by
      have hfc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
      have hx0 : F 0 x ∈ interior {y | f y ≤ c} := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (isOpen_interior.mem_nhds hx0)
    have hmax : IsLocalMax (fun t : ℝ => f (F t x)) 0 := by
      filter_upwards [hnhds] with t ht
      change f (F t x) ≤ f (F 0 x)
      rw [F.map_zero_apply, heq]
      exact (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) ht
    have hz := hmax.hasDerivAt_eq_zero (hder x 0)
    rw [F.map_zero_apply] at hz
    exact (hboundary x heq).ne hz
  · exact interior_maximal (fun _ (hx : f _ < c) => hx.le) (isOpen_lt hf continuous_const)

/-- The flow strictly enters the sublevel across the boundary. -/
theorem FlowCancellation.strict_sublevel_entry_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 < t → f (F t x) < c := by
  have hforward := forwardInvariant_sublevel_of_boundary F hf hD hder hboundary
  have hlocal :
    ∀ x ∈ {y | f y ≤ c}, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior {y | f y ≤ c} := by
    intro x hx
    obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rw [interior_sublevel_eq_of_boundary F hf hder hboundary]
    exact hentry t ht
  intro x hx t ht
  have hi := FlowConstruction.interior_entry_of_local F hforward hlocal x hx t ht
  have hi' : F t x ∈ interior {y | f y ≤ c} := hi
  exact
    Eq.mp
      (congrArg (fun S : Set X => F t x ∈ S)
        (interior_sublevel_eq_of_boundary F hf hder hboundary))
      hi'

/-! ### The signed level time -/

/-- The level hitting time is unique. -/
theorem FlowCancellation.flow_level_time_unique {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) (x : X) {s t : ℝ} (hs : f (F s x) = c)
    (ht : f (F t x) = c) : s = t := by
  have hnot {a b : ℝ} (ha : f (F a x) = c) (hb : f (F b x) = c) : ¬a < b := by
    intro hab
    have hh :=
      strict_sublevel_entry_of_boundary F hf hD hder hboundary (F a x) ha.le (b - a)
        (sub_pos.mpr hab)
    rw [← F.map_add, sub_add_cancel, hb] at hh
    exact lt_irrefl _ hh
  exact le_antisymm (le_of_not_gt (hnot ht hs)) (le_of_not_gt (hnot hs ht))

/-! ### Height-translating flows -/

/-- The directional derivative of a smooth function is smooth. -/
theorem MorseCancellation.contMDiff_directionalDerivative {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

/-- Two points on the same orbit at the same level are equal. -/
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

/-! ### The cubic birth–death model -/

/-- The cubic birth–death model `x³ + tx` with transverse directions. -/
abbrev MorseCancellation.Model (m : ℕ) :=
  ℝ × (Fin m → ℝ)

/-- The cubic family `x³ + tx` in one variable. -/
def MorseCancellation.cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  p.1 ^ 3 / 3 + t * p.1 + ∑ i, σ i * (p.2 i) ^ 2

/-- The differential of the model. -/
def MorseCancellation.differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m →L[ℝ] ℝ :=
  (p.1 ^ 2 + t) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
    ∑ i,
      (2 * σ i * p.2 i) •
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))

/-- The differential computes the partial derivatives. -/
theorem MorseCancellation.differential_apply {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p v : Model m) :
    differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i := by
  simp [differential]

/-- The cubic family is smooth. -/
theorem MorseCancellation.contDiff_cubic_family {m : ℕ} (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Model m => cubic σ p.1 p.2) := by
  unfold cubic
  fun_prop

/-- The cubic is smooth. -/
theorem MorseCancellation.contDiff_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) : ContDiff ℝ ∞ (cubic σ t) :=
  (contDiff_cubic_family σ).comp (contDiff_const.prodMk contDiff_id)

/-- The cubic is differentiable. -/
theorem MorseCancellation.hasFDerivAt_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (cubic σ t) (differential σ t p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! (((hx.pow 3).mul_const (1 / 3)).add (hx.const_mul t)).add hq using 1
  · funext q
    simp [cubic, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    intro v
    simp [differential]
    ring_nf

/-- The derivative of the cubic. -/
theorem MorseCancellation.fderiv_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = differential σ t p :=
  (hasFDerivAt_cubic σ t p).fderiv

/-- The critical points of the cubic satisfy `3x² + t = 0`. -/
theorem MorseCancellation.critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (t : ℝ)
    (p : Model m) : fderiv ℝ (cubic σ t) p = 0 ↔ p.1 ^ 2 + t = 0 ∧ p.2 = 0 := by
  rw [fderiv_cubic]
  constructor
  · intro h
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) h
    have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
    refine ⟨hx', ?_⟩
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) h
    have hy' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  · rintro ⟨hx, hy⟩
    apply ContinuousLinearMap.ext
    intro v
    simp [differential_apply, hx, hy]

/-- At parameter zero the only critical point is the origin. -/
theorem MorseCancellation.cubic_zero_unique_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : fderiv ℝ (cubic σ 0) p = 0 ↔ p = 0 := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : p.1 = 0 := by nlinarith [sq_nonneg p.1]
    exact Prod.ext hx' hy
  · rintro rfl
    simp

/-- For positive parameter the cubic has no critical points. -/
theorem MorseCancellation.positive_parameter_no_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {t : ℝ} (ht : 0 < t) (p : Model m) : fderiv ℝ (cubic σ t) p ≠ 0 := by
  intro h
  have hx := ((critical_iff σ hσ t p).mp h).1
  nlinarith [sq_nonneg p.1]

/-- For negative parameter the critical points are `±√(−t/3)`. -/
theorem MorseCancellation.negative_parameter_critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (a : ℝ) (p : Model m) : fderiv ℝ (cubic σ (-(a ^ 2))) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hs : p.1 = a ∨ p.1 = -a := by
      have he : (p.1 - a) * (p.1 + a) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact hs.elim (fun h => Or.inl (Prod.ext h hy)) (fun h => Or.inr (Prod.ext h hy))
  · rintro (rfl | rfl) <;> simp

/-- The critical values of the cubic at negative parameter. -/
theorem MorseCancellation.cubic_critical_values {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    cubic σ (-(a ^ 2)) (a, 0) = -(2 * a ^ 3 / 3) ∧ cubic σ (-(a ^ 2)) (-a, 0) = 2 * a ^ 3 / 3 := by
  constructor <;> simp [cubic] <;> ring

/-! ### Endpoint charts -/

/-- The endpoint coordinate of a cubic chart. -/
def MorseCancellation.endpointCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) * Real.sqrt (a + e * (s - e * a) / 3)

/-- The domain of the endpoint coordinate. -/
def MorseCancellation.endpointDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * (s - e * a) / 3}

/-- The endpoint domain is open. -/
theorem MorseCancellation.endpointDomain_open (a e : ℝ) : IsOpen (endpointDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

/-- The endpoint lies in the domain. -/
theorem MorseCancellation.endpoint_mem_domain {a : ℝ} (ha : 0 < a) (e : ℝ) :
    e * a ∈ endpointDomain a e := by simpa [endpointDomain] using ha

/-- The endpoint coordinate at the center. -/
theorem MorseCancellation.endpointCoordinate_center (a e : ℝ) : endpointCoordinate a e (e * a) = 0 := by
  simp [endpointCoordinate]

/-- The endpoint coordinate is smooth. -/
theorem MorseCancellation.contDiffOn_endpointCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointCoordinate a e) (endpointDomain a e) := by
  intro s hs
  have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => t - e * a) s := contDiffAt_id.sub contDiffAt_const
  exact
    (hlin.mul
        ((contDiffAt_const.add ((contDiffAt_const.mul hlin).div_const 3)).sqrt
          (ne_of_gt hs))).contDiffWithinAt

/-- The endpoint coordinate is differentiable. -/
theorem MorseCancellation.hasDerivAt_endpointCoordinate {a : ℝ} (ha : 0 < a) (e : ℝ) :
    HasDerivAt (endpointCoordinate a e) (Real.sqrt a) (e * a) := by
  have hd :=
    ((hasDerivAt_id (e * a)).sub_const (e * a)).mul
      ((((hasDerivAt_id (e * a)).sub_const (e * a)).const_mul e).div_const 3 |>.const_add
          a |>.sqrt
        (by simpa using ha.ne'))
  convert! hd using 1; simp []

/-- The cubic on the endpoint square. -/
theorem MorseCancellation.cubic_endpoint_square {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (he : e ^ 2 = 1)
    {p : Model m} (hp : p.1 ∈ endpointDomain a e) :
    cubic σ (-(a ^ 2)) p =
      cubic σ (-(a ^ 2)) (e * a, 0) + e * endpointCoordinate a e p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 :=
  by
  simp only [cubic, endpointCoordinate, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- An endpoint scalar chart exists. -/
theorem MorseCancellation.exists_endpoint_scalar_chart {a : ℝ} (ha : 0 < a) (e : ℝ) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ Φ.source ∧
        Φ.source ⊆ endpointDomain a e ∧ (Φ : ℝ → ℝ) = endpointCoordinate a e ∧ Φ (e * a) = 0 := by
  have hd := (hasDerivAt_endpointCoordinate ha e).hasFDerivAt
  have hi : Function.Injective (fderiv ℝ (endpointCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * Real.sqrt a = y * Real.sqrt a at hxy
    exact mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne' hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨Φ, hp, hsub, hΦ⟩ :=
    exists_partialDiffeomorph_of_contDiffOn (endpointDomain_open a e)
      (endpoint_mem_domain ha e) (contDiffOn_endpointCoordinate a e) ⟨A, rfl⟩
  exact ⟨Φ, hp, hsub, hΦ, by rw [hΦ, endpointCoordinate_center]⟩

/-- The scalar product chart at an endpoint. -/
def MorseCancellation.scalarProductChart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)).toPartialEquiv
  open_source := Φ.open_source.prod isOpen_univ
  open_target := Φ.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ p.1, p.2)) (Φ.source ×ˢ Set.univ) :=
      (Φ.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn
  contMDiffOn_invFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ.symm p.1, p.2)) (Φ.target ×ˢ Set.univ) :=
      (Φ.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn

/-- An endpoint product chart exists. -/
theorem MorseCancellation.exists_endpoint_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (e : ℝ) (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (∀ p, (P p).2 = p.2) ∧
            (∀ p ∈ P.source,
              cubic σ (-(a ^ 2)) p =
                cubic σ (-(a ^ 2)) (e * a, 0) + e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2 i ^ 2) := by
  obtain ⟨Φ, hp, hsource, hΦ, hcenter⟩ := exists_endpoint_scalar_chart ha e
  let P := scalarProductChart (V := Fin m → ℝ) Φ
  have hP (p : Model m) : P p = (endpointCoordinate a e p.1, p.2) :=
    Prod.ext (congrFun hΦ p.1) rfl
  refine ⟨P, ⟨hp, Set.mem_univ _⟩, ?_, fun _ => rfl, ?_⟩
  · rw [hP, endpointCoordinate_center]
    rfl
  · intro p hp
    rw [hP]
    exact cubic_endpoint_square σ a e he (hsource hp.1)

/-! ### Local function replacement -/

/-- A function replaced by a model on a chart. -/
def LocalFunctionReplacement.replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) (y : M) : ℝ := by
  classical exact if y ∈ Φ.target then b (Φ.symm y) else f y

/-- The replacement computes the model inside the chart. -/
theorem LocalFunctionReplacement.replace_of_mem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b y = b (Φ.symm y) := by simp [replace, hy]

/-- The replacement is the original off the chart. -/
theorem LocalFunctionReplacement.replace_of_notMem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∉ Φ.target) :
    replace Φ f b y = f y := by simp [replace, hy]

/-- The replacement computes in the chart. -/
theorem LocalFunctionReplacement.replace_chart {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {x : E} (hx : x ∈ Φ.source) :
    replace Φ f b (Φ x) = b x := by
  rw [replace_of_mem Φ f b (Φ.map_source' hx)]
  exact congrArg b (Φ.left_inv' hx)

/-- The replacement's germ inside the chart. -/
theorem LocalFunctionReplacement.replace_germ_chart {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b =ᶠ[𝓝 y] b ∘ Φ.symm := by
  filter_upwards [Φ.open_target.mem_nhds hy] with z hz
  exact replace_of_mem Φ f b hz

/-- Replacing by the original is the identity. -/
theorem LocalFunctionReplacement.replace_self {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b : E → ℝ}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b x) : replace Φ f b = f := by
  funext y
  by_cases hy : y ∈ Φ.target
  · rw [replace_of_mem Φ f b hy]
    exact (hmodel (Φ.symm y) (Φ.map_target' hy)).symm.trans (congrArg f (Φ.right_inv' hy))
  · exact replace_of_notMem Φ f b hy

/-- The replacement agrees with the original off the support. -/
theorem LocalFunctionReplacement.replace_eq_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M}
    (hy : y ∉ Φ '' K) : replace Φ f b₁ y = f y := by
  by_cases hyt : y ∈ Φ.target
  · have hx : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [replace_of_mem Φ f b₁ hyt, hfix _ hx]
    exact (hmodel (Φ.symm y) (Φ.map_target' hyt)).symm.trans (congrArg f (Φ.right_inv' hyt))
  · exact replace_of_notMem Φ f b₁ hyt

/-- The replacement's germ off the support is the original's. -/
theorem LocalFunctionReplacement.replace_germ_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) : replace Φ f b₁ =ᶠ[𝓝 y] f := by
  have hc : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
  exact replace_eq_off_support Φ hmodel hfix hz

/-- The replacement is smooth. -/
theorem LocalFunctionReplacement.contMDiff_replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : ContDiff ℝ ∞ b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (replace Φ f b₁) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hs :=
      hb.contMDiff.contMDiffAt.comp y
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy))
    exact hs.congr_of_eventuallyEq (replace_germ_chart Φ f b₁ hy)
  · have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    exact
      hf.contMDiffAt.congr_of_eventuallyEq (replace_germ_off_support Φ hK hKΦ hmodel hfix hnot)

/-- The critical points of the replacement on the chart. -/
theorem LocalFunctionReplacement.replace_critical_iff {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) {y : M}
    (hy : y ∈ Φ.target) : mfderiv I 𝓘(ℝ, ℝ) (replace Φ f b) y = 0 ↔ fderiv ℝ b (Φ.symm y) = 0 := by
  have hΦ : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ Φ.symm y := ⟨Φ.symm, hy, fun _ _ => rfl⟩
  have hsurj := (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [(replace_germ_chart Φ f b hy).mfderiv_eq,
    mfderiv_comp y (hb.contMDiff.mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hy),
    mfderiv_eq_fderiv]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    have he := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L w) h
    change fderiv ℝ b (Φ.symm y) (mfderiv I 𝓘(ℝ, E) Φ.symm y w) = 0 at he
    change mfderiv I 𝓘(ℝ, E) Φ.symm y w = v at hw
    simpa only [hw, zero_apply] using he
  · intro h
    rw [h]
    rfl

/-! ### The cubic descent field -/

/-- The cubic descent field. -/
def MorseCancellation.cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m :=
  (-(p.1 ^ 2 + t), fun i => -σ i * p.2 i)

/-- The differential of the cubic descent. -/
theorem MorseCancellation.differential_cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    differential σ t p (cubicDescent σ t p) = -(p.1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * p.2 i) ^ 2 := by
  rw [differential_apply]
  simp only [cubicDescent]
  have hs : (∑ i, 2 * σ i * p.2 i * (-σ i * p.2 i)) = -2 * ∑ i, (σ i * p.2 i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The cubic descent is strict off the critical point. -/
theorem MorseCancellation.cubicDescent_strict {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p ≠ 0) : fderiv ℝ (cubic σ t) p (cubicDescent σ t p) < 0 := by
  rw [fderiv_cubic, differential_cubicDescent]
  by_contra hh
  have hsum : 0 ≤ ∑ i, (σ i * p.2 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : p.1 ^ 2 + t = 0 := by nlinarith [sq_nonneg (p.1 ^ 2 + t)]
  have hz : (∑ i, (σ i * p.2 i) ^ 2) = 0 := by
    have hle := le_of_not_gt hh
    rw [hx] at hle
    linarith
  have hy (i : Fin m) : σ i * p.2 i = 0 := by
    have hi :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp hz i
        (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  apply hp
  rw [fderiv_cubic]
  apply ContinuousLinearMap.ext
  intro v
  rw [differential_apply, hx]
  simp only [MulZeroClass.zero_mul, zero_add, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  calc
    2 * σ i * p.2 i * v.2 i = 2 * (σ i * p.2 i) * v.2 i := by ring
    _ = 0 := by rw [hy, MulZeroClass.mul_zero, MulZeroClass.zero_mul]

/-- The cubic descent vanishes at the critical point. -/
theorem MorseCancellation.cubicDescent_zero_of_critical {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p = 0) : cubicDescent σ t p = 0 := by
  rw [fderiv_cubic] at hp
  have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hp
  have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
  apply Prod.ext
  · simpa only [cubicDescent, Prod.fst_zero, neg_eq_zero] using hx'
  · funext i
    have hi := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hp
    have hi' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hi
    change -σ i * p.2 i = 0
    nlinarith

/-- The native cubic descent field. -/
def MorseCancellation.nativeCubicDescent {m : ℕ} (σ : Fin m → ℝ) {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    (x : M) → TangentSpace 𝓘(ℝ, B) x :=
  FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)

/-- The field coordinate at a cubic endpoint. -/
def MorseCancellation.endpointFieldCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) / (a + e * s)

/-- The domain of the endpoint field coordinate. -/
def MorseCancellation.endpointFieldDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * s}

/-- The endpoint field domain is open. -/
theorem MorseCancellation.endpointFieldDomain_open (a e : ℝ) : IsOpen (endpointFieldDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

/-- The endpoint lies in the field domain. -/
theorem MorseCancellation.endpointField_mem_domain {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    e * a ∈ endpointFieldDomain a e := by
  change 0 < a + e * (e * a)
  have h : e * (e * a) = a := by rw [← mul_assoc, ← pow_two, he, one_mul]
  rw [h]
  linarith

/-- The endpoint field coordinate at the center. -/
theorem MorseCancellation.endpointFieldCoordinate_center (a e : ℝ) :
    endpointFieldCoordinate a e (e * a) = 0 := by simp [endpointFieldCoordinate]

/-- The endpoint field coordinate is smooth. -/
theorem MorseCancellation.contDiffOn_endpointFieldCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointFieldCoordinate a e) (endpointFieldDomain a e) := by
  intro s hs
  exact
    ((contDiffAt_id.sub contDiffAt_const).div
        (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (ne_of_gt hs)).contDiffWithinAt

/-- The endpoint field coordinate is differentiable. -/
theorem MorseCancellation.hasDerivAt_endpointFieldCoordinate (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    HasDerivAt (endpointFieldCoordinate a e) (2 * a / (a + e * s) ^ 2) s := by
  have hd :=
    ((hasDerivAt_id s).sub_const (e * a)).div (((hasDerivAt_id s).const_mul e).const_add a)
      (ne_of_gt hs)
  convert! hd using 1
  congr 1
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- The endpoint field coordinate computes the pushforward. -/
theorem MorseCancellation.endpointFieldCoordinate_pushforward (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    deriv (endpointFieldCoordinate a e) s * (a ^ 2 - s ^ 2) =
      (-2 * e * a) * endpointFieldCoordinate a e s := by
  rw [(hasDerivAt_endpointFieldCoordinate a he hs).deriv]
  unfold endpointFieldCoordinate
  have hn : a + e * s ≠ 0 := ne_of_gt hs
  field_simp
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- An endpoint field scalar chart exists. -/
theorem MorseCancellation.exists_endpoint_field_scalar_chart {a : ℝ} (ha : 0 < a) {e : ℝ}
    (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ P.source ∧
        P.source ⊆ endpointFieldDomain a e ∧
          (P : ℝ → ℝ) = endpointFieldCoordinate a e ∧ P (e * a) = 0 := by
  have hm := endpointField_mem_domain ha he
  have hd := (hasDerivAt_endpointFieldCoordinate a he hm).hasFDerivAt
  have hn : 2 * a / (a + e * (e * a)) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ (ne_of_gt hm))
  have hi : Function.Injective (fderiv ℝ (endpointFieldCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * (2 * a / (a + e * (e * a)) ^ 2) = y * (2 * a / (a + e * (e * a)) ^ 2) at hxy
    exact mul_right_cancel₀ hn hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointFieldCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨P, hp, hsub, hP⟩ :=
    exists_partialDiffeomorph_of_contDiffOn (endpointFieldDomain_open a e) hm
      (contDiffOn_endpointFieldCoordinate a e) ⟨A, rfl⟩
  exact ⟨P, hp, hsub, hP, by rw [hP, endpointFieldCoordinate_center]⟩

/-- The linear field at a cubic endpoint. -/
def MorseCancellation.endpointLinearField {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (p : Model m) : Model m :=
  ((-2 * e * a) * p.1, fun i => -σ i * p.2 i)

/-- The product field at a cubic endpoint. -/
def MorseCancellation.endpointFieldProduct {m : ℕ} (a e : ℝ) (p : Model m) : Model m :=
  (endpointFieldCoordinate a e p.1, p.2)

/-- The endpoint product field's derivative on the cubic. -/
theorem MorseCancellation.fderiv_endpointFieldProduct_cubic {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {e : ℝ}
    (he : e ^ 2 = 1) {p : Model m} (hp : p.1 ∈ endpointFieldDomain a e) :
    fderiv ℝ (endpointFieldProduct a e) p (cubicDescent σ (-(a ^ 2)) p) =
      endpointLinearField σ a e (endpointFieldProduct a e p) := by
  have hd :=
    ((hasDerivAt_endpointFieldCoordinate a he hp).comp_hasFDerivAt p
          (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (endpointFieldProduct a e) _ p at hd
  rw [hd.fderiv]
  apply Prod.ext
  · change
      (2 * a / (a + e * p.1) ^ 2) * (-(p.1 ^ 2 + -(a ^ 2))) =
        (-2 * e * a) * endpointFieldCoordinate a e p.1
    have hh := endpointFieldCoordinate_pushforward a he hp
    rw [(hasDerivAt_endpointFieldCoordinate a he hp).deriv] at hh
    convert! hh using 1; ring
  · rfl

/-- An endpoint field product chart exists. -/
theorem MorseCancellation.exists_endpoint_field_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (P : Model m → Model m) = endpointFieldProduct a e ∧
            ∀ p ∈ P.source,
              fderiv ℝ P p (cubicDescent σ (-(a ^ 2)) p) = endpointLinearField σ a e (P p) := by
  obtain ⟨Q, hq, hsub, hQ, hzero⟩ := exists_endpoint_field_scalar_chart ha he
  let P := scalarProductChart (V := Fin m → ℝ) Q
  have hP : (P : Model m → Model m) = endpointFieldProduct a e := by
    funext p
    exact Prod.ext (congrFun hQ p.1) rfl
  refine ⟨P, ⟨hq, Set.mem_univ _⟩, ?_, hP, ?_⟩
  · rw [hP]
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  · intro p hp
    rw [hP]
    exact fderiv_endpointFieldProduct_cubic σ a he (hsub hp.1)

/-- A model-conjugate partial chart field. -/
theorem MorseCancellation.partialChartField_of_model_conjugacy {D F E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, F) D F ∞) (Q : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (W : D → D) (U : F → F) (hpush : ∀ p ∈ P.source, fderiv ℝ P p (W p) = U (P p)) {x : M}
    (hx : x ∈ (P.trans Q).target) :
    FlowConstruction.partialChartField (P.trans Q).symm W x =
      FlowConstruction.partialChartField Q.symm U x := by
  have hxQ : x ∈ Q.target := hx.1
  have hxP : Q.symm x ∈ P.target := hx.2
  have hdiff : P.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, D) :=
    ⟨P.symm.mdifferentiableOn (by simp), P.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm Set.univ (Q.symm x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxP, rfl⟩
  have hh :=
    VectorField.mpullbackWithin_comp_of_left (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, D)) (f :=
      (Q.symm : M → F)) (g := (P.symm : F → D)) (V := fun y =>
      (NormedSpace.fromTangentSpace y).symm (W y)) (s := Set.univ) (t := Set.univ)
      (Q.symm.mdifferentiableAt (by simp) hxQ).mdifferentiableWithinAt (Set.mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  have hv :
    VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) (Q.symm x) =
      (NormedSpace.fromTangentSpace (Q.symm x)).symm (U (Q.symm x)) := by
    change FlowConstruction.partialChartField P.symm W (Q.symm x) = _
    rw [FlowConstruction.partialChartField_eq_mfderiv_symm P.symm W hxP]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ P (P.symm (Q.symm x)) (W (P.symm (Q.symm x))) = U (Q.symm x)
    have hp : P.symm (Q.symm x) ∈ P.source := P.map_target' hxP
    rw [hpush (P.symm (Q.symm x)) hp]
    exact congrArg U (P.right_inv' hxP)
  change
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, D) (P.symm ∘ Q.symm)
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x =
      _
  rw [hh, VectorField.mpullback_apply, hv]
  rfl

/-- A native cubic field endpoint chart exists. -/
theorem MorseCancellation.exists_native_cubic_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (h0 : (0 : Model m) ∈ Q.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ x ∈ Q.target,
        V x = FlowConstruction.partialChartField Q.symm (endpointLinearField σ a e) x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e * a, 0) = Q 0 ∧
          Φ.target ⊆ Q.target ∧
            (∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) ∧
              (Φ : Model m → M) = Q ∘ endpointFieldProduct a e := by
  obtain ⟨P, hp, hcenter, hP, hpush⟩ := exists_endpoint_field_product_chart σ ha he
  let Φ := P.trans Q
  have hsource : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    change (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) ∈ Q.source
    exact ⟨hp, hcenter.symm ▸ h0⟩
  refine ⟨Φ, hsource, ?_, fun _ hx => hx.1, ?_, ?_⟩
  · change Q (P (e * a, 0)) = Q 0
    rw [hcenter]
  · intro x hx
    rw [hmodel x hx.1]
    exact
      (partialChartField_of_model_conjugacy P Q (cubicDescent σ (-(a ^ 2)))
          (endpointLinearField σ a e) hpush hx).symm
  · change Q ∘ P = Q ∘ endpointFieldProduct a e
    rw [hP]

/-! ### Split coordinates and field alignment -/

/-- The linear splitting into the axis and transverse directions. -/
def MorseCancellation.splitLinear {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃ₗ[ℝ] (Fin n → ℝ)
    where
  toFun p j := (ρ.symm j).elim p.1 p.2
  invFun f := (f (ρ Option.none), fun i => f (ρ (Option.some i)))
  left_inv
    p := by
    apply Prod.ext
    · simp
    · funext i
      simp
  right_inv
    f := by
    funext j
    have hj := ρ.apply_symm_apply j
    cases h : ρ.symm j with
    | none => simpa only [h, Option.elim_none] using congrArg f hj
    | some i => simpa only [h, Option.elim_some] using congrArg f hj
  map_add' p
    q := by
    funext j
    cases h : ρ.symm j <;> simp [h]
  map_smul' t
    p := by
    funext j
    cases h : ρ.symm j <;> simp [h]

/-- The split equivalence of the model space. -/
def MorseCancellation.splitEquiv {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃L[ℝ] (Fin n → ℝ) :=
  (splitLinear ρ).toContinuousLinearEquiv

/-- The split equivalence on the axis component. -/
theorem MorseCancellation.splitEquiv_apply_none {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m) :
    splitEquiv ρ p (ρ Option.none) = p.1 := by
  change (ρ.symm (ρ Option.none)).elim p.1 p.2 = p.1
  simp

/-- The split equivalence on the transverse component. -/
theorem MorseCancellation.splitEquiv_apply_some {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m)
    (i : Fin m) : splitEquiv ρ p (ρ (Option.some i)) = p.2 i := by
  change (ρ.symm (ρ (Option.some i))).elim p.1 p.2 = p.2 i
  simp

/-- The signed sum in split coordinates. -/
theorem MorseCancellation.split_signed_sum {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ)
    (p : Model m) :
    (∑ j, w j * splitEquiv ρ p j ^ 2) =
      w (ρ Option.none) * p.1 ^ 2 + ∑ i, w (ρ (Option.some i)) * p.2 i ^ 2 := by
  rw [← ρ.sum_comp]
  simp only [Fintype.sum_option, splitEquiv_apply_none, splitEquiv_apply_some]

/-- The endpoint field in split coordinates. -/
theorem MorseCancellation.splitEquiv_endpoint_field {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) (p : Model m) :
    splitEquiv ρ
        (endpointLinearField (fun i => w (ρ (Option.some i))) (1 / 2) (w (ρ Option.none)) p) =
      fun j => -w j * splitEquiv ρ p j := by
  funext j
  obtain ⟨k, rfl⟩ := ρ.surjective j
  cases k with
  | none =>
    rw [splitEquiv_apply_none, splitEquiv_apply_none]
    change (-2 * w (ρ Option.none) * (1 / 2)) * p.1 = -w (ρ Option.none) * p.1
    ring
  | some i =>
    rw [splitEquiv_apply_some, splitEquiv_apply_some]
    rfl

attribute [local instance 100] Classical.propDecidable in
/-- The signed descent in split coordinates. -/
theorem MorseCancellation.splitCoordinates_signed_descent {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    MorseHandle.splitCoordinates w (fun i => -w i * z i) =
      MorseHandle.descent (MorseHandle.splitCoordinates w z) := by
  apply Prod.ext
  · ext i
    change -w i.1 * z i.1 = z i.1
    rw [i.2]
    ring
  · ext i
    change -w i.1 * z i.1 = -z i.1
    rw [(hw i.1).resolve_left i.2]
    ring

attribute [local instance 100] Classical.propDecidable in
/-- The linear equivalence aligning the selected Morse field. -/
def MorseCancellation.selectedMorseFieldEquiv {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates) :=
  (splitEquiv ρ).trans (MorseHandle.splitCoordinates c.weights)

attribute [local instance 100] Classical.propDecidable in
/-- The selected Morse field equivalence preserves descent. -/
theorem MorseCancellation.selectedMorseFieldEquiv_descent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (p : Model m) :
    selectedMorseFieldEquiv c ρ
        (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
          (c.weights (ρ Option.none)) p) =
      MorseHandle.descent (selectedMorseFieldEquiv c ρ p) := by
  change
    MorseHandle.splitCoordinates c.weights (splitEquiv ρ _) =
      MorseHandle.descent (MorseHandle.splitCoordinates c.weights (splitEquiv ρ p))
  rw [splitEquiv_endpoint_field]
  exact splitCoordinates_signed_descent c.weights c.signs (splitEquiv ρ p)

/-- The transverse change of field. -/
def MorseCancellation.transverseFieldChange {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    Model m ≃L[ℝ] Model m :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr T

/-- The transverse change preserves cubic descent. -/
theorem MorseCancellation.transverseFieldChange_cubicDescent {m : ℕ} (σ : Fin m → ℝ)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i) (t : ℝ) (p : Model m) :
    transverseFieldChange T (cubicDescent σ t p) = cubicDescent σ t (transverseFieldChange T p) :=
  by
  apply Prod.ext
  · rfl
  · change T (fun i => -σ i * p.2 i) = fun i => -σ i * T p.2 i
    have hleft : (fun i => -σ i * p.2 i) = -(fun i => σ i * p.2 i) := by
      funext i
      simp only [Pi.neg_apply, neg_mul]
    rw [hleft, map_neg, hcomm]
    funext i
    simp only [Pi.neg_apply, neg_mul]

/-- The transverse change in split coordinates. -/
def MorseCancellation.splitTransverseChange {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (e : (Fin m → ℝ) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (e.trans (P.prodCongr S)).trans e.symm

/-- The split transverse change commutes with the splitting. -/
theorem MorseCancellation.splitTransverseChange_commutes {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (σ : Fin m → ℝ)
    (e : (Fin m → ℝ) ≃L[ℝ] (A × B)) (α β : ℝ)
    (he : ∀ z, e (fun i => σ i * z i) = (α • (e z).1, β • (e z).2)) (P : A ≃L[ℝ] A)
    (S : B ≃L[ℝ] B) (z : Fin m → ℝ) :
    splitTransverseChange e P S (fun i => σ i * z i) = fun i =>
      σ i * splitTransverseChange e P S z i := by
  apply e.injective
  simp only [splitTransverseChange, ContinuousLinearEquiv.trans_apply, e.apply_symm_apply, he,
    ContinuousLinearEquiv.prodCongr_apply, map_smul]

/-- The Morse block change preserves descent. -/
theorem MorseCancellation.morse_block_change_descent {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P)
    (z : N × P) :
    (A.prodCongr B) (MorseHandle.descent z) =
      MorseHandle.descent ((A.prodCongr B) z) := by
  apply Prod.ext
  · rfl
  · change B (-z.2) = -B z.2
    exact B.map_neg _

/-- A positive ray alignment of the field exists. -/
theorem MorseCancellation.exists_positive_ray_alignment {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] {u v : D} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ (r : ℝ) (A : D ≃ₗᵢ[ℝ] D), 0 < r ∧ A (r • u) = v ∧ ∀ s : ℝ, A ((s * r) • u) = s • v := by
  let r := ‖v‖ / ‖u‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu)
  have hnorm : ‖r • u‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact div_mul_cancel₀ ‖v‖ (norm_ne_zero_iff.mpr hu)
  let A : D ≃ₗᵢ[ℝ] D := (ℝ ∙ (r • u - v))ᗮ.reflection
  have hA : A (r • u) = v := Submodule.reflection_sub hnorm
  refine ⟨r, A, hr, hA, ?_⟩
  intro s
  rw [← smul_smul, A.map_smul, hA]

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's axis component is nonzero. -/
theorem MorseCancellation.selectedMorseFieldEquiv_axis_ne_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ)) ≠ 0 := by
  intro h
  have hh :=
    (selectedMorseFieldEquiv c ρ).injective
      (h.trans (map_zero (selectedMorseFieldEquiv c ρ)).symm)
  have h1 := congrArg Prod.fst hh
  norm_num at h1

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's negative axis. -/
theorem MorseCancellation.selectedMorseFieldEquiv_negative_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      (1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw] at hh
  have h2 : z.2 = -z.2 := congrArg Prod.snd hh
  have hs : (2 : ℝ) • z.2 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.2) h2).trans (neg_add_cancel z.2)
  have hz : z.2 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h1
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext h1 hz)

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's positive axis. -/
theorem MorseCancellation.selectedMorseFieldEquiv_positive_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      -(1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw, map_neg] at hh
  have h1 : z.1 = -z.1 := (congrArg Prod.fst hh).symm
  have hs : (2 : ℝ) • z.1 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.1) h1).trans (neg_add_cancel z.1)
  have hz : z.1 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h2
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext hz h2)

attribute [local instance 100] Classical.propDecidable in
/-- A selected outgoing axis exists. -/
theorem MorseCancellation.exists_selected_outgoing_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {v : c.NegativeCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (r, 0) = (v, 0) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_negative_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn hv
  let B :=
    A.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ c.PositiveCoordinates)
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (r, (0 : Fin m → ℝ)) = r • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change r • A ((L₀ (1, 0)).1) = v
      rw [← A.map_smul]
      exact hA
    · change r • (L₀ (1, 0)).2 = 0
      rw [hz, smul_zero]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
/-- A selected incoming axis exists. -/
theorem MorseCancellation.exists_selected_incoming_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {v : c.PositiveCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (-r, 0) = (0, v) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_positive_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn (neg_ne_zero.mpr hv)
  let B :=
    (ContinuousLinearEquiv.refl ℝ c.NegativeCoordinates).prodCongr A.toContinuousLinearEquiv
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (-r, (0 : Fin m → ℝ)) = (-r) • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change (-r) • (L₀ (1, 0)).1 = 0
      rw [hz, smul_zero]
    · change (-r) • A ((L₀ (1, 0)).2) = v
      rw [neg_smul, ← A.map_smul, hA, neg_neg]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
/-- A cubic field endpoint with ray alignment exists. -/
theorem MorseCancellation.exists_cubic_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, c.descentField y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  let P := L.toDiffeomorph.toPartialDiffeomorph
  let Q := P.trans c.splitChart.symm
  have h0 : (0 : Model m) ∈ Q.source := by
    change (0 : Model m) ∈ Set.univ ∧ L 0 ∈ c.splitChart.target
    rw [map_zero, ← c.splitChart_center]
    exact ⟨Set.mem_univ _, c.splitChart.map_source' c.splitChart_mem_source⟩
  have hQzero : Q 0 = x := by
    change c.splitChart.symm (L 0) = x
    rw [map_zero, ← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hmodel :
    ∀ y ∈ Q.target,
      c.descentField y =
        FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
      fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)
      rw [L.fderiv]
      exact hL p
    exact
      (partialChartField_of_model_conjugacy P c.splitChart.symm (endpointLinearField σ (1 / 2) e)
          MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0 c.descentField
      hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf, hmap⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

attribute [local instance 100] Classical.propDecidable in
/-- An original field endpoint with ray alignment exists. -/
theorem MorseCancellation.exists_original_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ := exists_cubic_field_endpoint_with_alignment c σ he L hL
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictTarget Φ hU
  have hpΨ : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hp, hc.symm ▸ hxU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, hmap⟩
  intro y hy
  exact (hUsub hy.2).trans (hf y hy.1)

/-- The endpoint field coordinate on the open axis. -/
theorem MorseCancellation.endpointFieldCoordinate_mem_open_axis {a : ℝ} {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) (hdir : 0 < -e * endpointFieldCoordinate a e s) :
    s ∈ Set.Ioo (-a) a := by
  rcases sq_eq_one_iff.mp he with h | h
  · subst e
    have hd : 0 < a + s := by simpa [endpointFieldDomain] using hs
    have hy : (s - a) / (a + s) < 0 := by simpa [endpointFieldCoordinate] using hdir
    have hn : s - a < 0 := by simpa using (div_lt_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩
  · subst e
    have hd : 0 < a - s := by simpa [endpointFieldDomain] using hs
    have hy : 0 < (s + a) / (a - s) := by
      simpa [endpointFieldCoordinate, sub_eq_add_neg] using hdir
    have hn : 0 < s + a := by simpa using (lt_div_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩

attribute [local instance 100] Classical.propDecidable in
/-- A controlled Morse field endpoint exists. -/
theorem MorseCancellation.exists_controlled_morse_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ) {e : ℝ}
    (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              ∀ p ∈ Φ.source,
                p.1 ∈ endpointFieldDomain (1 / 2) e ∧
                  c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p) := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_original_field_endpoint_with_alignment c σ he L hL V heq
  let q : Model m := (e / 2, 0)
  have hq : q.1 ∈ endpointFieldDomain (1 / 2) e := by
    simpa only [q, mul_one_div] using endpointField_mem_domain (by norm_num : 0 < (1 / 2 : ℝ)) he
  have hd : ContinuousAt (endpointFieldCoordinate (1 / 2) e) q.1 :=
    ((contDiffOn_endpointFieldCoordinate (1 / 2) e).contDiffAt
        ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)).continuousAt
  have hprod : ContinuousAt (endpointFieldProduct (m := m) (1 / 2) e) q :=
    (hd.comp continuousAt_fst).prodMk continuousAt_snd
  have hzero : L (endpointFieldProduct (1 / 2) e q) = 0 := by
    have hq' : q = (e * (1 / 2), (0 : Fin m → ℝ)) := by
      apply Prod.ext
      · dsimp [q]
        ring
      · rfl
    rw [hq']
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  have hct : ContinuousAt (fun p : Model m => L (endpointFieldProduct (1 / 2) e p)) q :=
    L.continuous.continuousAt.comp hprod
  have htarget0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have htarget : ∀ᶠ p in 𝓝 q, L (endpointFieldProduct (1 / 2) e p) ∈ c.splitChart.target := by
    have hn : ∀ᶠ z in 𝓝 (L (endpointFieldProduct (1 / 2) e q)), z ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (hzero.symm ▸ htarget0)
    exact hct.eventually hn
  have hdomain : ∀ᶠ p in 𝓝 q, p.1 ∈ endpointFieldDomain (1 / 2) e :=
    continuousAt_fst.eventually ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)
  obtain ⟨U, hUsub, hU, hqU⟩ := mem_nhds_iff.mp (hdomain.and htarget)
  let Ψ := PartialChart.restrictSource Φ hU
  have hpΨ : q ∈ Ψ.source := ⟨hp, hqU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, ?_⟩
  · intro y hy
    exact hf y hy.1
  · intro p hp
    obtain ⟨hpd, hpt⟩ := hUsub hp.2
    refine ⟨hpd, ?_⟩
    change c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p)
    rw [hmap]
    exact c.splitChart.right_inv' hpt

/-! ### Aligned rays and cubic endpoints -/

/-- The descent flow of an outgoing aligned ray. -/
theorem MorseCancellation.descentFlow_outgoing_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : N} (hL : L (r, 0) = (v, 0)) (t : ℝ) :
    MorseHandle.descentFlow t (L (r, 0)) = L (r * Real.exp t, 0) := by
  have he : (r * Real.exp t, (0 : Fin m → ℝ)) = Real.exp t • (r, 0) := by
    apply Prod.ext
    · change r * Real.exp t = Real.exp t * r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • v, Real.exp (-t) • (0 : P)) = (Real.exp t • v, Real.exp t • (0 : P))
  simp

/-- The descent flow of an incoming aligned ray. -/
theorem MorseCancellation.descentFlow_incoming_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : P} (hL : L (-r, 0) = (0, v)) (t : ℝ) :
    MorseHandle.descentFlow t (L (-r, 0)) = L (-r * Real.exp (-t), 0) := by
  have he : (-r * Real.exp (-t), (0 : Fin m → ℝ)) = Real.exp (-t) • (-r, 0) := by
    apply Prod.ext
    · change -r * Real.exp (-t) = Real.exp (-t) * -r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • (0 : N), Real.exp (-t) • v) = (Real.exp (-t) • (0 : N), Real.exp (-t) • v)
  simp

/-- An aligned Morse ray lies on the cubic axis. -/
theorem MorseCancellation.cubic_axis_of_aligned_morse_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (C : M → N × P)
    (L : Model m ≃L[ℝ] (N × P)) {a : ℝ} {e : ℝ} (he : e ^ 2 = 1)
    (hcoord :
      ∀ p ∈ Φ.source, p.1 ∈ endpointFieldDomain a e ∧ C (Φ p) = L (endpointFieldProduct a e p))
    {x : M} (hx : x ∈ Φ.target) {r : ℝ} (hr : 0 < -e * r) (hCx : C x = L (r, 0)) :
    ∃ s ∈ Set.Ioo (-a) a,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = x ∧ endpointFieldCoordinate a e s = r := by
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  have hpx : Φ p = x := Φ.right_inv' hx
  obtain ⟨hdom, hCp⟩ := hcoord p hp
  rw [hpx, hCx] at hCp
  have hlin : endpointFieldProduct a e p = (r, 0) := L.injective hCp.symm
  have hscalar : endpointFieldCoordinate a e p.1 = r := congrArg Prod.fst hlin
  have hzero : p.2 = 0 := congrArg Prod.snd hlin
  have haxis : p = (p.1, 0) := Prod.ext rfl hzero
  have hdir : 0 < -e * endpointFieldCoordinate a e p.1 := hscalar.symm ▸ hr
  refine ⟨p.1, endpointFieldCoordinate_mem_open_axis he hdom hdir, ?_, ?_, hscalar⟩
  · exact haxis ▸ hp
  · exact (congrArg Φ haxis).symm.trans hpx

/-- The flow formula from local shifts. -/
theorem MorseCancellation.flow_formula_of_local_shifts {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (γ : ℝ → X) {S : Set ℝ} (hS : IsPreconnected S)
    (hlocal : ∀ t ∈ S, ∀ᶠ s in 𝓝 t, γ s = F (s - t) (γ t)) {t₀ t : ℝ} (h₀ : t₀ ∈ S) (ht : t ∈ S) :
    γ t = F (t - t₀) (γ t₀) := by
  let β : S → X := fun u => F (-u.1) (γ u.1)
  have hc : IsLocallyConstant β := by
    apply (IsLocallyConstant.iff_eventually_eq β).mpr
    intro u
    filter_upwards [continuousAt_subtype_val.eventually (hlocal u.1 u.2)] with v hv
    change F (-v.1) (γ v.1) = F (-u.1) (γ u.1)
    rw [hv, ← F.map_add]
    congr 1
    ring
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hb : β ⟨t, ht⟩ = β ⟨t₀, h₀⟩ :=
    hc.apply_eq_of_isPreconnected PreconnectedSpace.isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _)
  have hh := congrArg (F t) hb
  change F t (F (-t) (γ t)) = F t (F (-t₀) (γ t₀)) at hh
  simpa only [← F.map_add, add_neg_cancel, F.map_zero_apply, ← sub_eq_add_neg] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The flow eventually follows the Morse coordinate formula. -/
theorem MorseCancellation.eventually_morse_coordinate_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) (t : ℝ)
    (ht : F t x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) :
    ∀ᶠ s in 𝓝 t,
      c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  have hlocal :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      F u (F t x) = c.splitChart.symm (MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    c.eventually_flow_eq_descentModel hV F hF ht heq
  have htime : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t
  have hmodel :
    Continuous (fun u : ℝ => MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have htarget :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      MorseHandle.descentFlow u (c.splitChart (F t x)) ∈ c.splitChart.target := by
    have hnhds : ∀ᶠ y in 𝓝 (c.splitChart (F t x)), y ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (c.splitChart.map_source' ht)
    have hm0 :
      Filter.Tendsto (fun u : ℝ => MorseHandle.descentFlow u (c.splitChart (F t x))) (𝓝 0)
        (𝓝 (c.splitChart (F t x))) := by simpa only [Flow.map_zero_apply] using hmodel.tendsto 0
    exact hm0.eventually hnhds
  filter_upwards [htime.eventually hlocal, htime.eventually htarget] with s hs hst
  rw [← F.map_add, sub_add_cancel] at hs
  have hh := congrArg c.splitChart hs
  exact hh.trans (c.splitChart.right_inv' hst)

attribute [local instance 100] Classical.propDecidable in
/-- The Morse coordinates of an actual trajectory. -/
theorem MorseCancellation.morse_coordinates_of_actual_trajectory {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) {S : Set ℝ}
    (hS : IsPreconnected S) (htarget : ∀ t ∈ S, F t x ∈ c.splitChart.source)
    (heq : ∀ t ∈ S, ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) {t₀ t : ℝ} (h₀ : t₀ ∈ S)
    (ht : t ∈ S) :
    c.splitChart (F t x) = MorseHandle.descentFlow (t - t₀) (c.splitChart (F t₀ x)) :=
  flow_formula_of_local_shifts MorseHandle.descentFlow (fun s => c.splitChart (F s x)) hS
    (fun s hs => eventually_morse_coordinate_flow c hV F hF x s (htarget s hs) (heq s hs)) h₀ ht

attribute [local instance 100] Classical.propDecidable in
/-- Tail data of a Morse endpoint orbit. -/
theorem MorseCancellation.morse_endpoint_tail_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M) (x : M) {l : Filter ℝ}
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p)) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) ∧
      ∀ᶠ t in l, F t x ∈ c.splitChart.source ∧ ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hcoord : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) := by
    have hh : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 (c.splitChart p)) :=
      hc.tendsto.comp hlim
    simpa only [c.splitChart_center] using hh
  have hsource : ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ z in 𝓝 y, V z = c.descentField z :=
    eventually_eventually_nhds.mpr heq
  exact ⟨hcoord, hlim.eventually (hsource.and hgerm)⟩

attribute [local instance 100] Classical.propDecidable in
/-- An incoming Morse tail exists. -/
theorem MorseCancellation.exists_incoming_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≥ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≥ T, (c.splitChart (F t x)).1 = 0) ∧
          ∀ t ≥ T,
            ∀ s ≥ T,
              c.splitChart (F s x) =
                MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hformula (t : ℝ) (ht : T ≤ t) (s : ℝ) (hs : T ≤ s) :
    c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Ici
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).1‖) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atTop, ‖(c.splitChart (F t x)).1‖ ≤ ‖(c.splitChart (F s x)).1‖ := by
    filter_upwards [Filter.eventually_ge_atTop T, Filter.eventually_ge_atTop t] with s hs hst
    rw [hformula t ht s hs]
    exact MorseHandle.norm_fst_le_descentFlow (sub_nonneg.mpr hst) _
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
/-- An outgoing Morse tail exists. -/
theorem MorseCancellation.exists_outgoing_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≤ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≤ T, (c.splitChart (F t x)).2 = 0) ∧
          ∀ t ≤ T,
            ∀ s ≤ T,
              c.splitChart (F s x) =
                MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.mp htail
  have hformula (t : ℝ) (ht : t ≤ T) (s : ℝ) (hs : s ≤ T) :
    c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Iic
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).2‖) Filter.atBot (𝓝 0) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atBot, ‖(c.splitChart (F t x)).2‖ ≤ ‖(c.splitChart (F s x)).2‖ := by
    filter_upwards [Filter.eventually_le_atBot T, Filter.eventually_le_atBot t] with s hs hst
    rw [hformula t ht s hs, MorseHandle.norm_descentFlow_snd]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (by linarith))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
/-- The incoming tail lies on the cubic axis. -/
theorem MorseCancellation.incoming_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (1 / 2, 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) 1 ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) 1 q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.PositiveCoordinates} (hL : L (-r, 0) = (0, v))
    (hbase : c.splitChart (F T x) = (0, v))
    (hmodel :
      ∀ t ≥ T,
        c.splitChart (F t x) = MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atTop,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atTop, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_ge_atTop T] with t ht hT
  have hline : c.splitChart (F t x) = L (-r * Real.exp (-(t - T)), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_incoming_aligned_ray L hL (t - T)
  have hdir : 0 < -(1 : ℝ) * (-r * Real.exp (-(t - T))) := by nlinarith [Real.exp_pos (-(t - T))]
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing tail lies on the cubic axis. -/
theorem MorseCancellation.outgoing_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (-(1 / 2 : ℝ), 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) (-1) ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) (-1) q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.NegativeCoordinates} (hL : L (r, 0) = (v, 0))
    (hbase : c.splitChart (F T x) = (v, 0))
    (hmodel :
      ∀ t ≤ T,
        c.splitChart (F t x) = MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atBot,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atBot, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_le_atBot T] with t ht hT
  have hline : c.splitChart (F t x) = L (r * Real.exp (t - T), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_outgoing_aligned_ray L hL (t - T)
  have hdir : 0 < -(-1 : ℝ) * (r * Real.exp (t - T)) := by
    simpa using mul_pos hr (Real.exp_pos (t - T))
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (-1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
/-- The Morse coordinates are nonzero on a nonstationary orbit. -/
theorem MorseCancellation.morse_coordinates_nonzero_on_nonstationary_orbit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {t : ℝ} (ht : F t x ∈ c.splitChart.source) :
    c.splitChart (F t x) ≠ 0 := by
  have heqp : V p = c.descentField p :=
    mem_of_mem_nhds (x := p) (s := {y : M | V y = c.descentField y}) heq
  have hVp : V p = 0 := heqp.trans c.descentField_center
  have hfixed := FlowConstruction.flow_fixed_of_zero hV F hF hVp
  intro hz
  have hpoint : F t x = p :=
    c.splitChart.toOpenPartialHomeomorph.injOn ht c.splitChart_mem_source
      (hz.trans c.splitChart_center.symm)
  have hh := congrArg (F (-t)) hpoint
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hfixed] at hh
  exact hxp hh

attribute [local instance 100] Classical.propDecidable in
/-- An actual incoming cubic endpoint exists. -/
theorem MorseCancellation.exists_actual_incoming_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (1 / 2, 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atTop,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z, L (endpointLinearField σ (1 / 2) 1 z) = MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source, c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) 1 z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_incoming_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).2
  have hbase : c.splitChart (F T x) = (0, v) := Prod.ext (hzero T le_rfl) rfl
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext rfl hv))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_incoming_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) 1 q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (1 : ℝ) ^ 2 = 1) L hL' V heq
  refine ⟨Φ, hc, hval, hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      incoming_tail_on_cubic_axis c Φ L hc hval hcoord F x hlim hr hLray hbase (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
/-- An actual outgoing cubic endpoint exists. -/
theorem MorseCancellation.exists_actual_outgoing_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (-(1 / 2 : ℝ), 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atBot,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z,
                      L (endpointLinearField σ (1 / 2) (-1) z) =
                        MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source,
                      c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) (-1) z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_outgoing_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).1
  have hbase : c.splitChart (F T x) = (v, 0) := Prod.ext rfl (hzero T le_rfl)
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext hv rfl))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_outgoing_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) (-1) q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (-1 : ℝ) ^ 2 = 1) L hL' V heq
  have hc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source := by convert! hc using 1; norm_num
  have hval' : Φ (-(1 / 2 : ℝ), 0) = p := by convert! hval using 1; norm_num
  refine ⟨Φ, hc', hval', hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      outgoing_tail_on_cubic_axis c Φ L hc' hval' hcoord F x hlim hr hLray hbase
        (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
/-- The backward basin meets the attaching core. -/
theorem MorseCancellation.native_backward_basin_mem_attaching_core {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    ∃ u : PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_outgoing_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).1‖) Filter.atBot (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_le_atBot T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).1 ≠ 0 := fun hz => hnonzero (Prod.ext hz (hplane s hs))
  obtain ⟨u, t, ht, hu⟩ := exists_negative_core_ray_parameter hr hn hsmall
  have hmodel :
    MorseHandle.descentFlow t
        (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · exact hu
    · change Real.exp (-t) • (0 : c.PositiveCoordinates) = (c.splitChart (F s x)).2
      rw [smul_zero, hplane s hs]
  have hcore := native_attaching_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.attachingCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary
        (c.attachingCoreMap r hr hblock u).property hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core is the backward basin. -/
theorem MorseCancellation.native_attaching_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔
      ∃ u : PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock u : M) = x := by
  constructor
  · exact
      native_backward_basin_mem_attaching_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_attaching_core_backward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
/-- The forward basin meets the belt core. -/
theorem MorseCancellation.native_forward_basin_mem_belt_core {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_incoming_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).2‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_ge_atTop T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).2 ≠ 0 := fun hz => hnonzero (Prod.ext (hplane s hs) hz)
  obtain ⟨u, t, ht, hu⟩ := exists_positive_core_ray_parameter hr hn hsmall
  have hmodel :
    MorseHandle.descentFlow t
        ((0 : c.NegativeCoordinates), r • (u : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · change Real.exp t • (0 : c.NegativeCoordinates) = (c.splitChart (F s x)).1
      rw [smul_zero, hplane s hs]
    · exact hu
  have hcore := native_belt_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.beltCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary (c.beltCoreMap r hr hblock u).property
        hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
/-- The belt core is the forward basin. -/
theorem MorseCancellation.native_belt_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
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
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔
      ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock u : M) = x := by
  constructor
  · exact native_forward_basin_mem_belt_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_belt_core_forward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

/-! ### The cubic axis parameter -/

/-- `tanh` differentiates to `sech²`. -/
theorem MorseCancellation.hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hf : (fun x => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  change HasDerivAt (fun x => Real.sinh x / Real.cosh x) _ t at h
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `tanh` is strictly monotone. -/
theorem MorseCancellation.strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh (fun t => sub_pos.mpr (Real.tanh_sq_lt_one t))

/-- `tanh` has range `(−1, 1)`. -/
theorem MorseCancellation.range_tanh : Set.range Real.tanh = Set.Ioo (-1 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  · intro hs
    obtain ⟨t, -, ht⟩ := Real.tanh_surjOn hs
    exact ⟨t, ht⟩

/-- `tanh` tends to `1` at infinity. -/
theorem MorseCancellation.tendsto_tanh_atTop : Filter.Tendsto Real.tanh Filter.atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_atTop_isLUB strictMono_tanh.monotone
  rw [range_tanh]
  exact isLUB_Ioo (by norm_num)

/-- `tanh` tends to `−1` at negative infinity. -/
theorem MorseCancellation.tendsto_tanh_atBot : Filter.Tendsto Real.tanh Filter.atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_atBot_isGLB strictMono_tanh.monotone
  rw [range_tanh]
  exact isGLB_Ioo (by norm_num)

/-- The time parameter along the cubic axis. -/
def MorseCancellation.cubicAxisParameter (a t : ℝ) : ℝ :=
  a * Real.tanh (a * t)

/-- The cubic axis parameter is differentiable. -/
theorem MorseCancellation.hasDerivAt_cubicAxisParameter (a t : ℝ) :
    HasDerivAt (cubicAxisParameter a) (a ^ 2 - cubicAxisParameter a t ^ 2) t := by
  have h := ((hasDerivAt_tanh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a
  change HasDerivAt (cubicAxisParameter a) (a * ((1 - Real.tanh (a * t) ^ 2) * (a * 1))) t at h
  convert h using 1
  dsimp [cubicAxisParameter]
  ring

/-- The cubic axis parameter lies in the axis. -/
theorem MorseCancellation.cubicAxisParameter_mem {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisParameter a t ∈ Set.Ioo (-a) a := by
  have hlo := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * t)) ha
  have hhi := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * t)) ha
  constructor
  · simpa only [cubicAxisParameter, mul_neg, mul_one] using hlo
  · simpa only [cubicAxisParameter, mul_one] using hhi

/-- The cubic axis parameter's range. -/
theorem MorseCancellation.range_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Set.range (cubicAxisParameter a) = Set.Ioo (-a) a := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact cubicAxisParameter_mem ha t
  · intro hs
    have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · apply (lt_div_iff₀ ha).mpr
        simpa only [neg_one_mul] using hs.1
      · apply (div_lt_iff₀ ha).mpr
        simpa only [one_mul] using hs.2
    refine ⟨Real.artanh (s / a) / a, ?_⟩
    simp only [cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

/-- The axis parameter tends to the positive endpoint. -/
theorem MorseCancellation.tendsto_cubicAxisParameter_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 a) := by
  have h := (tendsto_tanh_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 (a * 1)) at h
  simpa only [mul_one] using h

/-- The axis parameter tends to the negative endpoint. -/
theorem MorseCancellation.tendsto_cubicAxisParameter_atBot {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (-a)) := by
  have h := (tendsto_tanh_atBot.comp (Filter.tendsto_id.const_mul_atBot ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (a * -1)) at h
  simpa only [mul_neg, mul_one] using h

/-! ### The cubic model orbit -/

/-- The orbit of the cubic model. -/
def MorseCancellation.cubicModelOrbit {m : ℕ} (a t : ℝ) : Model m :=
  (cubicAxisParameter a t, 0)

/-- The cubic model orbit at time zero. -/
theorem MorseCancellation.cubicModelOrbit_zero {m : ℕ} (a : ℝ) : cubicModelOrbit (m := m) a 0 = 0 := by
  simp [cubicModelOrbit, cubicAxisParameter, Real.tanh_zero]

/-- The cubic model orbit solves the field. -/
theorem MorseCancellation.hasDerivAt_cubicModelOrbit {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    HasDerivAt (cubicModelOrbit a) (cubicDescent σ (-(a ^ 2)) (cubicModelOrbit a t)) t := by
  have h := (hasDerivAt_cubicAxisParameter a t).prodMk (hasDerivAt_const t (0 : Fin m → ℝ))
  change HasDerivAt (cubicModelOrbit a) (a ^ 2 - cubicAxisParameter a t ^ 2, 0) t at h
  convert h using 1
  apply Prod.ext
  · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
    ring
  · funext i
    simp only [cubicDescent, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]

/-- The cubic model orbit's range. -/
theorem MorseCancellation.range_cubicModelOrbit {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Set.range (cubicModelOrbit (m := m) a) = Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨cubicAxisParameter_mem ha t, rfl⟩
  · rintro ⟨hs, hz⟩
    obtain ⟨t, ht⟩ := (range_cubicAxisParameter ha).symm ▸ hs
    refine ⟨t, ?_⟩
    exact Prod.ext ht (show (0 : Fin m → ℝ) = p.2 from hz.symm)

/-- The model orbit tends to the positive end. -/
theorem MorseCancellation.tendsto_cubicModelOrbit_atTop {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atTop (𝓝 (a, 0)) :=
  (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds tendsto_const_nhds

/-- The model orbit tends to the negative end. -/
theorem MorseCancellation.tendsto_cubicModelOrbit_atBot {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atBot (𝓝 (-a, 0)) :=
  (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds tendsto_const_nhds

/-- `artanh` is smooth on `(−1,1)`. -/
theorem MorseCancellation.contDiffAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ Real.artanh x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hr : ContDiffAt ℝ ∞ (fun y : ℝ => (1 + y) / (1 - y)) x :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
      (by linarith [hx.2])
  exact (hr.sqrt hp.ne').log (Real.sqrt_pos.mpr hp).ne'

/-- The cubic axis parameter is smooth. -/
theorem MorseCancellation.contDiff_cubicAxisParameter (a : ℝ) : ContDiff ℝ ∞ (cubicAxisParameter a) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    have hh : ContDiff ℝ ∞ (fun t => Real.sinh t / Real.cosh t) :=
      Real.contDiff_sinh.div Real.contDiff_cosh (fun t => (Real.cosh_pos t).ne')
    have he : (fun t => Real.sinh t / Real.cosh t) = Real.tanh :=
      funext (fun t => (Real.tanh_eq_sinh_div_cosh t).symm)
    rw [he] at hh
    exact hh
  change ContDiff ℝ ∞ (fun t => a * Real.tanh (a * t))
  exact contDiff_const.mul (ht.comp (contDiff_const.mul contDiff_id))

/-- The clock function inverse to the axis parameter. -/
def MorseCancellation.cubicAxisClock (a s : ℝ) : ℝ :=
  Real.artanh (s / a) / a

/-- The clock inverts the axis parameter. -/
theorem MorseCancellation.cubicAxisClock_parameter {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisClock a (cubicAxisParameter a t) = t := by
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel_left₀ _ ha.ne', Real.artanh_tanh]

/-- The axis parameter inverts the clock. -/
theorem MorseCancellation.cubicAxisParameter_clock {a s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Ioo (-a) a) :
    cubicAxisParameter a (cubicAxisClock a s) = s := by
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

/-- The cubic axis clock is smooth. -/
theorem MorseCancellation.contDiffOn_cubicAxisClock {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicAxisClock a) (Set.Ioo (-a) a) := by
  intro s hs
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  exact
    (((contDiffAt_artanh hs').comp s (contDiffAt_id.div_const a)).div_const a).contDiffWithinAt
