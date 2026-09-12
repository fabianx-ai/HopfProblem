/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
/-!
# The Morse cancellation toolbox

The chart-level cancellation machinery: given two critical points of adjacent
index connected across a regular level, the modifying fields, local
replacements and flow manipulations that remove the pair without changing the
sublevel homotopy type (Milnor, *Lectures on the h-cobordism theorem*, Thm
4.1; Milnor, *Morse Theory* §3).

## Outline

1. `MorseCancel`: the native Morse index of a critical point, quadratic germs
   and their classification, signed Morse charts, adapted surgeries and the
   clock-normalized cubic endpoint control.
2. `Degree.FlowCancellation` and `Degree.FlowSuspension`: strict flow descent
   into sublevel sets, level basins, smooth time germs and the suspension of
   isotopies to flows.
3. `Degree.LocalFunctionReplacement` / `Degree.LocalFieldReplacement`: replacing
   a function or gradient-like field on a compact support.
4. `Smale.FiberwiseDiffeomorph` and the E1-positioned
   `Smale.SupportedDiffeomorph` material: diffeomorphisms supported in a chart.

## Main definitions and results

* `MorseCancellation.nativeMorseIndex` - the chart-independent Morse index.
* `MorseCancellation.equivalent_quadratic_germs_of_bijective_derivative` - germ
  classification behind the Morse lemma.
* `MorseCancellation.adapted_surgeries_after_pair_removal` - the windows after a
  cancellation.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Thm 4.1.
* [milnor63] J. Milnor, *Morse Theory*, §3.

## Tags

morse-theory, cancellation, h-cobordism, quadratic-germs
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nonempty_adaptedSurgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) :
    Nonempty (AdaptedWindows E f) := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  let : Finite (Smale.ManifoldMorse.criticalPoints E f) := hfinite.to_subtype
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex :
    ∀ p : Smale.ManifoldMorse.criticalPoints E f,
      ∃ d : Smale.ManifoldMorse.MorseSurgeryData E f p.val,
        d.radius < r p / 3 ∧
          ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      Smale.ManifoldMorse.exists_morseSurgeryData_lt hf hm p.property
        (fun x hx hfx => hinj hx p.property hfx) (div_pos (hr p) (by norm_num))
  choose d hd hisolated using hex
  have hsq (p : Smale.ManifoldMorse.criticalPoints E f) : 9 * (d p).radius ^ 2 < (r p) ^ 2 := by
    have hsmall : 3 * (d p).radius < r p := by linarith [hd p]
    have hsum : 0 < r p + 3 * (d p).radius :=
      add_pos (hr p) (mul_pos (by norm_num) (d p).radius_pos)
    nlinarith [mul_pos (sub_pos.mpr hsmall) hsum]
  have hwide (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + 9 * (d p).radius ^ 2 < f q - 9 * (d q).radius ^ 2 := by
    linarith [hgap p q hpq, hsq p, hsq q]
  have hintervals :
    Pairwise
      (fun p q : Smale.ManifoldMorse.criticalPoints E f =>
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
      (fun p : Smale.ManifoldMorse.criticalPoints E f => p.val) (fun p => p.property)
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

theorem MorseCancellation.exists_forward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ T : ℝ,
      0 < T ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
            Smale.MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) < 0 := by
  let T := Real.log (r / ‖z.1‖)
  have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.1‖ := (one_lt_div hn).mpr hzn
  have hT : 0 < T := Real.log_pos hratio
  have hexp : Real.exp T = r / ‖z.1‖ := Real.exp_log (div_pos hr hn)
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).1‖ = r := by
    rw [Smale.MorseHandle.norm_descentFlow_fst, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall : ‖(Smale.MorseHandle.descentFlow T z).2‖ < r :=
    (Smale.MorseHandle.norm_snd_descentFlow_le hT.le z).trans_lt hzp
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      calc
        Real.exp t * ‖z.1‖ ≤ Real.exp T * ‖z.1‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
    · exact
        mem_closedBall_zero_iff.mpr
          ((Smale.MorseHandle.norm_snd_descentFlow_le ht.1 z).trans hzp.le)
  · change
      -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2 <
        0
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hsmall
    linarith

theorem MorseCancellation.exists_backward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ T : ℝ,
      T < 0 ∧
        (∀ t ∈ Set.Icc T (0 : ℝ),
            Smale.MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          0 < Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) := by
  let T := -Real.log (r / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.2‖ := (one_lt_div hn).mpr hzp
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = r / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hr hn)]
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).2‖ = r := by
    rw [Smale.MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(Smale.MorseHandle.descentFlow t z).1‖ < r := by
    rw [Smale.MorseHandle.norm_descentFlow_fst]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans_lt hzn
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · exact mem_closedBall_zero_iff.mpr (hsmall t ht.2).le
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
  · change
      0 <
        -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (hsmall T hT.le)
    linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
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
theorem MorseCancellation.exists_native_forward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    Smale.MorseHandle.descentFlow s (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [Set.uIcc_of_le hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨hT.le, le_rfl⟩))]
  change
    -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 <
      0 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_native_backward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    Smale.MorseHandle.descentFlow s (c.splitChart x) ∈
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
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_morse_positive_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    Smale.MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst, hzero, norm_zero,
        MulZeroClass.mul_zero]
      exact hr.le
    · exact
        mem_closedBall_zero_iff.mpr
          ((Smale.MorseHandle.norm_snd_descentFlow_le ht (c.splitChart x)).trans hp.le)
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
    Filter.Tendsto (fun t => Smale.MorseHandle.descentFlow t (c.splitChart x)) Filter.atTop
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hn :
    Filter.Tendsto (fun t => c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atTop (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hn
  apply hn.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_morse_negative_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    Smale.MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans hn.le
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd, hzero, norm_zero,
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
    Filter.Tendsto (fun t => Smale.MorseHandle.descentFlow t (c.splitChart x)) Filter.atBot
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hh :
    Filter.Tendsto (fun t => c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atBot (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_native_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
theorem MorseCancellation.exists_descending_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
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
    (Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc) heq

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_attaching_core_backward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) :
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
theorem MorseCancellation.native_belt_core_forward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
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
theorem MorseCancellation.native_attaching_core_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) {t : ℝ} (ht : t ≤ 0) :
    F t (c.attachingCoreMap r hr hblock u) =
      c.splitChart.symm (Smale.MorseHandle.descentFlow t (r • (u : c.NegativeCoordinates), 0)) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (r • (u : c.NegativeCoordinates), 0)
  have hn : ‖z.1‖ = r := by
    change ‖r • (u : c.NegativeCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property,
      mul_one]
  have hstay (s : ℝ) (hs : s ≤ 0) :
    Smale.MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hs) hr.le
      nlinarith
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
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
theorem MorseCancellation.native_belt_core_flow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) {t : ℝ} (ht : 0 ≤ t) :
    F t (c.beltCoreMap r hr hblock v) =
      c.splitChart.symm (Smale.MorseHandle.descentFlow t (0, r • (v : c.PositiveCoordinates))) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (0, r • (v : c.PositiveCoordinates))
  have hn : ‖z.2‖ = r := by
    change ‖r • (v : c.PositiveCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp v.property,
      mul_one]
  have hstay (s : ℝ) (hs : 0 ≤ s) :
    Smale.MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      change Real.exp s * ‖(0 : c.NegativeCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, MulZeroClass.mul_zero]
      positivity
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd, hn]
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

theorem MorseCancellation.exists_negative_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : Smale.PuncturedHandle.UnitSphere A) (t : ℝ), t < 0 ∧ Real.exp t • (r • (u : A)) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Smale.PuncturedHandle.UnitSphere A :=
    ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩
  have hratio : 0 < ‖z‖ / r := div_pos hn hr
  have hratio1 : ‖z‖ / r < 1 := (div_lt_one hr).mpr hzr
  have hcoef : Real.exp (Real.log (‖z‖ / r)) * r * ‖z‖⁻¹ = 1 := by
    rw [Real.exp_log hratio]
    field_simp
  refine ⟨u, Real.log (‖z‖ / r), Real.log_neg hratio hratio1, ?_⟩
  change Real.exp (Real.log (‖z‖ / r)) • (r • (‖z‖⁻¹ • z)) = z
  rw [smul_smul, smul_smul, hcoef, one_smul]

theorem MorseCancellation.exists_positive_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : Smale.PuncturedHandle.UnitSphere A) (t : ℝ),
      0 < t ∧ Real.exp (-t) • (r • (u : A)) = z := by
  obtain ⟨u, t, ht, heq⟩ := exists_negative_core_ray_parameter hr hz hzr
  exact ⟨u, -t, neg_pos.mpr ht, by simpa only [neg_neg] using heq⟩

theorem Degree.FlowCancellation.exists_local_strict_flow_descent {X : Type*} [TopologicalSpace X]
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

theorem Degree.FlowCancellation.exists_local_strict_sublevel_entry {X : Type*}
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

theorem Degree.FlowCancellation.forwardInvariant_sublevel_of_boundary {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ c := by
  apply Smale.FlowConstruction.forwardInvariant_of_local F (isClosed_le hf continuous_const)
  intro x hx
  obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | htpos
  · simpa only [← ht0, F.map_zero_apply] using hx
  · exact (hentry t ⟨htpos, ht.2⟩).le

theorem Degree.FlowCancellation.interior_sublevel_eq_of_boundary {X : Type*} [TopologicalSpace X]
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

theorem Degree.FlowCancellation.strict_sublevel_entry_of_boundary {X : Type*} [TopologicalSpace X]
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
  have hi := Smale.FlowConstruction.interior_entry_of_local F hforward hlocal x hx t ht
  have hi' : F t x ∈ interior {y | f y ≤ c} := hi
  exact
    Eq.mp
      (congrArg (fun S : Set X => F t x ∈ S)
        (interior_sublevel_eq_of_boundary F hf hder hboundary))
      hi'

def Degree.FlowCancellation.levelBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)
    (c : ℝ) : Set X :=
  {x | ∃ t : ℝ, f (F t x) = c}

def Degree.FlowCancellation.signedLevelTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c : ℝ) (x : X) : ℝ := by
  classical exact if h : x ∈ levelBasin F f c then h.choose else 0

theorem Degree.FlowCancellation.signedLevelTime_hits {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {x : X} (hx : x ∈ levelBasin F f c) :
    f (F (signedLevelTime F f c x) x) = c := by
  rw [signedLevelTime, dif_pos hx]
  exact hx.choose_spec

theorem Degree.FlowCancellation.levelBasin_flow_iff {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c s : ℝ) (x : X) :
    F s x ∈ levelBasin F f c ↔ x ∈ levelBasin F f c := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t + s, by simpa only [F.map_add] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    simpa only [← F.map_add, sub_add_cancel] using ht

theorem Degree.FlowCancellation.flow_level_time_unique {X : Type*} [TopologicalSpace X]
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

theorem Degree.FlowCancellation.signedLevelTime_eq_of_level {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} {t : ℝ} (ht : f (F t x) = c) :
    signedLevelTime F f c x = t :=
  flow_level_time_unique F hf hD hder hboundary x (signedLevelTime_hits F f c ⟨t, ht⟩) ht

theorem Degree.FlowCancellation.signedLevelTime_eq_zero {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : signedLevelTime F f c x = 0 :=
  signedLevelTime_eq_of_level F hf hD hder hboundary (by simpa only [F.map_zero_apply] using hx)

theorem Degree.FlowCancellation.signedLevelTime_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : x ∈ levelBasin F f c) (s : ℝ) :
    signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  apply signedLevelTime_eq_of_level F hf hD hder hboundary
  rw [← F.map_add, sub_add_cancel]
  exact signedLevelTime_hits F f c hx

theorem Smale.FlowConstruction.exists_enlarged_interval {a b : ℝ} (hab : a ≤ b) {W : Set ℝ}
    (hW : IsOpen W) (hIW : Set.Icc a b ⊆ W) : ∃ l u : ℝ, l < a ∧ b < u ∧ Set.Ioo l u ⊆ W := by
  obtain ⟨l, r, hla, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨le_rfl, hab⟩))
  obtain ⟨s, u, hbu, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨hab, le_rfl⟩))
  refine ⟨l, u, hla.1, hbu.2, ?_⟩
  intro y hy
  by_cases hya : y < a
  · exact hL ⟨hy.1, hya.trans hla.2⟩
  by_cases hby : b < y
  · exact hR ⟨hbu.1.trans hby, hy.2⟩
  exact hIW ⟨le_of_not_gt hya, le_of_not_gt hby⟩

theorem Smale.FlowConstruction.scalar_height_translation {φ γ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {W : Set ℝ} (hW : IsOpen W) {a b c t : ℝ} (hIW : Set.Icc a b ⊆ W)
    (hφW : Set.EqOn φ (fun _ => 1) W) (hγ : ∀ s, HasDerivAt γ (φ (γ s)) s) (hγ₀ : γ 0 = c)
    (hc : c ∈ Set.Icc a b) (ht : c + t ∈ Set.Icc a b) : γ t = c + t := by
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_enlarged_interval (hc.1.trans hc.2) hW hIW
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x => (NormedSpace.fromTangentSpace x).symm (φ x)
  have hV :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (hφ.of_le (by simp))
  have hactual : IsMIntegralCurveOn γ V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    exact (hγ s).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hlinear : IsMIntegralCurveOn (fun s => c + s) V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    have hcs : c + s ∈ W := hlu ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd : HasDerivAt (fun r => c + r) (φ (c + s)) s := by
      rw [hφW hcs]
      exact (hasDerivAt_id s).const_add c
    exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have htime : t ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV hactual hlinear
      (by simpa only [add_zero] using hγ₀) htime

theorem Smale.FlowConstruction.exists_heightTranslatingFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ F : Flow ℝ M, ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t := by
  obtain ⟨φ, W, F, hφ, hW, hIW, hφW, hF⟩ := exists_regularBandFlow hf hband
  refine ⟨F, ?_⟩
  intro x t hx ht
  exact scalar_height_translation hφ hW hIW hφW (hF x) (by simp only [Flow.map_zero_apply]) hx ht

theorem MorseCancellation.contMDiff_directionalDerivative {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

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
    Degree.FlowCancellation.flow_level_time_unique F hf.continuous
      (contMDiff_directionalDerivative hf hV).continuous
      (fun z u => Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hF z) u) hboundary x
      (hmove ▸ hy) (show f (F 0 x) = c by rw [F.map_zero_apply]; exact hx)
  simpa only [htime, F.map_zero_apply] using hmove

abbrev MorseCancellation.Model (m : ℕ) :=
  ℝ × (Fin m → ℝ)

def MorseCancellation.cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  p.1 ^ 3 / 3 + t * p.1 + ∑ i, σ i * (p.2 i) ^ 2

def MorseCancellation.differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m →L[ℝ] ℝ :=
  (p.1 ^ 2 + t) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
    ∑ i,
      (2 * σ i * p.2 i) •
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))

theorem MorseCancellation.differential_apply {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p v : Model m) :
    differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i := by
  simp [differential]

theorem MorseCancellation.contDiff_cubic_family {m : ℕ} (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Model m => cubic σ p.1 p.2) := by
  unfold cubic
  fun_prop

theorem MorseCancellation.contDiff_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) : ContDiff ℝ ∞ (cubic σ t) :=
  (contDiff_cubic_family σ).comp (contDiff_const.prodMk contDiff_id)

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

theorem MorseCancellation.fderiv_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = differential σ t p :=
  (hasFDerivAt_cubic σ t p).fderiv

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

theorem MorseCancellation.cubic_zero_unique_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : fderiv ℝ (cubic σ 0) p = 0 ↔ p = 0 := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : p.1 = 0 := by nlinarith [sq_nonneg p.1]
    exact Prod.ext hx' hy
  · rintro rfl
    simp

theorem MorseCancellation.positive_parameter_no_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {t : ℝ} (ht : 0 < t) (p : Model m) : fderiv ℝ (cubic σ t) p ≠ 0 := by
  intro h
  have hx := ((critical_iff σ hσ t p).mp h).1
  nlinarith [sq_nonneg p.1]

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

theorem MorseCancellation.cubic_critical_values {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    cubic σ (-(a ^ 2)) (a, 0) = -(2 * a ^ 3 / 3) ∧ cubic σ (-(a ^ 2)) (-a, 0) = 2 * a ^ 3 / 3 := by
  constructor <;> simp [cubic] <;> ring

def MorseCancellation.endpointCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) * Real.sqrt (a + e * (s - e * a) / 3)

def MorseCancellation.endpointDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * (s - e * a) / 3}

theorem MorseCancellation.endpointDomain_open (a e : ℝ) : IsOpen (endpointDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem MorseCancellation.endpoint_mem_domain {a : ℝ} (ha : 0 < a) (e : ℝ) :
    e * a ∈ endpointDomain a e := by simpa [endpointDomain] using ha

theorem MorseCancellation.endpointCoordinate_center (a e : ℝ) : endpointCoordinate a e (e * a) = 0 := by
  simp [endpointCoordinate]

theorem MorseCancellation.contDiffOn_endpointCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointCoordinate a e) (endpointDomain a e) := by
  intro s hs
  have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => t - e * a) s := contDiffAt_id.sub contDiffAt_const
  exact
    (hlin.mul
        ((contDiffAt_const.add ((contDiffAt_const.mul hlin).div_const 3)).sqrt
          (ne_of_gt hs))).contDiffWithinAt

theorem MorseCancellation.hasDerivAt_endpointCoordinate {a : ℝ} (ha : 0 < a) (e : ℝ) :
    HasDerivAt (endpointCoordinate a e) (Real.sqrt a) (e * a) := by
  have hd :=
    ((hasDerivAt_id (e * a)).sub_const (e * a)).mul
      ((((hasDerivAt_id (e * a)).sub_const (e * a)).const_mul e).div_const 3 |>.const_add
          a |>.sqrt
        (by simpa using ha.ne'))
  convert! hd using 1; simp []

theorem MorseCancellation.cubic_endpoint_square {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (he : e ^ 2 = 1)
    {p : Model m} (hp : p.1 ∈ endpointDomain a e) :
    cubic σ (-(a ^ 2)) p =
      cubic σ (-(a ^ 2)) (e * a, 0) + e * endpointCoordinate a e p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 :=
  by
  simp only [cubic, endpointCoordinate, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

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
    NoExotic.exists_partialDiffeomorph_of_contDiffOn (endpointDomain_open a e)
      (endpoint_mem_domain ha e) (contDiffOn_endpointCoordinate a e) ⟨A, rfl⟩
  exact ⟨Φ, hp, hsub, hΦ, by rw [hΦ, endpointCoordinate_center]⟩

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

def Degree.LocalFunctionReplacement.replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) (y : M) : ℝ := by
  classical exact if y ∈ Φ.target then b (Φ.symm y) else f y

theorem Degree.LocalFunctionReplacement.replace_of_mem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b y = b (Φ.symm y) := by simp [replace, hy]

theorem Degree.LocalFunctionReplacement.replace_of_notMem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∉ Φ.target) :
    replace Φ f b y = f y := by simp [replace, hy]

theorem Degree.LocalFunctionReplacement.replace_chart {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {x : E} (hx : x ∈ Φ.source) :
    replace Φ f b (Φ x) = b x := by
  rw [replace_of_mem Φ f b (Φ.map_source' hx)]
  exact congrArg b (Φ.left_inv' hx)

theorem Degree.LocalFunctionReplacement.replace_germ_chart {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b =ᶠ[𝓝 y] b ∘ Φ.symm := by
  filter_upwards [Φ.open_target.mem_nhds hy] with z hz
  exact replace_of_mem Φ f b hz

theorem Degree.LocalFunctionReplacement.replace_self {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b : E → ℝ}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b x) : replace Φ f b = f := by
  funext y
  by_cases hy : y ∈ Φ.target
  · rw [replace_of_mem Φ f b hy]
    exact (hmodel (Φ.symm y) (Φ.map_target' hy)).symm.trans (congrArg f (Φ.right_inv' hy))
  · exact replace_of_notMem Φ f b hy

theorem Degree.LocalFunctionReplacement.replace_eq_off_support {E B H M : Type*}
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

theorem Degree.LocalFunctionReplacement.replace_germ_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) : replace Φ f b₁ =ᶠ[𝓝 y] f := by
  have hc : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
  exact replace_eq_off_support Φ hmodel hfix hz

theorem Degree.LocalFunctionReplacement.contMDiff_replace {E B H M : Type*} [NormedAddCommGroup E]
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

theorem Degree.LocalFunctionReplacement.replace_critical_iff {E B H M : Type*}
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

def MorseCancellation.cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m :=
  (-(p.1 ^ 2 + t), fun i => -σ i * p.2 i)

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

def MorseCancellation.nativeCubicDescent {m : ℕ} (σ : Fin m → ℝ) {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    (x : M) → TangentSpace 𝓘(ℝ, B) x :=
  Smale.FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)

def MorseCancellation.endpointFieldCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) / (a + e * s)

def MorseCancellation.endpointFieldDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * s}

theorem MorseCancellation.endpointFieldDomain_open (a e : ℝ) : IsOpen (endpointFieldDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem MorseCancellation.endpointField_mem_domain {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    e * a ∈ endpointFieldDomain a e := by
  change 0 < a + e * (e * a)
  have h : e * (e * a) = a := by rw [← mul_assoc, ← pow_two, he, one_mul]
  rw [h]
  linarith

theorem MorseCancellation.endpointFieldCoordinate_center (a e : ℝ) :
    endpointFieldCoordinate a e (e * a) = 0 := by simp [endpointFieldCoordinate]

theorem MorseCancellation.contDiffOn_endpointFieldCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointFieldCoordinate a e) (endpointFieldDomain a e) := by
  intro s hs
  exact
    ((contDiffAt_id.sub contDiffAt_const).div
        (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (ne_of_gt hs)).contDiffWithinAt

theorem MorseCancellation.hasDerivAt_endpointFieldCoordinate (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    HasDerivAt (endpointFieldCoordinate a e) (2 * a / (a + e * s) ^ 2) s := by
  have hd :=
    ((hasDerivAt_id s).sub_const (e * a)).div (((hasDerivAt_id s).const_mul e).const_add a)
      (ne_of_gt hs)
  convert! hd using 1
  congr 1
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

theorem MorseCancellation.endpointFieldCoordinate_pushforward (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    deriv (endpointFieldCoordinate a e) s * (a ^ 2 - s ^ 2) =
      (-2 * e * a) * endpointFieldCoordinate a e s := by
  rw [(hasDerivAt_endpointFieldCoordinate a he hs).deriv]
  unfold endpointFieldCoordinate
  have hn : a + e * s ≠ 0 := ne_of_gt hs
  field_simp
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

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
    NoExotic.exists_partialDiffeomorph_of_contDiffOn (endpointFieldDomain_open a e) hm
      (contDiffOn_endpointFieldCoordinate a e) ⟨A, rfl⟩
  exact ⟨P, hp, hsub, hP, by rw [hP, endpointFieldCoordinate_center]⟩

def MorseCancellation.endpointLinearField {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (p : Model m) : Model m :=
  ((-2 * e * a) * p.1, fun i => -σ i * p.2 i)

def MorseCancellation.endpointFieldProduct {m : ℕ} (a e : ℝ) (p : Model m) : Model m :=
  (endpointFieldCoordinate a e p.1, p.2)

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

theorem MorseCancellation.partialChartField_of_model_conjugacy {D F E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, F) D F ∞) (Q : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (W : D → D) (U : F → F) (hpush : ∀ p ∈ P.source, fderiv ℝ P p (W p) = U (P p)) {x : M}
    (hx : x ∈ (P.trans Q).target) :
    Smale.FlowConstruction.partialChartField (P.trans Q).symm W x =
      Smale.FlowConstruction.partialChartField Q.symm U x := by
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
    change Smale.FlowConstruction.partialChartField P.symm W (Q.symm x) = _
    rw [Smale.FlowConstruction.partialChartField_eq_mfderiv_symm P.symm W hxP]
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

theorem MorseCancellation.exists_native_cubic_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (h0 : (0 : Model m) ∈ Q.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ x ∈ Q.target,
        V x = Smale.FlowConstruction.partialChartField Q.symm (endpointLinearField σ a e) x) :
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

def MorseCancellation.splitEquiv {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃L[ℝ] (Fin n → ℝ) :=
  (splitLinear ρ).toContinuousLinearEquiv

theorem MorseCancellation.splitEquiv_apply_none {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m) :
    splitEquiv ρ p (ρ Option.none) = p.1 := by
  change (ρ.symm (ρ Option.none)).elim p.1 p.2 = p.1
  simp

theorem MorseCancellation.splitEquiv_apply_some {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m)
    (i : Fin m) : splitEquiv ρ p (ρ (Option.some i)) = p.2 i := by
  change (ρ.symm (ρ (Option.some i))).elim p.1 p.2 = p.2 i
  simp

theorem MorseCancellation.split_signed_sum {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ)
    (p : Model m) :
    (∑ j, w j * splitEquiv ρ p j ^ 2) =
      w (ρ Option.none) * p.1 ^ 2 + ∑ i, w (ρ (Option.some i)) * p.2 i ^ 2 := by
  rw [← ρ.sum_comp]
  simp only [Fintype.sum_option, splitEquiv_apply_none, splitEquiv_apply_some]

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
theorem MorseCancellation.splitCoordinates_signed_descent {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    Smale.MorseHandle.splitCoordinates w (fun i => -w i * z i) =
      Smale.MorseHandle.descent (Smale.MorseHandle.splitCoordinates w z) := by
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
def MorseCancellation.selectedMorseFieldEquiv {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates) :=
  (splitEquiv ρ).trans (Smale.MorseHandle.splitCoordinates c.weights)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.selectedMorseFieldEquiv_descent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (p : Model m) :
    selectedMorseFieldEquiv c ρ
        (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
          (c.weights (ρ Option.none)) p) =
      Smale.MorseHandle.descent (selectedMorseFieldEquiv c ρ p) := by
  change
    Smale.MorseHandle.splitCoordinates c.weights (splitEquiv ρ _) =
      Smale.MorseHandle.descent (Smale.MorseHandle.splitCoordinates c.weights (splitEquiv ρ p))
  rw [splitEquiv_endpoint_field]
  exact splitCoordinates_signed_descent c.weights c.signs (splitEquiv ρ p)

def MorseCancellation.transverseFieldChange {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    Model m ≃L[ℝ] Model m :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr T

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

def MorseCancellation.splitTransverseChange {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (e : (Fin m → ℝ) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (e.trans (P.prodCongr S)).trans e.symm

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

theorem MorseCancellation.morse_block_change_descent {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P)
    (z : N × P) :
    (A.prodCongr B) (Smale.MorseHandle.descent z) =
      Smale.MorseHandle.descent ((A.prodCongr B) z) := by
  apply Prod.ext
  · rfl
  · change B (-z.2) = -B z.2
    exact B.map_neg _

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
theorem MorseCancellation.selectedMorseFieldEquiv_axis_ne_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ)) ≠ 0 := by
  intro h
  have hh :=
    (selectedMorseFieldEquiv c ρ).injective
      (h.trans (map_zero (selectedMorseFieldEquiv c ρ)).symm)
  have h1 := congrArg Prod.fst hh
  norm_num at h1

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.selectedMorseFieldEquiv_negative_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
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
theorem MorseCancellation.selectedMorseFieldEquiv_positive_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
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
theorem MorseCancellation.exists_selected_outgoing_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {v : c.NegativeCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (r, 0) = (v, 0) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              Smale.MorseHandle.descent (L p) := by
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
    change B (L₀ _) = Smale.MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_selected_incoming_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {v : c.PositiveCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (-r, 0) = (0, v) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              Smale.MorseHandle.descent (L p) := by
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
    change B (L₀ _) = Smale.MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_cubic_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p)) :
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
        Smale.FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
      fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p)
      rw [L.fderiv]
      exact hL p
    exact
      (partialChartField_of_model_conjugacy P c.splitChart.symm (endpointLinearField σ (1 / 2) e)
          Smale.MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0 c.descentField
      hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf, hmap⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_original_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ := exists_cubic_field_endpoint_with_alignment c σ he L hL
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp heq
  let Ψ := Smale.PartialChart.restrictTarget Φ hU
  have hpΨ : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hp, hc.symm ▸ hxU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, hmap⟩
  intro y hy
  exact (hUsub hy.2).trans (hf y hy.1)

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
theorem MorseCancellation.exists_controlled_morse_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ) {e : ℝ}
    (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p))
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
  let Ψ := Smale.PartialChart.restrictSource Φ hU
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

theorem MorseCancellation.descentFlow_outgoing_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : N} (hL : L (r, 0) = (v, 0)) (t : ℝ) :
    Smale.MorseHandle.descentFlow t (L (r, 0)) = L (r * Real.exp t, 0) := by
  have he : (r * Real.exp t, (0 : Fin m → ℝ)) = Real.exp t • (r, 0) := by
    apply Prod.ext
    · change r * Real.exp t = Real.exp t * r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • v, Real.exp (-t) • (0 : P)) = (Real.exp t • v, Real.exp t • (0 : P))
  simp

theorem MorseCancellation.descentFlow_incoming_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : P} (hL : L (-r, 0) = (0, v)) (t : ℝ) :
    Smale.MorseHandle.descentFlow t (L (-r, 0)) = L (-r * Real.exp (-t), 0) := by
  have he : (-r * Real.exp (-t), (0 : Fin m → ℝ)) = Real.exp (-t) • (-r, 0) := by
    apply Prod.ext
    · change -r * Real.exp (-t) = Real.exp (-t) * -r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • (0 : N), Real.exp (-t) • v) = (Real.exp (-t) • (0 : N), Real.exp (-t) • v)
  simp

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
theorem MorseCancellation.eventually_morse_coordinate_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) (t : ℝ)
    (ht : F t x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) :
    ∀ᶠ s in 𝓝 t,
      c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  have hlocal :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      F u (F t x) = c.splitChart.symm (Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    c.eventually_flow_eq_descentModel hV F hF ht heq
  have htime : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t
  have hmodel :
    Continuous (fun u : ℝ => Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const
  have htarget :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      Smale.MorseHandle.descentFlow u (c.splitChart (F t x)) ∈ c.splitChart.target := by
    have hnhds : ∀ᶠ y in 𝓝 (c.splitChart (F t x)), y ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (c.splitChart.map_source' ht)
    have hm0 :
      Filter.Tendsto (fun u : ℝ => Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) (𝓝 0)
        (𝓝 (c.splitChart (F t x))) := by simpa only [Flow.map_zero_apply] using hmodel.tendsto 0
    exact hm0.eventually hnhds
  filter_upwards [htime.eventually hlocal, htime.eventually htarget] with s hs hst
  rw [← F.map_add, sub_add_cancel] at hs
  have hh := congrArg c.splitChart hs
  exact hh.trans (c.splitChart.right_inv' hst)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.morse_coordinates_of_actual_trajectory {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) {S : Set ℝ}
    (hS : IsPreconnected S) (htarget : ∀ t ∈ S, F t x ∈ c.splitChart.source)
    (heq : ∀ t ∈ S, ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) {t₀ t : ℝ} (h₀ : t₀ ∈ S)
    (ht : t ∈ S) :
    c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - t₀) (c.splitChart (F t₀ x)) :=
  flow_formula_of_local_shifts Smale.MorseHandle.descentFlow (fun s => c.splitChart (F s x)) hS
    (fun s hs => eventually_morse_coordinate_flow c hV F hF x s (htarget s hs) (heq s hs)) h₀ ht

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.morse_endpoint_tail_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
theorem MorseCancellation.exists_incoming_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
                Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hformula (t : ℝ) (ht : T ≤ t) (s : ℝ) (hs : T ≤ s) :
    c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
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
    exact Smale.MorseHandle.norm_fst_le_descentFlow (sub_nonneg.mpr hst) _
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_outgoing_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
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
                Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.mp htail
  have hformula (t : ℝ) (ht : t ≤ T) (s : ℝ) (hs : s ≤ T) :
    c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
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
    rw [hformula t ht s hs, Smale.MorseHandle.norm_descentFlow_snd]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (by linarith))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.incoming_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
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
        c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
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
theorem MorseCancellation.outgoing_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
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
        c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
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
theorem MorseCancellation.morse_coordinates_nonzero_on_nonstationary_orbit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {t : ℝ} (ht : F t x ∈ c.splitChart.source) :
    c.splitChart (F t x) ≠ 0 := by
  have heqp : V p = c.descentField p :=
    mem_of_mem_nhds (x := p) (s := {y : M | V y = c.descentField y}) heq
  have hVp : V p = 0 := heqp.trans c.descentField_center
  have hfixed := Smale.FlowConstruction.flow_fixed_of_zero hV F hF hVp
  intro hz
  have hpoint : F t x = p :=
    c.splitChart.toOpenPartialHomeomorph.injOn ht c.splitChart_mem_source
      (hz.trans c.splitChart_center.symm)
  have hh := congrArg (F (-t)) hpoint
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hfixed] at hh
  exact hxp hh

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_actual_incoming_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
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
                  (∀ z, L (endpointLinearField σ (1 / 2) 1 z) = Smale.MorseHandle.descent (L z)) ∧
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
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) 1 q) = Smale.MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (1 : ℝ) ^ 2 = 1) L hL' V heq
  refine ⟨Φ, hc, hval, hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      incoming_tail_on_cubic_axis c Φ L hc hval hcoord F x hlim hr hLray hbase (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_actual_outgoing_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
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
                        Smale.MorseHandle.descent (L z)) ∧
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
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) (-1) q) = Smale.MorseHandle.descent (L q) := by
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
theorem MorseCancellation.native_backward_basin_mem_attaching_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
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
    ∃ u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
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
    Smale.MorseHandle.descentFlow t
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
theorem MorseCancellation.native_attaching_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
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
      ∃ u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock u : M) = x := by
  constructor
  · exact
      native_backward_basin_mem_attaching_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_attaching_core_backward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_forward_basin_mem_belt_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
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
    ∃ u : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
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
    Smale.MorseHandle.descentFlow t
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
theorem MorseCancellation.native_belt_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
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
      ∃ u : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock u : M) = x := by
  constructor
  · exact native_forward_basin_mem_belt_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_belt_core_forward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.attaching_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (x : (S.data p).LowerLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.attachingSphere := by
  let d := S.data p
  have hh :=
    MorseCancellation.native_attaching_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.lower_regular y hy))
      x.property
  rw [d.attaching_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.belt_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (x : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.beltSphere := by
  let d := S.data p
  have hh :=
    MorseCancellation.native_belt_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.upper_regular y hy))
      x.property
  rw [d.belt_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.critical_model_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, S.field y = (S.data p).chart.descentField y := by
  let d := S.data p
  have hcenter :
    d.chart.splitChart.symm (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) =
      p.val := by
    rw [← d.chart.splitChart_center]
    exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source
  have hg :=
    S.model_germ p (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos)),
        Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos))⟩
  rw [hcenter] at hg
  exact hg

theorem MorseCancellation.hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hf : (fun x => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  change HasDerivAt (fun x => Real.sinh x / Real.cosh x) _ t at h
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem MorseCancellation.strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh (fun t => sub_pos.mpr (Real.tanh_sq_lt_one t))

theorem MorseCancellation.range_tanh : Set.range Real.tanh = Set.Ioo (-1 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  · intro hs
    obtain ⟨t, -, ht⟩ := Real.tanh_surjOn hs
    exact ⟨t, ht⟩

theorem MorseCancellation.tendsto_tanh_atTop : Filter.Tendsto Real.tanh Filter.atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_atTop_isLUB strictMono_tanh.monotone
  rw [range_tanh]
  exact isLUB_Ioo (by norm_num)

theorem MorseCancellation.tendsto_tanh_atBot : Filter.Tendsto Real.tanh Filter.atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_atBot_isGLB strictMono_tanh.monotone
  rw [range_tanh]
  exact isGLB_Ioo (by norm_num)

def MorseCancellation.cubicAxisParameter (a t : ℝ) : ℝ :=
  a * Real.tanh (a * t)

theorem MorseCancellation.hasDerivAt_cubicAxisParameter (a t : ℝ) :
    HasDerivAt (cubicAxisParameter a) (a ^ 2 - cubicAxisParameter a t ^ 2) t := by
  have h := ((hasDerivAt_tanh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a
  change HasDerivAt (cubicAxisParameter a) (a * ((1 - Real.tanh (a * t) ^ 2) * (a * 1))) t at h
  convert h using 1
  dsimp [cubicAxisParameter]
  ring

theorem MorseCancellation.cubicAxisParameter_mem {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisParameter a t ∈ Set.Ioo (-a) a := by
  have hlo := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * t)) ha
  have hhi := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * t)) ha
  constructor
  · simpa only [cubicAxisParameter, mul_neg, mul_one] using hlo
  · simpa only [cubicAxisParameter, mul_one] using hhi

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

theorem MorseCancellation.tendsto_cubicAxisParameter_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 a) := by
  have h := (tendsto_tanh_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 (a * 1)) at h
  simpa only [mul_one] using h

theorem MorseCancellation.tendsto_cubicAxisParameter_atBot {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (-a)) := by
  have h := (tendsto_tanh_atBot.comp (Filter.tendsto_id.const_mul_atBot ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (a * -1)) at h
  simpa only [mul_neg, mul_one] using h

def MorseCancellation.cubicModelOrbit {m : ℕ} (a t : ℝ) : Model m :=
  (cubicAxisParameter a t, 0)

theorem MorseCancellation.cubicModelOrbit_zero {m : ℕ} (a : ℝ) : cubicModelOrbit (m := m) a 0 = 0 := by
  simp [cubicModelOrbit, cubicAxisParameter, Real.tanh_zero]

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

theorem MorseCancellation.tendsto_cubicModelOrbit_atTop {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atTop (𝓝 (a, 0)) :=
  (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds tendsto_const_nhds

theorem MorseCancellation.tendsto_cubicModelOrbit_atBot {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atBot (𝓝 (-a, 0)) :=
  (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds tendsto_const_nhds

theorem MorseCancellation.contDiffAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ Real.artanh x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hr : ContDiffAt ℝ ∞ (fun y : ℝ => (1 + y) / (1 - y)) x :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
      (by linarith [hx.2])
  exact (hr.sqrt hp.ne').log (Real.sqrt_pos.mpr hp).ne'

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

def MorseCancellation.cubicAxisClock (a s : ℝ) : ℝ :=
  Real.artanh (s / a) / a

theorem MorseCancellation.cubicAxisClock_parameter {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisClock a (cubicAxisParameter a t) = t := by
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel_left₀ _ ha.ne', Real.artanh_tanh]

theorem MorseCancellation.cubicAxisParameter_clock {a s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Ioo (-a) a) :
    cubicAxisParameter a (cubicAxisClock a s) = s := by
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

theorem MorseCancellation.contDiffOn_cubicAxisClock {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicAxisClock a) (Set.Ioo (-a) a) := by
  intro s hs
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  exact
    (((contDiffAt_artanh hs').comp s (contDiffAt_id.div_const a)).div_const a).contDiffWithinAt

def MorseCancellation.cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : (Fin m → ℝ) × ℝ) :
    Model m :=
  (cubicAxisParameter a p.2, fun i => Real.exp (-σ i * p.2) * p.1 i)

def MorseCancellation.cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : Model m) :
    (Fin m → ℝ) × ℝ :=
  (fun i => Real.exp (σ i * cubicAxisClock a p.1) * p.2 i, cubicAxisClock a p.1)

theorem MorseCancellation.cubicFlowCylinder_left_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (p : (Fin m → ℝ) × ℝ) : cubicFlowCylinderInverse σ a (cubicFlowCylinder σ a p) = p := by
  apply Prod.ext
  · funext i
    change
      Real.exp (σ i * cubicAxisClock a (cubicAxisParameter a p.2)) *
          (Real.exp (-σ i * p.2) * p.1 i) =
        p.1 i
    rw [cubicAxisClock_parameter ha, ← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
      Real.exp_zero, one_mul]
  · exact cubicAxisClock_parameter ha p.2

theorem MorseCancellation.cubicFlowCylinder_right_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {p : Model m} (hp : p.1 ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (cubicFlowCylinderInverse σ a p) = p := by
  apply Prod.ext
  · exact cubicAxisParameter_clock ha hp
  · funext i
    change
      Real.exp (-σ i * cubicAxisClock a p.1) * (Real.exp (σ i * cubicAxisClock a p.1) * p.2 i) =
        p.2 i
    rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

theorem MorseCancellation.contDiff_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    ContDiff ℝ ∞ (cubicFlowCylinder σ a) := by
  apply ((contDiff_cubicAxisParameter a).comp contDiff_snd).prodMk
  apply contDiff_pi.mpr
  intro i
  fun_prop

theorem MorseCancellation.contDiffOn_cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ContDiffOn ℝ ∞ (cubicFlowCylinderInverse σ a) (Set.Ioo (-a) a ×ˢ Set.univ) := by
  have ht :
    ContDiffOn ℝ ∞ (fun p : Model m => cubicAxisClock a p.1) (Set.Ioo (-a) a ×ˢ Set.univ) :=
    (contDiffOn_cubicAxisClock ha).comp contDiffOn_fst (fun _ hp => hp.1)
  apply ContDiffOn.prodMk ?_ ht
  apply contDiffOn_pi.mpr
  intro i
  exact
    (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul ht)).mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn)

def MorseCancellation.cubicFlowCylinderChart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, Model m) ((Fin m → ℝ) × ℝ) (Model m) ∞
    where
  toFun := cubicFlowCylinder σ a
  invFun := cubicFlowCylinderInverse σ a
  source := Set.univ
  target := Set.Ioo (-a) a ×ˢ Set.univ
  map_source' p _ := ⟨cubicAxisParameter_mem ha p.2, Set.mem_univ _⟩
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := cubicFlowCylinder_left_inv σ ha p
  right_inv' _ hp := cubicFlowCylinder_right_inv σ ha hp.1
  open_source := isOpen_univ
  open_target := isOpen_Ioo.prod isOpen_univ
  contMDiffOn_toFun := (contDiff_cubicFlowCylinder σ a).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiffOn_cubicFlowCylinderInverse σ ha).contMDiffOn

theorem MorseCancellation.hasDerivAt_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => cubicFlowCylinder σ a (z, s))
      (cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t))) t := by
  have hz :
    HasDerivAt (fun s => fun i => Real.exp (-σ i * s) * z i)
      (fun i => -σ i * (Real.exp (-σ i * t) * z i)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hd :=
      ((Real.hasDerivAt_exp (-σ i * t)).comp t ((hasDerivAt_id t).const_mul (-σ i))).mul_const
        (z i)
    convert! hd using 1
    first
    | rfl
    | ring
  have hd := (hasDerivAt_cubicAxisParameter a t).prodMk hz
  have he :
    cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t)) =
      (a ^ 2 - cubicAxisParameter a t ^ 2, fun i => -σ i * (Real.exp (-σ i * t) * z i)) := by
    apply Prod.ext
    · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
      ring
    · rfl
  rw [he]
  exact hd

theorem MorseCancellation.cubicFlowCylinder_axis {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    cubicFlowCylinder σ a (0, t) = cubicModelOrbit a t := by
  simp only [cubicFlowCylinder, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]
  rfl

theorem MorseCancellation.cubicFlowCylinder_zero_time {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ) :
    cubicFlowCylinder σ a (z, 0) = (0, z) := by
  simp only [cubicFlowCylinder, cubicAxisParameter, MulZeroClass.mul_zero, Real.tanh_zero,
    Real.exp_zero, one_mul]

theorem MorseCancellation.monotone_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Monotone (cubicAxisParameter a) := by
  intro s t hst
  exact
    mul_le_mul_of_nonneg_left (strictMono_tanh.monotone (mul_le_mul_of_nonneg_left hst ha.le))
      ha.le

theorem MorseCancellation.cubicFlowCylinder_transverse_norm_le_max {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (z : Fin m → ℝ) {s t u : ℝ} (ht : t ∈ Set.Icc s u) :
    ‖(cubicFlowCylinder σ a (z, t)).2‖ ≤
      Max.max ‖(cubicFlowCylinder σ a (z, s)).2‖ ‖(cubicFlowCylinder σ a (z, u)).2‖ := by
  let Z (r : ℝ) : Fin m → ℝ := (cubicFlowCylinder σ a (z, r)).2
  have hcoord (r : ℝ) (i : Fin m) : ‖Z r i‖ = Real.exp (-σ i * r) * ‖z i‖ := by
    change ‖Real.exp (-σ i * r) * z i‖ = _
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg (Z s)))).mpr
  intro i
  change ‖Z t i‖ ≤ Max.max ‖Z s‖ ‖Z u‖
  by_cases hi : 0 ≤ σ i
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * s) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hi)))
          (norm_nonneg _))
      _ = ‖Z s i‖ := (hcoord s i).symm
      _ ≤ ‖Z s‖ := (norm_le_pi_norm (Z s) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_left _ _
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * u) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 (neg_nonneg.mpr (le_of_not_ge hi))))
          (norm_nonneg _))
      _ = ‖Z u i‖ := (hcoord u i).symm
      _ ≤ ‖Z u‖ := (norm_le_pi_norm (Z u) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_right _ _

theorem MorseCancellation.cubicFlowCylinder_stays_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {s t u c r : ℝ} (ht : t ∈ Set.Icc s u)
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hs' : |cubicAxisParameter a s - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, s)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hs
  have hu' : |cubicAxisParameter a u - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, u)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hu
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  constructor
  · change |cubicAxisParameter a t - c| ≤ r
    apply abs_le.mpr
    have hst := monotone_cubicAxisParameter ha ht.1
    have htu := monotone_cubicAxisParameter ha ht.2
    constructor <;> linarith [(abs_le.mp hs'.1).1, (abs_le.mp hu'.1).2]
  · exact (cubicFlowCylinder_transverse_norm_le_max σ a z ht).trans (max_le hs'.2 hu'.2)

def Smale.FiberwiseDiffeomorph.retainParameter {X P : Type*} (F : X × P → X) (p : X × P) :
    X × P :=
  (F p, p.2)

theorem Smale.FiberwiseDiffeomorph.contMDiff_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) :
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) :=
  hF.prodMk contMDiff_snd

theorem Smale.FiberwiseDiffeomorph.bijective_retainParameter {X P : Type*} {F : X × P → X}
    (hF : ∀ s, Function.Bijective (fun x => F (x, s))) : Function.Bijective (retainParameter F) :=
  by
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have hst : s = t := congrArg Prod.snd heq
    subst t
    exact Prod.ext ((hF s).1 (congrArg Prod.fst heq)) rfl
  · rintro ⟨y, s⟩
    obtain ⟨x, hx⟩ := (hF s).2 y
    exact ⟨(x, s), Prod.ext hx rfl⟩

theorem Smale.FiberwiseDiffeomorph.mfderiv_retainParameter_apply {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) (p : X × P) (v : D × P) :
    mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p v =
      (mfderiv I I (fun x => F (x, p.2)) p.1 v.1 +
          mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2 v.2,
        v.2) := by
  change mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (fun z => (F z, z.2)) p v = _
  rw [mfderiv_prodMk (hF.mdifferentiable (by simp) p) mdifferentiableAt_snd, mfderiv_snd]
  change ((mfderiv (I.prod 𝓘(ℝ, P)) I F p) v, v.2) = _
  exact Prod.ext (mfderiv_prod_eq_add_apply (v := v) (hF.mdifferentiable (by simp) p)) rfl

theorem Smale.FiberwiseDiffeomorph.isInvertible_mfderiv_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ P] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) (p : X × P) :
    (mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p).IsInvertible := by
  let A : D →L[ℝ] D := mfderiv I I (fun x => F (x, p.2)) p.1
  let B : P →L[ℝ] D := mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2
  have hA : Function.Bijective A := by
    obtain ⟨d, hd⟩ := hslice p.2
    have heq : (fun x => F (x, p.2)) = d := funext (fun x => (hd x).symm)
    change Function.Bijective (mfderiv I I (fun x => F (x, p.2)) p.1)
    rw [heq]
    exact (d.mfderivToContinuousLinearEquiv (by simp) p.1).bijective
  let L : (D × P) →L[ℝ] (D × P) := mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p
  have hL (v : D × P) : L v = (A v.1 + B v.2, v.2) := mfderiv_retainParameter_apply hF p v
  have hbij : Function.Bijective L := by
    constructor
    · intro u v huv
      have hs : u.2 = v.2 := by simpa only [hL] using congrArg Prod.snd huv
      have hx : A u.1 + B u.2 = A v.1 + B v.2 := by simpa only [hL] using congrArg Prod.fst huv
      rw [hs] at hx
      exact Prod.ext (hA.1 (add_right_cancel hx)) hs
    · intro v
      obtain ⟨x, hx⟩ := hA.2 (v.1 - B v.2)
      refine ⟨(x, v.2), ?_⟩
      rw [hL, hx, sub_add_cancel]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

def Smale.FiberwiseDiffeomorph.diffeomorph {D H X P : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace H]
    {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ P] [I.Boundaryless] [IsManifold I ∞ X] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) :
    Diffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (X × P) (X × P) ∞ := by
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) := by
    intro p
    exact
      Smale.isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ p)
        (contMDiff_retainParameter hF).contMDiffOn
        (isInvertible_mfderiv_retainParameter hF hslice p)
  apply hlocal.diffeomorphOfBijective
  apply bijective_retainParameter
  intro s
  obtain ⟨d, hd⟩ := hslice s
  have heq : (fun x => F (x, s)) = d := funext (fun x => (hd x).symm)
  rw [heq]
  exact d.bijective

def Smale.PartialChart.vectorProduct (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Diffeomorph 𝓘(ℝ, E × F) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (E × F) (E × F) ∞
    where
  toEquiv := Equiv.refl (E × F)
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

def Smale.PartialChart.prod {E₁ E₂ F₁ F₂ H₁ H₂ G₁ G₂ X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace H₁]
    [TopologicalSpace H₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {J₁ : ModelWithCorners ℝ F₁ G₁} {J₂ : ModelWithCorners ℝ F₂ G₂} [TopologicalSpace X₁]
    [ChartedSpace H₁ X₁] [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [TopologicalSpace Y₁]
    [ChartedSpace G₁ Y₁] [TopologicalSpace Y₂] [ChartedSpace G₂ Y₂]
    (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞) (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) :
    PartialDiffeomorph (I₁.prod I₂) (J₁.prod J₂) (X₁ × X₂) (Y₁ × Y₂) ∞
    where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.prodMap Ψ.contMDiffOn_toFun
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.prodMap Ψ.contMDiffOn_invFun

theorem Degree.FlowSuspension.exists_isotopy_suspension_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A : ℝ × E → E}
    (hA : ContDiff ℝ ∞ A)
    (hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (t, x)) :
    ∃ Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞, ∀ p, Ψ p = (A (p.2, p.1), p.2) :=
  by
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun p : E × ℝ => A (p.2, p.1)) :=
    hA.contMDiff.comp (contMDiff_snd.prodMk_space contMDiff_fst)
  let D := Smale.FiberwiseDiffeomorph.diffeomorph hF hslice
  let V := Smale.PartialChart.vectorProduct E ℝ
  exact ⟨(V.trans D).trans V.symm, fun p => rfl⟩

def Degree.FlowSuspension.suspensionFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) : Flow ℝ (E × ℝ)
    where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' := by
    apply Ψ.continuous.comp
    exact
      (Ψ.symm.continuous.comp continuous_snd).fst.prodMk
        ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst)
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t
    p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

theorem Degree.FlowSuspension.suspensionFlow_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (t : ℝ)
    (p : E × ℝ) : suspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

theorem Degree.FlowSuspension.suspensionFlow_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : E × ℝ) : (suspensionFlow Ψ t p).2 = p.2 + t := by
  have hinv : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = _
  rw [hheight, hinv]

theorem Degree.FlowSuspension.suspensionFlow_endpoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : ℝ × E → E} (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (hA0 : ∀ x, A (0, x) = x) (x : E) :
    suspensionFlow Ψ 1 (x, 0) = (A (1, x), 1) := by
  have hstart : Ψ (x, (0 : ℝ)) = (x, 0) := by rw [hΨ, hA0]
  rw [← hstart, suspensionFlow_chart, zero_add, hΨ]

def Degree.FlowSuspension.suspensionField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) : E × ℝ :=
  fderiv ℝ Ψ (Ψ.symm p) (0, 1)

theorem Degree.FlowSuspension.contDiff_suspensionField {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) :
    ContDiff ℝ ∞ (suspensionField Ψ) := by
  have hΨ : ContDiff ℝ ∞ (Ψ : (E × ℝ) → E × ℝ) := Ψ.contMDiff.contDiff
  have hΨinv : ContDiff ℝ ∞ (Ψ.symm : (E × ℝ) → E × ℝ) := Ψ.symm.contMDiff.contDiff
  exact ((hΨ.fderiv_right (by simp)).comp hΨinv).clm_apply contDiff_const

theorem Degree.FlowSuspension.hasDerivAt_suspensionFlow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ (suspensionFlow Ψ t p)) t := by
  have hb : HasDerivAt (fun s : ℝ => ((Ψ.symm p).1, (Ψ.symm p).2 + s)) (0, 1) t :=
    (hasDerivAt_const t (Ψ.symm p).1).prodMk ((hasDerivAt_id t).const_add (Ψ.symm p).2)
  have hd :=
    (Ψ.contMDiff.contDiff.differentiable (by simp)
          ((Ψ.symm p).1, (Ψ.symm p).2 + t)).hasFDerivAt.comp_hasDerivAt
      t hb
  change
    HasDerivAt (fun s => Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + s))
      (fderiv ℝ Ψ (Ψ.symm (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t))) (0, 1)) t
  rw [Ψ.symm_apply_apply]
  exact hd

theorem Degree.FlowSuspension.hasDerivAt_suspensionFlow_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ p) 0 := by
  simpa only [(suspensionFlow Ψ).map_zero_apply] using hasDerivAt_suspensionFlow Ψ p 0

theorem Degree.FlowSuspension.suspensionField_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : E × ℝ) : (suspensionField Ψ p).2 = 1 := by
  have hd : HasDerivAt (fun t => (suspensionFlow Ψ t p).2) (suspensionField Ψ p).2 0 :=
    (hasDerivAt_suspensionFlow_zero Ψ p).snd
  have heq : (fun t => (suspensionFlow Ψ t p).2) = fun t => p.2 + t :=
    funext (fun t => suspensionFlow_height Ψ hheight t p)
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_id (0 : ℝ)).const_add p.2)

theorem Degree.FlowSuspension.suspensionField_eq_vertical_of_stationary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (p : E × ℝ)
    (hstationary : ∀ᶠ s in 𝓝 p.2, ∀ x, A (s, x) = A (p.2, x)) : suspensionField Ψ p = (0, 1) := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have hqheight : q.2 = p.2 := by
    have hh := congrArg Prod.snd hq
    rw [hΨ] at hh
    exact hh
  have hqfirst : A (p.2, q.1) = p.1 := by
    have hh := congrArg Prod.fst hq
    rw [hΨ] at hh
    change A (q.2, q.1) = p.1 at hh
    rwa [hqheight] at hh
  have ht : Filter.Tendsto (fun t : ℝ => p.2 + t) (𝓝 0) (𝓝 p.2) := by
    have hc : Continuous (fun t : ℝ => p.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq : (fun t => suspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t => (p.1, p.2 + t)) := by
    filter_upwards [ht.eventually hstationary] with t hts
    change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
    rw [hΨ, hqheight, hts q.1, hqfirst]
  have hv : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  exact ((hasDerivAt_suspensionFlow_zero Ψ p).congr_of_eventuallyEq heq.symm).unique hv

theorem Degree.FlowSuspension.suspensionFlow_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) (t : ℝ) : suspensionFlow Ψ t p = (p.1, p.2 + t) := by
  have hΨp : Ψ p = p := by rw [hΨ, hfix _ _ hp]
  have hinv : Ψ.symm p = p := by
    have hh := Ψ.symm_apply_apply p
    rwa [hΨp] at hh
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = _
  rw [hinv, hΨ, hfix _ _ hp]

theorem Degree.FlowSuspension.suspensionField_eq_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) : suspensionField Ψ p = (0, 1) := by
  have heq : (fun t => suspensionFlow Ψ t p) = fun t => (p.1, p.2 + t) :=
    funext (fun t => suspensionFlow_vertical_off_support Ψ hΨ hfix hp t)
  have hd := hasDerivAt_suspensionFlow_zero Ψ p
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2))

theorem Degree.FlowSuspension.hasCompactSupport_suspensionField_sub_vertical {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hK : IsCompact K)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {a b : ℝ}
    (hstationary : ∀ s ∉ Set.Icc a b, ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x)) :
    HasCompactSupport (fun p => suspensionField Ψ p - (0, 1)) := by
  apply
    HasCompactSupport.intro (hK.prod (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc a b)))
  intro p hp
  have hv : suspensionField Ψ p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Set.Icc a b := fun h => hp ⟨hx, h⟩
      exact suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary _ ht)
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  rw [hv, sub_self]

theorem Smale.SupportedDiffeomorph.contMDiff_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    (hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun p : ℝ × Y => extendMap Φ (fun x => A (p.1, x)) p.2) := by
  intro p
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource p.1 (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

theorem Smale.SupportedDiffeomorph.contMDiffAt_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P × X → X} (hA : ContMDiff (𝓘(ℝ, P).prod I) I ∞ A) {K : Set X} (hK : IsCompact K)
    (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : P × Y}
    (hsource : Set.MapsTo (fun x => A (p.1, x)) Φ.source Φ.source) :
    ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ (fun q : P × Y => extendMap Φ (fun x => A (q.1, x)) q.2) p :=
  by
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

def Smale.SupportedDiffeomorph.bumpFamily {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (p : E × M) : M :=
  extendMap Φ (fun x => x + β x • p.1) p.2

theorem Smale.SupportedDiffeomorph.bumpFamily_zero {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (y : M) : bumpFamily Φ β (0, y) = y := by
  have heq : (fun x : E => x + β x • (0 : E)) = id := by funext x; simp
  change extendMap Φ (fun x => x + β x • (0 : E)) y = y
  rw [heq]
  exact extendMap_id Φ y

theorem Smale.SupportedDiffeomorph.bumpFamily_chart {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {x : E} (hx : x ∈ Φ.source) :
    bumpFamily Φ β (a, Φ x) = Φ (x + β x • a) :=
  extendMap_chart Φ _ hx

theorem Smale.SupportedDiffeomorph.bumpFamily_mem_target {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    bumpFamily Φ β (a, y) ∈ Φ.target :=
  extendMap_mem_target Φ hsource hy

theorem Smale.SupportedDiffeomorph.bumpFamily_coordinates {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    Φ.symm (bumpFamily Φ β (a, y)) = Φ.symm y + β (Φ.symm y) • a := by
  change Φ.symm (extendMap Φ (fun x => x + β x • a) y) = _
  rw [extendMap_of_mem Φ _ hy]
  exact Φ.left_inv' (hsource (Φ.map_target' hy))

theorem Smale.SupportedDiffeomorph.bumpFamily_fixed_outside {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {y : M}
    (hy : y ∉ Φ '' tsupport β) : bumpFamily Φ β (a, y) = y := by
  apply extendMap_eq_of_notMem_image Φ (K := tsupport β) _ hy
  intro x hx
  have hzero : β x = 0 := by
    by_contra hn
    exact hx (subset_tsupport β hn)
  simp only [hzero, zero_smul, add_zero]

theorem Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ a : E, ‖a‖ < ε → ∃ D : Diffeomorph J J M M ∞, ∀ y, D y = bumpFamily Φ β (a, y)) ∧
          (∀ p : E × M, ‖p.1‖ < ε → ContMDiffAt (𝓘(ℝ, E).prod J) J ∞ (bumpFamily Φ β) p) ∧
            ∀ a : E, ‖a‖ < ε → Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source := by
  obtain ⟨ε, hε, hsmall⟩ := Smale.SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let A : E × E → E := fun p => p.2 + β p.2 • p.1
  have hA : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hβ.contMDiff.comp contMDiff_snd).smul contMDiff_fst)
  have hfix : ∀ a x, x ∉ tsupport β → A (a, x) = x := by
    intro a x hx
    have hzero : β x = 0 := by
      by_contra hn
      exact hx (subset_tsupport β hn)
    simp only [A, hzero, zero_smul, add_zero]
  have hsource (a : E) (ha : ‖a‖ < ε) : Set.MapsTo (fun x => A (a, x)) Φ.source Φ.source := by
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    have heq : (fun x => A (a, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  refine ⟨ε, hε, ?_, ?_, hsource⟩
  · intro a ha
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ d y = extendMap Φ (fun x => x + β x • a) y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext hd)
  · intro p hp
    exact contMDiffAt_extendFamily Φ hA hcompact.isCompact hsupport hfix (hsource p.1 hp)

theorem Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {X : Type*}
    [TopologicalSpace X] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) {f : X → M} (hf : Continuous f) {C : Set X}
    (hC : IsCompact C) {O : Set M} (hO : IsOpen O) (hmap : Set.MapsTo f C O) :
    ∀ᶠ a in 𝓝 (0 : E), Set.MapsTo (fun x => bumpFamily Φ β (a, f x)) C O := by
  obtain ⟨δ, hδ, -, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  apply hC.eventually_forall_of_forall_eventually
  intro x hx
  have hpair : ContinuousAt (fun p : E × X => (p.1, f p.2)) (0, x) :=
    (continuous_fst.prodMk (hf.comp continuous_snd)).continuousAt
  have hbase : ContinuousAt (bumpFamily Φ β) (0, f x) :=
    (hsmooth (0, f x) (by simpa only [norm_zero] using hδ)).continuousAt
  have hfamily : ContinuousAt (fun p : E × X => bumpFamily Φ β (p.1, f p.2)) (0, x) :=
    ContinuousAt.comp (g := bumpFamily Φ β) (f := fun p : E × X => (p.1, f p.2)) hbase hpair
  apply hfamily.preimage_mem_nhds
  apply hO.mem_nhds
  rw [bumpFamily_zero]
  exact hmap hx

theorem Smale.SupportedDiffeomorph.exists_small_supported_bump_isotopy {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ Φ '' tsupport β → A (t, y) = y) ∧
                      ∀ x ∈ Φ.source, A (1, Φ x) = Φ (x + β x • a) := by
  obtain ⟨ε, hε, hsmall⟩ := Smale.SmallPerturbation.exists_radius_bumpTranslation hs hcompact
  refine ⟨ε, hε, ?_⟩
  intro a ha
  let B : ℝ × E → E := fun p => p.2 + β p.2 • (Real.smoothTransition p.1 • a)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B :=
    contMDiff_snd.add
      ((hs.contMDiff.comp contMDiff_snd).smul ((hθ.comp contMDiff_fst).smul contMDiff_const))
  have hmodel :
    ∀ t : ℝ,
      ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ x, d x = B (t, x)) ∧ ∀ x ∉ tsupport β, d x = x := by
    intro t
    have hnorm : ‖Real.smoothTransition t • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact mul_le_of_le_one_left (norm_nonneg a) (Real.smoothTransition.le_one t)
    exact hsmall (Real.smoothTransition t • a) (hnorm.trans_lt ha)
  have hfix : ∀ t x, x ∉ tsupport β → B (t, x) = x := by
    intro t x hx
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    exact (hd x).symm.trans (hdfix x hx)
  have hsource : ∀ t, Set.MapsTo (fun x => B (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    have heq : (fun x => B (t, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  let A : ℝ × M → M := fun p => extendMap Φ (fun x => B (p.1, x)) p.2
  refine ⟨A, contMDiff_extendFamily Φ hB hcompact.isCompact hsupport hfix hsource, ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun x => B (0, x)) = id := by
      funext x
      simp only [B, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero, id_eq]
    change extendMap Φ (fun x => B (0, x)) y = y
    rw [hzero]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ (fun x => B (t, x)) y = extendMap Φ d y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext (fun x => (hd x).symm))
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro x hx
    change extendMap Φ (fun y => B (1, y)) (Φ x) = _
    rw [extendMap_chart Φ (fun y => B (1, y)) hx]
    simp only [B, Real.smoothTransition.one, one_smul]

def Smale.SupportedDiffeomorph.IsotopicToIdentity {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (e : Diffeomorph J J M M ∞) : Prop :=
  ∃ A : ℝ × M → M,
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
      (∀ y, A (0, y) = y) ∧
        (∀ y, A (1, y) = e y) ∧ ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y

theorem Smale.SupportedDiffeomorph.isotopicToIdentity_refl {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] : IsotopicToIdentity (Diffeomorph.refl J M ∞) := by
  refine ⟨Prod.snd, contMDiff_snd, fun _ => rfl, fun _ => rfl, ?_⟩
  exact fun _ => ⟨Diffeomorph.refl J M ∞, fun _ => rfl⟩

theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.trans {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e d : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e)
    (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity (e.trans d) := by
  obtain ⟨A, hA, hA₀, hA₁, hAd⟩ := he
  obtain ⟨B, hB, hB₀, hB₁, hBd⟩ := hd
  refine ⟨fun p => B (p.1, A p), hB.comp (contMDiff_fst.prodMk hA), ?_, ?_, ?_⟩
  · intro y
    change B (0, A (0, y)) = y
    rw [hA₀, hB₀]
  · intro y
    change B (1, A (1, y)) = d (e y)
    rw [hA₁, hB₁]
  · intro t
    obtain ⟨e', he'⟩ := hAd t
    obtain ⟨d', hd'⟩ := hBd t
    refine ⟨e'.trans d', ?_⟩
    intro y
    change B (t, A (t, y)) = d' (e' y)
    rw [he', hd']

theorem Smale.SupportedDiffeomorph.exists_radius_bumpFamily_isotopy {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = bumpFamily Φ β (a, y)) → IsotopicToIdentity e := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  refine ⟨A, hA, hzero, ?_, hdiff⟩
  intro y
  rw [he]
  by_cases hy : y ∈ Φ.target
  · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
    have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
    rw [hpoint] at hh
    change A (1, y) = extendMap Φ (fun x => x + β x • a) y
    rw [extendMap_of_mem Φ _ hy]
    exact hh
  · have hnot : y ∉ Φ '' tsupport β := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hsupport hx))
    rw [hfix 1 y hnot, bumpFamily_fixed_outside Φ β a hnot]

structure Smale.SupportedDiffeomorph.SupportedRelativeIsotopy {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (e : Diffeomorph J J M M ∞) (K S : Set M) where
  family : ℝ × M → M
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ x, family (0, x) = x
  one : ∀ x, family (1, x) = e x
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ x, d x = family (t, x)
  fixedOutside : ∀ t x, x ∉ K → family (t, x) = x
  fixedOn : ∀ t x, x ∈ S → family (t, x) = x

theorem Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.isotopicToIdentity {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity e := by
  refine ⟨A.family, A.smooth, A.zero, A.one, ?_⟩
  intro t
  obtain ⟨d, hd⟩ := A.slices t
  exact ⟨d, fun x => (hd x).symm⟩

theorem Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_outside {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∉ K) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOutside 1 x hx)

theorem Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_on {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∈ S) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOn 1 x hx)

structure Degree.FlowSuspension.SuspensionCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E) (W : (E × ℝ) → E × ℝ)
    (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = suspensionField chart
  flow_eq : F = suspensionFlow chart
  height : ∀ p, (chart p).2 = p.2
  base_iff : ∀ U : Set E, K ⊆ U → ∀ p, (chart p).1 ∈ U ↔ p.1 ∈ U
  lower : ∀ p, p.2 ≤ 0 → chart p = p
  upper : ∀ p, 1 ≤ p.2 → chart p = (D p.1, p.2)

theorem Degree.FlowSuspension.exists_compact_isotopy_suspension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {K S : Set E} (hK : IsCompact K)
    (I : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)),
      ContDiff ℝ ∞ W ∧
        (∀ p, (W p).2 = 1) ∧
          HasCompactSupport (fun p => W p - (0, 1)) ∧
            tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) ∧
              (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
                (∀ x, F 1 (x, 0) = (D x, 1)) ∧
                  (∀ t p, (F t p).2 = p.2 + t) ∧
                    (∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                      (∀ x ∈ S, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                        Nonempty (SuspensionCoordinates D K W F) := by
  let τ : ℝ → ℝ := fun s => Real.smoothTransition (3 * s - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hτlower (s : ℝ) (hs : s ≤ 1 / 3) : τ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hτupper (s : ℝ) (hs : 2 / 3 ≤ s) : τ s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : ℝ × E → E := fun p => I.family (τ p.1, p.2)
  have hInorm : ContDiff ℝ ∞ I.family :=
    (I.smooth.comp (Smale.PartialChart.vectorProduct ℝ E).contMDiff).contDiff
  have hA : ContDiff ℝ ∞ A := hInorm.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd)
  have hslice (s : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (s, x) :=
    I.slices (τ s)
  have hA0 (x : E) : A (0, x) = x := by
    change I.family (τ 0, x) = x
    rw [hτlower 0 (by norm_num)]
    exact I.zero x
  have hA1 (x : E) : A (1, x) = D x := by
    change I.family (τ 1, x) = D x
    rw [hτupper 1 (by norm_num)]
    exact I.one x
  have hfix (s : ℝ) (x : E) (hx : x ∉ K) : A (s, x) = x := I.fixedOutside (τ s) x hx
  have hstationary (s : ℝ) (hs : s ∉ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x) := by
    by_cases hlo : s < 1 / 3
    · filter_upwards [eventually_lt_nhds hlo] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτlower r hr.le, hτlower s hlo.le]
    · have hhi : 2 / 3 < s := lt_of_not_ge (fun h => hs ⟨le_of_not_gt hlo, h⟩)
      filter_upwards [eventually_gt_nhds hhi] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτupper r hr.le, hτupper s hhi.le]
  obtain ⟨Ψ, hΨ⟩ := exists_isotopy_suspension_diffeomorph hA hslice
  let W := suspensionField Ψ
  let F := suspensionFlow Ψ
  have hvertical (p : E × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) : W p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · exact
        suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary p.2 (fun h => hp ⟨hx, h⟩))
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  have hsupp : tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_Icc)
    intro p hp
    by_contra hout
    apply hp
    change W p - (0, 1) = 0
    rw [hvertical p hout, sub_self]
  have hcoords : SuspensionCoordinates D K W F := by
    refine ⟨Ψ, rfl, rfl, fun p => by rw [hΨ], ?_, ?_, ?_⟩
    · intro U hKU p
      have hfixU (z : E × ℝ) (hz : z ∉ U ×ˢ Set.univ) : Ψ z = z := by
        have hn : z.1 ∉ K := fun h => hz ⟨hKU h, Set.mem_univ _⟩
        rw [hΨ, hfix z.2 z.1 hn]
      have hmaps := Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.toEquiv hfixU
      have hmapsInv :=
        Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.symm.toEquiv
          (Smale.SupportedDiffeomorph.inverse_fixed_outside Ψ.toEquiv hfixU)
      constructor
      · intro hp
        have hh := hmapsInv ⟨hp, Set.mem_univ (Ψ p).2⟩
        have hh' : (Ψ.symm (Ψ p)).1 ∈ U := hh.1
        simpa only [Ψ.symm_apply_apply] using hh'
      · intro hp
        exact (hmaps ⟨hp, Set.mem_univ p.2⟩).1
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = p
      rw [hτlower p.2 (by linarith), I.zero]
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = (D p.1, p.2)
      rw [hτupper p.2 (by linarith), I.one]
  refine
    ⟨W, F, contDiff_suspensionField Ψ, suspensionField_height Ψ (fun p => by rw [hΨ]),
      hasCompactSupport_suspensionField_sub_vertical Ψ hΨ hK hfix hstationary, hsupp,
      hasDerivAt_suspensionFlow Ψ, ?_, suspensionFlow_height Ψ (fun p => by rw [hΨ]), ?_, ?_,
      ⟨hcoords⟩⟩
  · intro x
    exact
      (suspensionFlow_endpoint Ψ hΨ hA0 x).trans (congrArg (fun y : E => (y, (1 : ℝ))) (hA1 x))
  · intro x hx s t
    exact suspensionFlow_vertical_off_support Ψ hΨ hfix (p := (x, s)) hx t
  · intro x hx s t
    have hΨfix (r : ℝ) : Ψ (x, r) = (x, r) := by
      rw [hΨ]
      change (I.family (τ r, x), r) = (x, r)
      rw [I.fixedOn (τ r) x hx]
    change suspensionFlow Ψ t (x, s) = (x, s + t)
    rw [← hΨfix s, suspensionFlow_chart, hΨfix]

def Degree.LocalFieldReplacement.replace {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) : TangentSpace 𝓘(ℝ, E) x := by
  classical exact if x ∈ Φ.target then W x else V x

theorem Degree.LocalFieldReplacement.replace_of_mem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∈ Φ.target) :
    replace Φ V W x = W x := by simp [replace, hx]

theorem Degree.LocalFieldReplacement.replace_of_notMem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∉ Φ.target) :
    replace Φ V W x = V x := by simp [replace, hx]

theorem Degree.LocalFieldReplacement.exists_smooth_field_replacement {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞) [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
        Φ.target)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∈ Φ.target, x ∉ Φ '' K → W x = V x) (hreg : ∀ x ∈ Φ.target, W x ≠ 0) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Φ.target, V' x = W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0 ∧ x ∉ Φ.target) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let V' := replace Φ V W
  have hclosed : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  have hoff (x : M) (hx : x ∉ Φ '' K) : ∀ᶠ y in 𝓝 x, V' y = V y := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    by_cases hyt : y ∈ Φ.target
    · exact (replace_of_mem Φ V W hyt).trans (hfix y hyt hy)
    · exact replace_of_notMem Φ V W hyt
  have hsmooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro x
    by_cases hx : x ∈ Φ.target
    · apply (hW.contMDiffAt (Φ.open_target.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hx] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) (replace_of_mem Φ V W hy)
    · have hnot : x ∉ Φ '' K := by
        rintro ⟨p, hp, rfl⟩
        exact hx (Φ.map_source' (hKΦ hp))
      apply hV.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [hoff x hnot] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy
  refine ⟨V', hsmooth, fun x hx => replace_of_mem Φ V W hx, ?_, hoff⟩
  intro x
  by_cases hx : x ∈ Φ.target
  · rw [show V' x = W x from replace_of_mem Φ V W hx]
    simp only [hreg x hx, hx, not_true_eq_false, and_false]
  · rw [show V' x = V x from replace_of_notMem Φ V W hx]
    simp only [hx, not_false_eq_true, and_true]

theorem Smale.exists_compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : E → ℝ,
      ContDiff ℝ ∞ η ∧
        HasCompactSupport η ∧
          tsupport η ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, η x = 1) ∧ ∀ x, η x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKL (n := ⊤)
  have hsupp : tsupport (η : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (hηzero x hxL)
  exact
    ⟨η, η.contMDiff.contDiff, HasCompactSupport.intro hL hηzero, hsupp.trans hLU, hηone, hηrange⟩

def MorseCancellation.cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (φ : Model m → ℝ) (p : Model m) :
    Model m :=
  (a ^ 2 - p.1 ^ 2 - 2 * a ^ 2 * φ p, fun i => -σ i * p.2 i)

theorem MorseCancellation.contDiff_cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (cancelledDescent σ a φ) := by
  unfold cancelledDescent
  fun_prop

theorem MorseCancellation.cancelledDescent_axis_negative {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) (s : ℝ) :
    (cancelledDescent σ a φ (s, 0)).1 < 0 := by
  change a ^ 2 - s ^ 2 - 2 * a ^ 2 * φ (s, 0) < 0
  by_cases hs : s ∈ Set.Icc (-a) a
  · rw [hone s hs]
    nlinarith [sq_pos_of_pos ha, sq_nonneg s]
  · have hsq : a ^ 2 < s ^ 2 := by
      by_cases hl : -a ≤ s
      · have hr : a < s := lt_of_not_ge (fun h => hs ⟨hl, h⟩)
        nlinarith
      · have hh : s < -a := lt_of_not_ge hl
        nlinarith
    have hnonneg : 0 ≤ 2 * a ^ 2 * φ (s, 0) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) (hφ (s, 0))
    linarith

theorem MorseCancellation.cancelledDescent_ne_zero {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    (p : Model m) : cancelledDescent σ a φ p ≠ 0 := by
  intro hp
  have hz : p.2 = 0 := by
    funext i
    have hi := congrArg (fun q : Model m => q.2 i) hp
    change -σ i * p.2 i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (hσ i))
  have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
  have hx := congrArg Prod.fst hp
  rw [he] at hx
  exact (cancelledDescent_axis_negative σ ha hφ hone p.1).ne hx

theorem MorseCancellation.cancelledDescent_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    {φ : Model m → ℝ} {p : Model m} (hp : p ∉ tsupport φ) :
    cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  apply Prod.ext
  · simp only [cancelledDescent, cubicDescent, hq, Pi.zero_apply, MulZeroClass.mul_zero, sub_zero]
    ring
  · rfl

theorem MorseCancellation.exists_cubic_field_cancellation {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {U : Set (Model m)} (hU : IsOpen U)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ U) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ U ∧
            (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
              (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                ContDiff ℝ ∞ (cancelledDescent σ a φ) ∧
                  (∀ p, cancelledDescent σ a φ p ≠ 0) ∧
                    ∀ p ∉ tsupport φ, cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  obtain ⟨φ, hφ, hc, hsupp, hone, hrange⟩ :=
    Smale.exists_compact_smooth_cutoff (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hU
      haxis
  have hone' (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : φ (s, (0 : Fin m → ℝ)) = 1 := by
    have hn : ∀ᶠ p in 𝓝 (s, (0 : Fin m → ℝ)), φ p = 1 :=
      (nhds_le_nhdsSet (show (s, (0 : Fin m → ℝ)) ∈ Set.Icc (-a) a ×ˢ {0} from ⟨hs, rfl⟩)) hone
    exact hn.self_of_nhds
  exact
    ⟨φ, hφ, hc, hsupp, hrange, hone', contDiff_cancelledDescent σ a hφ,
      cancelledDescent_ne_zero σ hσ ha (fun p => (hrange p).1) hone', fun p hp =>
      cancelledDescent_germ_off_support σ a hp⟩

theorem MorseCancellation.partialChartField_zero_iff {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D) {x : M}
    (hx : x ∈ Φ.target) :
    Smale.FlowConstruction.partialChartField Φ.symm W x = 0 ↔ W (Φ.symm x) = 0 := by
  rw [Smale.FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W hx]
  have hl : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ Φ (Φ.symm x) :=
    ⟨Φ, Φ.map_target' hx, fun _ _ => rfl⟩
  let A := hl.mfderivToContinuousLinearEquiv (by simp)
  let B : D ≃L[ℝ] TangentSpace 𝓘(ℝ, D) (Φ.symm x) :=
    (NormedSpace.fromTangentSpace (Φ.symm x)).symm
  change A (B (W (Φ.symm x))) = 0 ↔ W (Φ.symm x) = 0
  constructor
  · intro h
    have hb : B (W (Φ.symm x)) = 0 := A.injective (h.trans (map_zero A).symm)
    exact B.injective (hb.trans (map_zero B).symm)
  · intro h
    rw [h, map_zero, map_zero]

theorem MorseCancellation.cubicDescent_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (a : ℝ)
    (p : Model m) : cubicDescent σ (-(a ^ 2)) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [← negative_parameter_critical_iff σ hσ a p]
  constructor
  · intro hp
    by_contra hn
    have hh := cubicDescent_strict σ hn
    rw [hp, map_zero] at hh
    exact lt_irrefl _ hh
  · exact cubicDescent_zero_of_critical σ

theorem MorseCancellation.exists_native_cubic_field_cancellation_in {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ)
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) {N : Set M}
    (hN : IsOpen N) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ Φ.source ∧
            Φ '' tsupport φ ⊆ N ∧
              (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
                (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                  ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ x ∈ Φ.target,
                          V' x =
                            Smale.FlowConstruction.partialChartField Φ.symm
                              (cancelledDescent σ a φ) x) ∧
                        (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
                          ∀ x ∉ Φ '' tsupport φ, ∀ᶠ y in 𝓝 x, V' y = V y := by
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' N) := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hN
  have haxis' : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∩ Φ ⁻¹' N := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact ⟨haxis ⟨hs, rfl⟩, haxisN s hs⟩
  obtain ⟨φ, hφ, hc, hsupp', hrange, hone, hD, hnonzero, hoff⟩ :=
    exists_cubic_field_cancellation σ hσ ha hopen haxis'
  have hsupp : tsupport φ ⊆ Φ.source := fun _ hx => (hsupp' hx).1
  have hsuppN : Φ '' tsupport φ ⊆ N := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsupp' hz).2
  let W := Smale.FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ)
  have hW :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
      Φ.target :=
    Smale.FlowConstruction.contMDiffOn_partialChartField Φ.symm hD
  have hfix (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' tsupport φ) : W x = V x := by
    have hinv : Φ.symm x ∉ tsupport φ := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    have he := (hoff (Φ.symm x) hinv).eq_of_nhds
    rw [hmodel x hx]
    unfold W nativeCubicDescent Smale.FlowConstruction.partialChartField
    simp only [VectorField.mpullback_apply, he]
  have hreg (x : M) (hx : x ∈ Φ.target) : W x ≠ 0 := by
    intro hz
    exact hnonzero _ ((partialChartField_zero_iff Φ (cancelledDescent σ a φ) hx).mp hz)
  obtain ⟨V', hV', heq, hzero, hkeep⟩ :=
    Degree.LocalFieldReplacement.exists_smooth_field_replacement Φ V W hV hW hc hsupp hfix hreg
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  refine ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, ?_, hkeep⟩
  intro x
  rw [hzero x]
  constructor
  · rintro ⟨hx, hout⟩
    exact ⟨hx, fun he => hout (he ▸ Φ.map_source' hp), fun he => hout (he ▸ Φ.map_source' hq)⟩
  · rintro ⟨hx, hxp, hxq⟩
    refine ⟨hx, ?_⟩
    intro hxt
    have hz : Smale.FlowConstruction.partialChartField Φ.symm (cubicDescent σ (-(a ^ 2))) x = 0 :=
      (hmodel x hxt).symm.trans hx
    have hd := (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) hxt).mp hz
    rcases (cubicDescent_zero_iff σ hσ a (Φ.symm x)).mp hd with hh | hh
    · exact hxp ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))
    · exact hxq ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))

theorem Degree.FlowSuspension.exists_native_vertical_field_replacement {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [T2Space M]
    [IsManifold 𝓘(ℝ, B) ∞ M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = Smale.FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    {W : (E × ℝ) → E × ℝ} (hW : ContDiff ℝ ∞ W) (hWheight : ∀ p, (W p).2 = 1) {K : Set (E × ℝ)}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ p ∉ K, W p = (0, 1)) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, B) x,
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
        (∀ x ∈ Φ.target, V' x = Smale.FlowConstruction.partialChartField Φ.symm W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let Wn := Smale.FlowConstruction.partialChartField Φ.symm W
  have hWn :
    ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, Wn x⟩ : TangentBundle 𝓘(ℝ, B) M))
      Φ.target :=
    Smale.FlowConstruction.contMDiffOn_partialChartField Φ.symm hW
  have hreg (x : M) (hx : x ∈ Φ.target) : Wn x ≠ 0 := by
    intro hz
    have hWzero := (MorseCancellation.partialChartField_zero_iff Φ W hx).mp hz
    have hh := congrArg Prod.snd hWzero
    rw [hWheight] at hh
    exact one_ne_zero hh
  have hregV (x : M) (hx : x ∈ Φ.target) : V x ≠ 0 := by
    rw [hmodel x hx]
    intro hz
    have hh := (MorseCancellation.partialChartField_zero_iff Φ (fun _ : E × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hkeep (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' K) : Wn x = V x := by
    have hz : Φ.symm x ∉ K := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    rw [hmodel x hx]
    change Smale.FlowConstruction.partialChartField Φ.symm W x = _
    unfold Smale.FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix _ hz]
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    Degree.LocalFieldReplacement.exists_smooth_field_replacement Φ V Wn hV hWn hK hKΦ hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro x
  exact (hzeros x).trans ⟨And.left, fun hx => ⟨hx, fun ht => hregV x ht hx⟩⟩

theorem Degree.FlowSuspension.mvfderiv_native_height_field {E B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace M]
    [ChartedSpace B M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ} (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (W : (E × ℝ) → E × ℝ) {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (Smale.FlowConstruction.partialChartField Φ.symm W x) =
      -(W (Φ.symm x)).2 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target' hx
  have heq : (f ∘ Φ) =ᶠ[𝓝 q] (fun p : E × ℝ => b - p.2) := by
    filter_upwards [Φ.open_source.mem_nhds hq] with p hp
    exact hheight p hp
  have hd : fderiv ℝ (f ∘ Φ) q = fderiv ℝ (fun p : E × ℝ => b - p.2) q := heq.fderiv_eq
  rw [Smale.FlowConstruction.mvfderiv_partialChartField hf Φ.symm W hx]
  change fderiv ℝ (f ∘ Φ) q (W q) = -(W q).2
  rw [hd]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) b q).sub (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hh' :
    fderiv ℝ (fun p : E × ℝ => b - p.2) q =
      (0 : (E × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ :=
    hh.fderiv
  rw [hh']
  simp

theorem Degree.FlowSuspension.native_flow_segment_endpoints {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : F (b - a) (γ a) = γ b := by
  let c := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by constructor <;> dsimp [c] <;> linarith
  have hη : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have hh := (hcurve (γ c)).comp_add (-c)
    simpa only [sub_eq_add_neg, Function.comp_def] using hh
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hη.isMIntegralCurveOn _)
      (by simp)
  have heqclosed : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Icc a b) :=
    heq.of_subset_closure hγcont hη.continuous.continuousOn Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have ha := heqclosed (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := heqclosed (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)
  change γ a = F (a - c) (γ c) at ha
  change γ b = F (b - c) (γ c) at hb
  rw [ha, ← F.map_add, show b - a + (a - c) = b - c by ring, ← hb]

theorem MorseCancellation.native_cubic_flow_between_box_points {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c r : ℝ}
    (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source) (z : Fin m → ℝ) {s t : ℝ}
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (ht : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (t - s) (Φ (cubicFlowCylinder σ a (z, s))) = Φ (cubicFlowCylinder σ a (z, t)) := by
  let γ : ℝ → M := fun u => Φ (cubicFlowCylinder σ a (z, u))
  have hforward {u v : ℝ} (huv : u < v)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hv : cubicFlowCylinder σ a (z, v) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (v - u) (γ u) = γ v := by
    have hstay (w : ℝ) (hw : w ∈ Set.Icc u v) : cubicFlowCylinder σ a (z, w) ∈ Φ.source :=
      hbox (cubicFlowCylinder_stays_axis_ball σ ha z hw hu hv)
    have hcont : ContinuousOn γ (Set.Icc u v) :=
      Φ.contMDiffOn_toFun.continuousOn.comp
        (((contDiff_cubicFlowCylinder σ a).continuous.comp
            (continuous_const.prodMk continuous_id)).continuousOn)
        hstay
    have hcurve : IsMIntegralCurveOn γ V (Set.Ioo u v) := by
      intro w hw
      have hp := hstay w ⟨hw.1.le, hw.2.le⟩
      have hd :=
        Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
          (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicFlowCylinder σ a z w) hp
      have hd' :
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ w
          ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeCubicDescent σ Φ (-(a ^ 2)) (γ w))) :=
        hd
      rw [← hmodel (γ w) (Φ.map_source' hp)] at hd'
      exact hd'.hasMFDerivWithinAt
    exact Degree.FlowSuspension.native_flow_segment_endpoints hV F hF huv hcont hcurve
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hforward hst hs ht
  · subst t
    rw [sub_self, F.map_zero_apply]
  · have hh := congrArg (F (t - s)) (hforward hts ht hs)
    rw [← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply] at hh
    exact hh.symm

theorem MorseCancellation.exists_cubic_slice_in_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {c r : ℝ} (hc : c ∈ Set.Icc (-a) a) (hr : 0 < r) :
    ∃ (T δ : ℝ),
      0 < δ ∧
        ∀ z : Fin m → ℝ,
          ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
  have hcl : c ∈ closure (Set.Ioo (-a) a) := by
    rw [closure_Ioo (by linarith : -a ≠ a)]
    exact hc
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp hcl r hr
  let T := cubicAxisClock a s
  have hpoint : cubicFlowCylinder σ a (0, T) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hnear : cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
    rw [hpoint, Metric.mem_ball, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ Dist.dist s c)]
    simpa only [dist_comm] using hdist
  have hcont : Continuous (fun z : Fin m → ℝ => cubicFlowCylinder σ a (z, T)) :=
    (contDiff_cubicFlowCylinder σ a).continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      (hcont.continuousAt (Metric.isOpen_ball.mem_nhds hnear))
  refine ⟨T, δ, hδ, ?_⟩
  intro z hz
  exact hδsub (mem_closedBall_zero_iff.mpr hz)

theorem MorseCancellation.exists_native_cubic_endpoint_flow_coordinates {m : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) :
    ∃ (r δ T : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              ∀ p ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r,
                p.1 ∈ Set.Ioo (-a) a →
                  ‖(cubicFlowCylinderInverse σ a p).1‖ ≤ δ →
                    Φ p =
                      F (cubicAxisClock a p.1 - T)
                        (Φ (cubicFlowCylinder σ a ((cubicFlowCylinderInverse σ a p).1, T))) := by
  obtain ⟨r, hr, hbox⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds hcΦ)
  obtain ⟨T, δ, hδ, hslice⟩ := exists_cubic_slice_in_axis_ball σ ha hc hr
  refine ⟨r, δ, T, hr, hδ, hbox, hslice, ?_⟩
  intro p hp hpa hpδ
  let z := (cubicFlowCylinderInverse σ a p).1
  have hinit := Metric.ball_subset_closedBall (hslice z hpδ)
  have hpoint : cubicFlowCylinder σ a (z, cubicAxisClock a p.1) = p :=
    cubicFlowCylinder_right_inv σ ha hpa
  have hfinish :
    cubicFlowCylinder σ a (z, cubicAxisClock a p.1) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ hp
  have hh := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox z hinit hfinish
  rw [hpoint] at hh
  exact hh.symm

theorem MorseCancellation.exists_endpoint_slice_on_actual_orbit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (r δ T τ : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              Φ (cubicFlowCylinder σ a (0, T)) = F τ x := by
  obtain ⟨r, δ, T, hr, hδ, hbox, hslice, _⟩ :=
    exists_native_cubic_endpoint_flow_coordinates σ ha Φ hV hmodel F hF hc hcΦ
  have hcont := Φ.toOpenPartialHomeomorph.symm.continuousAt (Φ.map_source' hcΦ)
  have hcoord : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (c, (0 : Fin m → ℝ))) := by
    have hh : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (Φ.symm (Φ (c, 0)))) :=
      hcont.tendsto.comp hlim
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    rwa [hinv] at hh
  have hnear : ∀ᶠ t in l, Φ.symm (F t x) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hcoord.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨t, htnear, s, hs, hsΦ, hsorbit⟩ := (hnear.and htail).exists
  have hinv : Φ.symm (F t x) = (s, (0 : Fin m → ℝ)) := by
    rw [← hsorbit]
    exact Φ.left_inv' hsΦ
  rw [hinv] at htnear
  have hpoint : cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hstart :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ Metric.ball_subset_closedBall htnear
  have hfinish : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hflow := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox 0 hstart hfinish
  rw [hpoint, hsorbit, ← F.map_add] at hflow
  exact ⟨r, δ, T, T - cubicAxisClock a s + t, hr, hδ, hbox, hslice, hflow.symm⟩

theorem Degree.SmoothODE.flow_shifted_chart_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞) (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) :
    (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).source = Φ.source := by
  ext p
  change p ∈ Φ.source ∧ Φ p ∈ Set.univ ↔ p ∈ Φ.source
  simp

theorem MorseCancellation.exists_clock_normalized_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∃ d : ℝ, ∀ z : Model m, Ψ z = F d (Φ z) := by
  have hV₁ := hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω))
  obtain ⟨r, δ, T, τ, hr, hδ, hbox, hslice, hcenter⟩ :=
    exists_endpoint_slice_on_actual_orbit σ ha Φ hV₁ hmodel F hF hc hcΦ x hlim htail
  have hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t) := fun t =>
    (Degree.SmoothODE.contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)
  let Ψ := Φ.trans (Degree.SmoothODE.nativeFlowTimeDiffeomorph F hs (T - τ)).toPartialDiffeomorph
  have hsource : Ψ.source = Φ.source := Degree.SmoothODE.flow_shifted_chart_source Φ F hs (T - τ)
  have hΨmodel : ∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y := by
    intro y hy
    exact
      Degree.SmoothODE.partialChartField_flow_shift Φ F hs hF (cubicDescent σ (-(a ^ 2))) hmodel
        (T - τ) hy
  have hzero : V (Φ (c, 0)) = 0 := by
    rw [hmodel _ (Φ.map_source' hcΦ)]
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    have hw : cubicDescent σ (-(a ^ 2)) (Φ.symm (Φ (c, 0))) = 0 := by
      rw [hinv]
      ext i <;> simp [cubicDescent, hcrit]
    unfold nativeCubicDescent Smale.FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, hw, map_zero, map_zero]
  have hvalue : Ψ (c, 0) = Φ (c, 0) :=
    Smale.FlowConstruction.flow_fixed_of_zero hV₁ F hF hzero (T - τ)
  have hΨbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source := hsource.symm ▸ hbox
  have hbase : Ψ (cubicFlowCylinder σ a (0, T)) = F T x := by
    change F (T - τ) (Φ (cubicFlowCylinder σ a (0, T))) = F T x
    rw [hcenter, ← F.map_add, sub_add_cancel]
  refine ⟨Ψ, r, δ, T, hsource, hvalue, hr, hδ, hΨbox, hslice, hΨmodel, ?_, T - τ, fun _ => rfl⟩
  intro t ht
  have hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hh := native_cubic_flow_between_box_points σ ha Ψ hV₁ hΨmodel F hF hΨbox 0 hstart ht
  rw [hbase, ← F.map_add, sub_add_cancel] at hh
  exact hh.symm

theorem MorseCancellation.flow_time_atTop_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atTop_add_const_right Filter.atTop d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

theorem MorseCancellation.flow_time_atBot_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atBot_add_const_right Filter.atBot d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

theorem MorseCancellation.exists_basin_preserving_endpoint_clock {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∀ z : Model m,
                        ∀ p : M,
                          (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atTop (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p)) ∧
                            (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atBot (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 p)) := by
  obtain ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, d, hmap⟩ :=
    exists_clock_normalized_cubic_endpoint σ ha Φ hV hmodel F hF hc hcrit hcΦ x hlim htail
  refine ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, ?_⟩
  intro z p
  rw [hmap]
  exact ⟨flow_time_atTop_limit_iff F d (Φ z) p, flow_time_atBot_limit_iff F d (Φ z) p⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.flow_belt_passage {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    S.flow (Degree.BeltPassage.time s)
        ((S.data q).chart.splitChart.symm
          (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)) =
      (S.data q).chart.splitChart.symm
        (Degree.BeltPassage.lower (S.data q).radius s u.val v.val) := by
  let d := S.data q
  let z := Degree.BeltPassage.upper d.radius s u.val v.val
  have htime := Degree.BeltPassage.time_nonneg hs
  have hstay (t : ℝ) (ht : t ∈ Set.uIcc 0 (Degree.BeltPassage.time s)) :
    Smale.MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    rw [Set.uIcc_of_le htime] at ht
    exact
      Degree.BeltPassage.descentFlow_mem_block d.radius_pos hs hs₁
        (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property) ht
  have hz : z ∈ d.chart.splitChart.target := by
    have hh := d.block (hstay 0 Set.left_mem_uIcc)
    simpa only [Smale.MorseHandle.descentFlow.map_zero_apply] using hh
  have hcoords : d.chart.splitChart (d.chart.splitChart.symm z) = z :=
    d.chart.splitChart.right_inv' hz
  have hflow :=
    d.chart.flow_eq_descentModel_of_mem_uIcc (S.smooth.of_le (by simp)) S.flow S.integral (x :=
      d.chart.splitChart.symm z) (d.chart.splitChart.map_target' hz) (t :=
      Degree.BeltPassage.time s) (fun t ht => by rw [hcoords]; exact d.block (hstay t ht))
      (fun t ht => by rw [hcoords]; exact S.model_germ q _ (hstay t ht))
  change
    S.flow (Degree.BeltPassage.time s) (d.chart.splitChart.symm z) =
      d.chart.splitChart.symm
        (Smale.MorseHandle.descentFlow (Degree.BeltPassage.time s)
          (d.chart.splitChart (d.chart.splitChart.symm z))) at hflow
  rw [hcoords, Degree.BeltPassage.descentFlow_time d.radius hs u.val v.val] at hflow
  exact hflow

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.belt_passage_forward_limit_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f) {s : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (p : M) :
    Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) ↔
      Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (Degree.BeltPassage.lower (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) := by
  rw [← S.flow_belt_passage q hs hs₁ u v]
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow (Degree.BeltPassage.time s) _ p).symm

theorem MorseCancellation.compact_partial_chart_image_nowhereDense {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [T2Space X] (e : OpenPartialHomeomorph X A) {K : Set A}
    (hK : IsCompact K) (hKt : K ⊆ e.target) (hKi : interior K = ∅) :
    IsNowhereDense (e.symm '' K) := by
  have hclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)).isClosed
  apply hclosed.isNowhereDense_iff.mpr
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  have hopen : IsOpen (e '' interior (e.symm '' K)) :=
    e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsource)
  have hsub : e '' interior (e.symm '' K) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := interior_subset hx
    rw [← hzx, e.right_inv (hKt hz)]
    exact hz
  have hinto : e '' interior (e.symm '' K) ⊆ interior K := hopen.subset_interior_iff.mpr hsub
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hinto (Set.mem_image_of_mem e hx)
  exact (Set.eq_empty_iff_forall_notMem.mp hKi) _ hh

theorem MorseCancellation.interior_zero_product_empty {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [Nontrivial A] [TopologicalSpace B] (s : Set B) :
    interior (({0} : Set A) ×ˢ s) = ∅ := by
  rw [interior_prod_eq, interior_singleton, Set.empty_prod]

theorem MorseCancellation.native_positive_plane_piece_nowhereDense {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hindex : 0 < Module.finrank ℝ c.NegativeCoordinates) {r : ℝ}
    (hblock :
      ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target) :
    IsNowhereDense
      (c.splitChart.symm ''
        (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r)) :=
  by
  let : Nontrivial c.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  exact
    compact_partial_chart_image_nowhereDense c.splitChart.toOpenPartialHomeomorph
      (isCompact_singleton.prod (ProperSpace.isCompact_closedBall _ _)) hblock
      (interior_zero_product_empty _)

theorem MorseCancellation.exists_backward_morse_quadratic_level_exit {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ}
    (hr : 0 < r) {z : N × P} (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ s : ℝ,
      s < 0 ∧
        Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow s z) = r ^ 2 ∧
          (∀ t ∈ Set.Icc s (0 : ℝ),
              Smale.MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(Smale.MorseHandle.descentFlow s z).1‖ ≤ ‖z.1‖ := by
  let R := 3 * r / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  let T := -Real.log (R / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < R / ‖z.2‖ := (one_lt_div hn).mpr (hzp.trans hrR)
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = R / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hR hn)]
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).2‖ = R := by
    rw [Smale.MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ R hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(Smale.MorseHandle.descentFlow t z).1‖ ≤ ‖z.1‖ := by
    rw [Smale.MorseHandle.norm_descentFlow_fst]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)
  have hstay (t : ℝ) (ht : t ∈ Set.Icc T (0 : ℝ)) :
    Smale.MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r) := by
    constructor
    · exact mem_closedBall_zero_iff.mpr ((hsmall t ht.2).trans (by linarith))
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = R := by rw [hexp, div_mul_cancel₀ R hn.ne']
        _ ≤ 2 * r := by dsimp [R]; linarith
  have hheightT : r ^ 2 < Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) := by
    change
      r ^ 2 <
        -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr ((hsmall T hT.le).trans_lt hzn)
    dsimp [R]
    nlinarith [sq_pos_of_pos hr]
  have hheight0 : Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow 0 z) < r ^ 2 := by
    rw [Flow.map_zero_apply]
    change -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hzp
    nlinarith [sq_nonneg ‖z.1‖]
  have hc :
    Continuous (fun t : ℝ => Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow t z)) := by
    change
      Continuous
        (fun t : ℝ =>
          -‖(Smale.MorseHandle.descentFlow t z).1‖ ^ 2 +
            ‖(Smale.MorseHandle.descentFlow t z).2‖ ^ 2)
    exact
      (((Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const).fst.norm.pow
              2).neg).add
        ((Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const).snd.norm.pow 2)
  obtain ⟨s, hs, hlevel⟩ :=
    intermediate_value_Icc' hT.le hc.continuousOn
      (show
        r ^ 2 ∈
          Set.Icc (Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow 0 z))
            (Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z))
        from ⟨hheight0.le, hheightT.le⟩)
  have hs0 : s < 0 :=
    lt_of_le_of_ne hs.2
      (by
        intro heq
        rw [heq] at hlevel
        linarith)
  exact ⟨s, hs0, hlevel, fun t ht => hstay t ⟨hs.1.trans ht.1, ht.2⟩, hsmall s hs0.le⟩

theorem MorseCancellation.morse_descentFlow_swap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    Smale.MorseHandle.descentFlow t z.swap = (Smale.MorseHandle.descentFlow (-t) z).swap := by
  simp only [Smale.MorseHandle.descentFlow, neg_neg, Prod.swap]

theorem MorseCancellation.morse_quadratic_swap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : N × P) :
    Smale.MorseHandle.quadratic z.swap = -Smale.MorseHandle.quadratic z := by
  change -‖z.2‖ ^ 2 + ‖z.1‖ ^ 2 = -(-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  ring

theorem MorseCancellation.exists_forward_morse_quadratic_level_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ s : ℝ,
      0 < s ∧
        Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow s z) = -(r ^ 2) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s,
              Smale.MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(Smale.MorseHandle.descentFlow s z).2‖ ≤ ‖z.2‖ := by
  obtain ⟨s, hs, hlevel, hstay, hsmall⟩ :=
    exists_backward_morse_quadratic_level_exit (z := z.swap) hr hzp hzn hne
  rw [morse_descentFlow_swap, morse_quadratic_swap] at hlevel
  rw [morse_descentFlow_swap] at hsmall
  refine ⟨-s, neg_pos.mpr hs, by linarith, ?_, hsmall⟩
  intro t ht
  have hh :=
    hstay (-t) (show -t ∈ Set.Icc s (0 : ℝ) from ⟨by linarith [ht.2], neg_nonpos.mpr ht.1⟩)
  rw [morse_descentFlow_swap, neg_neg] at hh
  exact ⟨hh.2, hh.1⟩

theorem MorseCancellation.exists_uniform_small_of_zero_set {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : X → ℝ} (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x) {U : Set X}
    (hU : IsOpen U) (hzero : ∀ x, g x = 0 → x ∈ U) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, g x < δ → x ∈ U := by
  have hpos : ∀ x ∈ Uᶜ, 0 < g x := by
    intro x hx
    exact lt_of_le_of_ne (hnonneg x) (fun hh => hx (hzero x hh.symm))
  obtain ⟨δ, hδ, hbound⟩ := hU.isClosed_compl.isCompact.exists_forall_le' hg.continuousOn hpos
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_contra hnot
  exact (not_lt_of_ge (hbound x hnot)) hx

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_upper_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          Smale.MorseHandle.quadratic z = r ^ 2 → ‖z.1‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | Smale.MorseHandle.quadratic z = r ^ 2}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq Smale.MorseHandle.continuous_quadratic continuous_const)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact
      (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
          (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖) :=
    continuous_subtype_val.fst.norm
  have hzero :
    ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = 0 → z ∈ ψ ⁻¹' U := by
    intro z hz
    have hn : (z : c.NegativeCoordinates × c.PositiveCoordinates).1 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change
      -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
          ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 =
        r ^ 2 at hq
    rw [hn, norm_zero] at hq
    have hp : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).2]
    let v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).2,
        by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          hp]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv :
      r • (v : c.PositiveCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).2 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.beltCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext hn rfl)
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _) (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_lower_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          Smale.MorseHandle.quadratic z = -(r ^ 2) → ‖z.2‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | Smale.MorseHandle.quadratic z = -(r ^ 2)}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq Smale.MorseHandle.continuous_quadratic continuous_const)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact
      (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
          (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖) :=
    continuous_subtype_val.snd.norm
  have hzero :
    ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = 0 → z ∈ ψ ⁻¹' U := by
    intro z hz
    have hp : (z : c.NegativeCoordinates × c.PositiveCoordinates).2 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change
      -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
          ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 =
        -(r ^ 2) at hq
    rw [hp, norm_zero] at hq
    have hn : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).1]
    let v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).1,
        by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          hn]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv :
      r • (v : c.NegativeCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).1 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.attachingCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext rfl hp)
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _) (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_native_backward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).2 ≠ 0) :
    ∃ T : ℝ,
      T < 0 ∧
        f (F T x) = f p + r ^ 2 ∧
          F T x ∈ c.splitChart.source ∧
            ‖(c.splitChart (F T x)).1‖ ≤ ‖(c.splitChart x).1‖ ∧
              c.splitChart (F T x) ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_backward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [Set.uIcc_of_ge hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨le_rfl, hT.le⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = Smale.MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        r ^ 2 at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨le_rfl, hT.le⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_native_forward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).1 ≠ 0) :
    ∃ T : ℝ,
      0 < T ∧
        f (F T x) = f p - r ^ 2 ∧
          F T x ∈ c.splitChart.source ∧
            ‖(c.splitChart (F T x)).2‖ ≤ ‖(c.splitChart x).2‖ ∧
              c.splitChart (F T x) ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_forward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [Set.uIcc_of_le hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨hT.le, le_rfl⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = Smale.MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        -(r ^ 2) at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨hT.le, le_rfl⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.morse_coordinate_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source ∧ ‖(c.splitChart x).1‖ < a ∧ ‖(c.splitChart x).2‖ < b := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hn : ‖(c.splitChart p).1‖ < a := by
    simpa only [c.splitChart_center, Prod.fst_zero, norm_zero] using ha
  have hp : ‖(c.splitChart p).2‖ < b := by
    simpa only [c.splitChart_center, Prod.snd_zero, norm_zero] using hb
  have hs : ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hna : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).1‖ < a := hc.fst.norm (eventually_lt_nhds hn)
  have hpb : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).2‖ < b := hc.snd.norm (eventually_lt_nhds hp)
  exact hs.and (hna.and hpb)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_backward_exit_in_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
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
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).2 ≠ 0 → ∃ T : ℝ, T < 0 ∧ f (F T x) = f p + r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_upper_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c (lt_min hr hδ) hr] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_backward_morse_level_exit c hV F hF hr hblock hfield hx.1
      (hx.2.1.trans_le (min_le_left _ _)) hx.2.2 hne
  have hq : Smale.MorseHandle.quadratic (c.splitChart (F T x)) = r ^ 2 := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = r ^ 2
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.1.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_forward_exit_in_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
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
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).1 ≠ 0 → ∃ T : ℝ, 0 < T ∧ f (F T x) = f p - r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_lower_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c hr (lt_min hr hδ)] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_forward_morse_level_exit c hV F hF hr hblock hfield hx.1 hx.2.1
      (hx.2.2.trans_le (min_le_left _ _)) hne
  have hq : Smale.MorseHandle.quadratic (c.splitChart (F T x)) = -(r ^ 2) := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = -(r ^ 2)
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.2.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

theorem MorseCancellation.quadratic_germ_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (Q : QuadraticForm ℝ A)
    (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B} {L : A →L[ℝ] B}
    (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) (v : A) :
    R (L v) = Q v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hcurve : HasDerivAt (fun t : ℝ => F (t • v)) (L v) 0 :=
    hF.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • F (t • v)) (𝓝[≠] 0) (𝓝 (L v)) := by
    simpa only [zero_add, zero_smul, hF0, sub_zero] using hcurve.tendsto_slope_zero
  have hpath : Filter.Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 (0 : A)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => R (t⁻¹ • F (t • v))) =ᶠ[𝓝[≠] 0] fun _ => Q v := by
    filter_upwards [hquad.comp_tendsto hpath, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    change R (F (t • v)) = Q (t • v) at ht
    rw [R.map_smul, ht, Q.map_smul]
    simp only [smul_eq_mul]
    field_simp
  exact
    tendsto_nhds_unique (hR.continuousAt.tendsto.comp hslope)
      ((Filter.tendsto_congr' heq).mpr tendsto_const_nhds)

theorem MorseCancellation.equivalent_quadratic_germs_of_bijective_derivative {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : QuadraticForm ℝ A) (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B}
    {L : A →L[ℝ] B} (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hL : Function.Bijective L)
    (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) : Q.Equivalent R := by
  let e := LinearEquiv.ofBijective L.toLinearMap hL
  exact ⟨{ e with map_app' := quadratic_germ_derivative Q R hR hF hF0 hquad }⟩

theorem MorseCancellation.surgery_pair_band_isolation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
      f z ∈ Set.Icc (S.lower p) (S.upper q) → z = p.val ∨ z = q.val := by
  intro z hz hband
  by_cases hzp : f z ≤ f p
  · exact Or.inl (S.isolated p z hz ⟨hband.1, hzp.trans (S.value_lt_upper p).le⟩)
  by_cases hqz : f q ≤ f z
  · exact Or.inr (S.isolated q z hz ⟨(S.lower_lt_value q).le.trans hqz, hband.2⟩)
  exact (hconsecutive ⟨z, hz⟩ ⟨lt_of_not_ge hzp, lt_of_not_ge hqz⟩).elim

theorem MorseCancellation.surviving_critical_germs_of_pair_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {l u : ℝ}
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hexterior : ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f := by
  intro z hz
  obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
  apply hexterior z
  intro hband
  exact (hpair z hzf ⟨hband.1.le, hband.2.le⟩).elim hzp hzq

theorem MorseCancellation.distinct_critical_values_of_surviving_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hsub : Smale.ManifoldMorse.criticalPoints E g ⊆ Smale.ManifoldMorse.criticalPoints E f)
    (hgerms : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) :
    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  rw [← (hgerms x hx).self_of_nhds, ← (hgerms y hy).self_of_nhds]
  exact hxy

theorem MorseCancellation.exists_signed_morse_chart_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p,
      d.weights = c.weights ∧
        d.chart.source ⊆ c.chart.source ∧
          (∀ x, d.chart x = c.chart x) ∧ ∀ z, d.chart.symm z = c.chart.symm z := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let P := Smale.PartialChart.restrictSource c.chart hU
  let d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := P
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl, Set.inter_subset_left, fun _ => rfl, fun _ => rfl⟩

theorem MorseCancellation.adapted_surgeries_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val)
    (hexterior : ∀ z, f z ∉ Set.Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 z] f) :
    (∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation S p q hconsecutive) hcrit
      hexterior
  have hinj :=
    distinct_critical_values_of_surviving_germs S.distinct (fun z hz => ((hcrit z).mp hz).1) hkeep
  exact ⟨hkeep, hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

theorem MorseCancellation.signed_morse_chart_quadratic_equivalent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    (QuadraticMap.weightedSumSquares ℝ c.weights).Equivalent
      (QuadraticMap.weightedSumSquares ℝ d.weights) := by
  let Z := Fin (Module.finrank ℝ E) → ℝ
  let Q : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ c.weights
  let R : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ d.weights
  have hQ (z : Z) : Q z = ∑ i, c.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) c.weights z)
  have hR (z : Z) : R z = ∑ i, d.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) d.weights z)
  have hRcont : Continuous R := by
    change Continuous (fun z : Z => R z)
    simp_rw [hR]
    fun_prop
  let P := c.chart.symm.trans d.chart
  have hc0 : c.chart.symm (0 : Z) = p := by
    rw [← c.center]
    exact c.chart.left_inv' c.mem_source
  have h0 : (0 : Z) ∈ P.source := by
    refine ⟨?_, ?_⟩
    · rw [← c.center]
      exact c.chart.map_source' c.mem_source
    · change c.chart.symm (0 : Z) ∈ d.chart.source
      rw [hc0]
      exact d.mem_source
  have hP0 : P (0 : Z) = 0 := by
    change d.chart (c.chart.symm (0 : Z)) = 0
    rw [hc0, d.center]
  have hdiff := (P.mdifferentiableAt (by simp) h0).differentiableAt
  have hbij : Function.Bijective (fderiv ℝ P (0 : Z)) := by
    have hh := Smale.PartialChart.bijective_mfderiv P h0
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hquad : (fun z => R (P z)) =ᶠ[𝓝 (0 : Z)] Q := by
    filter_upwards [P.open_source.mem_nhds h0] with z hz
    have hzs : z ∈ c.chart.target ∧ c.chart.symm z ∈ d.chart.source := hz
    rw [hR, hQ]
    change (∑ i, d.weights i * (d.chart (c.chart.symm z) i) ^ 2) = ∑ i, c.weights i * (z i) ^ 2
    linarith [c.inverse_equation z hzs.1, d.equation (c.chart.symm z) hzs.2]
  exact
    equivalent_quadratic_germs_of_bijective_derivative Q R hRcont hdiff.hasFDerivAt hP0 hbij hquad

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_morse_chart_negative_card_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Fintype.card { i // c.weights i = -1 } = Fintype.card { i // d.weights i = -1 } := by
  have hs := (signed_morse_chart_quadratic_equivalent c d).sigNeg_eq
  rw [QuadraticForm.sigNeg_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares] at hs
  have hc : {i | c.weights i < 0} = {i | c.weights i = -1} := by
    ext i
    rcases c.signs i with h | h <;> norm_num [h]
  have hd : {i | d.weights i < 0} = {i | d.weights i = -1} := by
    ext i
    rcases d.signs i with h | h <;> norm_num [h]
  rw [hc, hd] at hs
  calc
    Fintype.card { i // c.weights i = -1 } = {i | c.weights i = -1}.ncard :=
      Set.fintypeCard_eq_ncard _
    _ = {i | d.weights i = -1}.ncard := hs
    _ = Fintype.card { i // d.weights i = -1 } := (Set.fintypeCard_eq_ncard _).symm

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_morse_chart_negative_finrank_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using
    signed_morse_chart_negative_card_eq c d

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_morse_chart_negative_finrank_eq_of_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p) (hgerm : g =ᶠ[𝓝 p] f) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  obtain ⟨c', hw, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
  have heq := signed_morse_chart_negative_card_eq c' d
  rw [hw] at heq
  simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using heq

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeMorseIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  if h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p) then
    Module.finrank ℝ (Classical.choice h).NegativeCoordinates
  else 0

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeMorseIndex_eq_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E f p = Module.finrank ℝ c.NegativeCoordinates := by
  unfold nativeMorseIndex
  rw [dif_pos ⟨c⟩]
  exact signed_morse_chart_negative_finrank_eq _ c

theorem MorseCancellation.nativeMorseIndex_congr_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hgerm : g =ᶠ[𝓝 p] f) : nativeMorseIndex E g p = nativeMorseIndex E f p := by
  classical
  by_cases h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    obtain ⟨d, -, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
    rw [nativeMorseIndex_eq_chart c, nativeMorseIndex_eq_chart d]
    exact (signed_morse_chart_negative_finrank_eq_of_germ c d hgerm).symm
  · have hg : ¬Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) g p) := by
      rintro ⟨d⟩
      obtain ⟨c, -, -, -, -⟩ := exists_signed_morse_chart_of_germ d hgerm.symm
      exact h ⟨c⟩
    simp only [nativeMorseIndex, dif_neg h, dif_neg hg]

theorem MorseCancellation.nativeMorseIndex_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} :
    nativeMorseIndex E f p ≤ Module.finrank ℝ E := by
  classical
  by_cases h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    rw [nativeMorseIndex_eq_chart c]
    have hc := c.finrank_negative_add_positive
    omega
  · simp only [nativeMorseIndex, dif_neg h, Nat.zero_le]

theorem AdaptedWindows.nonminimum_forward_basin_meagre {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : 0 < MorseCancellation.nativeMorseIndex E f p) :
    IsMeagre {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  let K :=
    c.splitChart.symm ''
      (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2))
  have hKt :
    ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2) ⊆
      c.splitChart.target := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha0 : a = 0 := ha
    subst a
    exact
      hblock
        ⟨Metric.mem_closedBall_self hr.le,
          Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hb⟩
  have hi : 0 < Module.finrank ℝ c.NegativeCoordinates := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart c] at hindex
  have hK : IsNowhereDense K := MorseCancellation.native_positive_plane_piece_nowhereDense c hi hKt
  have hcover :
    {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} ⊆
      ⋃ n : ℕ, S.flow (-(n : ℝ)) '' K := by
    intro x hx
    have hlim : Filter.Tendsto (fun n : ℕ => S.flow (n : ℝ) x) Filter.atTop (𝓝 p.val) :=
      hx.comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hs, hn, hp⟩ :=
      (hlim.eventually
          (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
    have hnew : Filter.Tendsto (fun t => S.flow t (S.flow (n : ℝ) x)) Filter.atTop (𝓝 p.val) :=
      (MorseCancellation.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
    have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
      ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp.trans (half_lt_self hr))).1).mp hnew
    have hmem : S.flow (n : ℝ) x ∈ K := by
      refine ⟨c.splitChart (S.flow (n : ℝ) x), ?_, c.splitChart.left_inv' hs⟩
      exact ⟨Set.mem_singleton_iff.mpr hz, mem_closedBall_zero_iff.mpr hp.le⟩
    exact
      Set.mem_iUnion.mpr
        ⟨n, S.flow (n : ℝ) x, hmem, (S.flow.toHomeomorph (n : ℝ)).symm_apply_apply x⟩
  apply IsMeagre.mono hcover
  apply isMeagre_iUnion
  intro n
  exact ((S.flow.toHomeomorph (-(n : ℝ))).isInducing.isNowhereDense_image hK).isMeagre

theorem Degree.FlowCancellation.height_eq_of_mem_omegaLimit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ} {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) {y : X}
    (hy : y ∈ omegaLimit κ F { x }) : f y = l := by
  have hc : MapClusterPt y κ (fun t => F t x) :=
    (mem_omegaLimit_singleton_iff_mapClusterPt κ F x y).mp hy
  have hh := hc.continuousAt_comp hf.continuousAt
  have hl : Filter.map (f ∘ (fun t => F t x)) κ ≤ 𝓝 l := hlim
  exact eq_of_nhds_neBot (hh.clusterPt.mono hl)

theorem Degree.FlowCancellation.omegaLimit_subset_of_strict_height {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ}
    (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) : omegaLimit κ F { x } ⊆ S := by
  intro y hy
  by_contra hnot
  have hy' : F 1 y ∈ omegaLimit κ F { x } := (F.isInvariant_omegaLimit κ { x } hshift) 1 hy
  have h0 := height_eq_of_mem_omegaLimit F hf hlim hy
  have h1 := height_eq_of_mem_omegaLimit F hf hlim hy'
  have hs := hstrict y hnot
  rw [h0, h1] at hs
  exact lt_irrefl _ hs

theorem Degree.FlowCancellation.exists_flow_limit_of_injective_exceptional_height {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {κ : Filter ℝ} [Filter.NeBot κ] (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) (hinj : Set.InjOn f S) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) :
    ∃ p ∈ S, f p = l ∧ Filter.Tendsto (fun t : ℝ => F t x) κ (𝓝 p) := by
  have hsub := omegaLimit_subset_of_strict_height F hf hshift hstrict hlim
  obtain ⟨p, hp⟩ := nonempty_omegaLimit κ F { x } (Set.singleton_nonempty x)
  have hpl := height_eq_of_mem_omegaLimit F hf hlim hp
  have hsingle : omegaLimit κ F { x } ⊆ { p } := by
    intro y hy
    exact hinj (hsub hy) (hsub hp) ((height_eq_of_mem_omegaLimit F hf hlim hy).trans hpl.symm)
  refine ⟨p, hsub hp, hpl, ?_⟩
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  have hωV : omegaLimit κ F { x } ⊆ V := hsingle.trans (Set.singleton_subset_iff.mpr hpV)
  have hEv := eventually_mapsTo_of_isOpen_of_omegaLimit_subset κ F { x } hV hωV
  filter_upwards [hEv] with t ht
  exact hVU (ht (Set.mem_singleton x))

theorem Degree.FlowCancellation.exists_strict_descent_flow_endpoints {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) (x : X) :
    ∃ p ∈ S,
      ∃ q ∈ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ S → f q < f x ∧ f x < f p) := by
  have hrange : Set.range (fun t : ℝ => f (F t x)) ⊆ Set.range f := by
    rintro y ⟨t, rfl⟩
    exact ⟨F t x, rfl⟩
  have hbelow : BddBelow (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddBelow.mono hrange
  have habove : BddAbove (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddAbove.mono hrange
  have htop := tendsto_atTop_ciInf (hmono x) hbelow
  have hbot := tendsto_atBot_ciSup (hmono x) habove
  have hshiftTop (t : ℝ) : Filter.Tendsto (t + ·) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - t)] with s hs
    linarith
  have hshiftBot (t : ℝ) : Filter.Tendsto (t + ·) Filter.atBot Filter.atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    filter_upwards [Filter.eventually_le_atBot (b - t)] with s hs
    linarith
  have hstep (y : X) (hy : y ∉ S) : f (F 1 y) < f y := by
    have hh := hstrict y hy (show (0 : ℝ) < 1 by norm_num)
    simpa only [F.map_zero_apply] using hh
  obtain ⟨p, hp, hfp, hplim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftBot hstep hinj hbot
  obtain ⟨q, hq, hfq, hqlim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftTop hstep hinj htop
  refine ⟨p, hp, q, hq, hplim, hqlim, ?_⟩
  intro hx
  have hlow : f q ≤ f (F 1 x) := by
    rw [hfq]
    exact ciInf_le hbelow 1
  have hhigh : f (F (-1) x) ≤ f p := by
    rw [hfp]
    exact le_ciSup habove (-1)
  have hdec : f (F 1 x) < f x := hstep x hx
  have hinc : f x < f (F (-1) x) := by
    have hh := hstrict x hx (show (-1 : ℝ) < 0 by norm_num)
    simpa only [F.map_zero_apply] using hh
  exact ⟨hlow.trans_lt hdec, hinc.trans_le hhigh⟩

theorem Degree.FlowCancellation.exists_uniform_flow_escape {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {C : Set X} (hC : IsCompact C) {c d : ℝ}
    (hescape : ∀ x ∈ C, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ,
      0 < T ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∃ t ∈ Set.Icc (-T) T, f (F t x) < c - δ ∨ d + δ < f (F t x) := by
  classical
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, by norm_num, 1, by norm_num, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let J := { p : ℝ × ℝ // 0 < p.2 }
  let O : J → Set X := fun p =>
    {x | f (F p.val.1 x) < c - p.val.2 ∨ d + p.val.2 < f (F p.val.1 x)}
  have hO (p : J) : IsOpen (O p) :=
    (isOpen_lt (hf.comp (F.continuous_toFun p.val.1)) continuous_const).union
      (isOpen_lt continuous_const (hf.comp (F.continuous_toFun p.val.1)))
  have hcover : C ⊆ ⋃ p, O p := by
    intro x hx
    obtain ⟨t, ht⟩ := hescape x hx
    by_cases hl : c ≤ f (F t x)
    · have hr : d < f (F t x) := lt_of_not_ge (fun h => ht ⟨hl, h⟩)
      have hδ : 0 < (f (F t x) - d) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (f (F t x) - d) / 2), hδ⟩, Or.inr ?_⟩
      change d + (f (F t x) - d) / 2 < f (F t x)
      linarith
    · have hl' : f (F t x) < c := lt_of_not_ge hl
      have hδ : 0 < (c - f (F t x)) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (c - f (F t x)) / 2), hδ⟩, Or.inl ?_⟩
      change f (F t x) < c - (c - f (F t x)) / 2
      linarith
  obtain ⟨S, hScover⟩ := hC.elim_finite_subcover O hO hcover
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := Set.mem_iUnion₂.mp (hScover hx)
    exact ⟨p, hp⟩
  let T := S.sup' hS (fun p => |p.val.1|) + 1
  let δ := S.inf' hS (fun p => p.val.2) / 2
  have hmin : 0 < S.inf' hS (fun p => p.val.2) :=
    (Finset.lt_inf'_iff hS).mpr (fun p _ => p.property)
  have hT : 0 < T := by
    obtain ⟨p, hp⟩ := hS
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    have habs := abs_nonneg p.val.1
    dsimp [T]
    linarith
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  refine ⟨T, hT, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp (hScover hx)
  have ht : |p.val.1| ≤ T := by
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    dsimp [T]
    linarith
  have hd : δ ≤ p.val.2 := by
    have hh := Finset.inf'_le (fun p : J => p.val.2) hp
    dsimp [δ]
    linarith
  refine ⟨p.val.1, abs_le.mp ht, ?_⟩
  rcases hpx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem Degree.FlowCancellation.exists_flow_no_return_neighborhood {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {c d : ℝ} {K U : Set X} (hU : IsOpen U)
    (hKU : K ⊆ U) (hband : ∀ x ∈ K, f x ∈ Set.Icc c d) (hinvariant : ∀ t x, x ∈ K → F t x ∈ K)
    (hmaximal : ∀ x, (∀ t : ℝ, f (F t x) ∈ Set.Icc c d) → x ∈ K) :
    ∃ N : Set X,
      IsOpen N ∧
        K ⊆ N ∧
          N ⊆ U ∧ ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hescape : ∀ x ∈ Uᶜ, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d := by
    intro x hx
    by_contra hh
    apply hx
    apply hKU
    apply hmaximal x
    intro t
    by_contra ht
    exact hh ⟨t, ht⟩
  obtain ⟨T, hT, δ, hδ, hEsc⟩ :=
    exists_uniform_flow_escape F hf hU.isClosed_compl.isCompact hescape
  let N : Set X := {x | ∀ s ∈ Set.Icc (-T) T, F s x ∈ U} ∩ f ⁻¹' Set.Ioo (c - δ) (d + δ)
  have hN : IsOpen N :=
    (Smale.MorsePerturbation.isOpen_forall_mem_compact CompactIccSpace.isCompact_Icc
          (hU.preimage (F.continuous continuous_snd continuous_fst))).inter
      (isOpen_Ioo.preimage hf)
  have hKN : K ⊆ N := by
    intro x hx
    refine ⟨fun s _ => hKU (hinvariant s x hx), ?_⟩
    have hh := hband x hx
    constructor <;> linarith [hh.1, hh.2]
  have hNU : N ⊆ U := by
    intro x hx
    have hh := hx.1 0 (show (0 : ℝ) ∈ Set.Icc (-T) T from ⟨by linarith, hT.le⟩)
    simpa only [F.map_zero_apply] using hh
  refine ⟨N, hN, hKN, hNU, ?_⟩
  intro x hx t ht htx s hs
  by_cases hshort : s ≤ T
  · exact hx.1 s ⟨by linarith [hs.1], hshort⟩
  have hTs : T < s := lt_of_not_ge hshort
  by_cases hshort' : t - s ≤ T
  · have hh := htx.1 (s - t) (show s - t ∈ Set.Icc (-T) T from ⟨by linarith, by linarith [hs.2]⟩)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  have hTs' : T < t - s := lt_of_not_ge hshort'
  by_contra hout
  obtain ⟨v, hv, hleave⟩ := hEsc (F s x) hout
  have htime : s + v ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hlo := hmono x htime.1
  have hhi := hmono x htime.2
  change f (F (s + v) x) ≤ f (F 0 x) at hlo
  change f (F t x) ≤ f (F (s + v) x) at hhi
  rw [F.map_zero_apply] at hlo
  rw [← F.map_add, add_comm v s] at hleave
  have hxheight : f x ∈ Set.Ioo (c - δ) (d + δ) := hx.2
  have htheight : f (F t x) ∈ Set.Ioo (c - δ) (d + δ) := htx.2
  rcases hleave with h | h
  · linarith [htheight.1]
  · linarith [hxheight.2]

theorem Degree.FlowCancellation.invariant_band_subset_connection {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q z : X}
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {x : X} (hstay : ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)) :
    x ∈ ({ p, q } : Set X) ∪ Set.range (fun t : ℝ => F t z) := by
  have hxband : f x ∈ Set.Icc (f p) (f q) := by simpa only [F.map_zero_apply] using hstay 0
  by_cases hxS : x ∈ S
  · rcases hpair x hxS hxband with rfl | rfl <;> exact Or.inl (by simp)
  obtain ⟨r, hr, s, hs, hrlim, hslim, hsep⟩ :=
    exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrband : f r ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hrlim)
      (Filter.Eventually.of_forall hstay)
  have hsband : f s ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hslim)
      (Filter.Eventually.of_forall hstay)
  have hsep' := hsep hxS
  have hrq : r = q :=
    (hpair r hr hrband).resolve_left
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.1])
  have hsp : s = p :=
    (hpair s hs hsband).resolve_right
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.2])
  obtain ⟨t, ht⟩ :=
    hunique x hxS (by simpa only [hrq] using hrlim) (by simpa only [hsp] using hslim)
  exact Or.inr ⟨t, ht⟩

theorem Degree.FlowCancellation.exists_isolated_connection_no_return {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    (hfixed : ∀ x ∈ S, ∀ t : ℝ, F t x = x) {p q z : X} (hp : p ∈ S) (hq : q ∈ S) (hpq : f p < f q)
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set X,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  let K : Set X := {x | ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)}
  have hKU : K ⊆ U := by
    intro x hx
    rcases invariant_band_subset_connection F hf hinj hmono hstrict hpair hunique hx with h |
      ⟨t, rfl⟩
    · rcases h with h | h
      · exact h ▸ hpU
      · exact (show x = q from h) ▸ hqU
    · exact hzU t
  have hKband (x : X) (hx : x ∈ K) : f x ∈ Set.Icc (f p) (f q) := by
    simpa only [F.map_zero_apply] using hx 0
  have hKi (t : ℝ) (x : X) (hx : x ∈ K) : F t x ∈ K := by
    intro s
    rw [← F.map_add]
    exact hx (s + t)
  obtain ⟨N, hN, hKN, hNU, hreturn⟩ :=
    exists_flow_no_return_neighborhood F hf hmono hU hKU hKband hKi (fun _ h => h)
  have hpK : p ∈ K := by
    intro t
    rw [hfixed p hp t]
    exact ⟨le_rfl, hpq.le⟩
  have hqK : q ∈ K := by
    intro t
    rw [hfixed q hq t]
    exact ⟨hpq.le, le_rfl⟩
  exact ⟨N, hN, hNU, hKN hpK, hKN hqK, fun t => hKN (hKi t z hzband), hreturn⟩

theorem Degree.FlowCancellation.exists_native_descent_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) (x : M) :
    ∃ p ∈ Smale.ManifoldMorse.criticalPoints E f,
      ∃ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ Smale.ManifoldMorse.criticalPoints E f → f q < f x ∧ f x < f p) := by
  exact
    exists_strict_descent_flow_endpoints F hf.continuous hinj
      (Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx =>
        Smale.FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
          hx)
      x

theorem Degree.FlowCancellation.exists_native_connection_no_return {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q z : M}
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set M,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  exact
    exists_isolated_connection_no_return F hf.continuous hinj
      (Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx => Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx)
      (fun x hx t => Smale.FlowConstruction.flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t) hp hq
      hpq hpair hzband hunique hU hpU hqU hzU

theorem AdaptedWindows.isOpen_minimum_forward_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : MorseCancellation.nativeMorseIndex E f p = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  have hi : Module.finrank ℝ c.NegativeCoordinates = 0 :=
    (MorseCancellation.nativeMorseIndex_eq_chart c).symm.trans hindex
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hi
  obtain ⟨r, hr, -, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have hnear : ∀ᶠ y in 𝓝 p.val, Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val) := by
    filter_upwards [MorseCancellation.morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => S.flow t y) := S.flow.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t y p.val).mp hy

theorem AdaptedWindows.dense_minimum_forward_basins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    Dense
      {x : M |
        ∃ p : Smale.ManifoldMorse.criticalPoints E f,
          MorseCancellation.nativeMorseIndex E f p = 0 ∧
            Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let : Finite (Smale.ManifoldMorse.criticalPoints E f) := S.finite.to_subtype
  let I :=
    { p : Smale.ManifoldMorse.criticalPoints E f // 0 < MorseCancellation.nativeMorseIndex E f p }
  let B := ⋃ p : I, {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)}
  have hm : IsMeagre B :=
    isMeagre_iUnion (fun p : I => S.nonminimum_forward_basin_meagre hf p.val p.property)
  have hd : Dense Bᶜ := dense_of_mem_residual hm
  apply hd.mono
  intro x hx
  obtain ⟨r, hr, p, hp, -, hlim, -⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hi : MorseCancellation.nativeMorseIndex E f p = 0 := by
    by_contra hi
    apply hx
    exact Set.mem_iUnion.mpr ⟨(⟨⟨p, hp⟩, Nat.pos_of_ne_zero hi⟩ : I), hlim⟩
  exact ⟨⟨p, hp⟩, hi, hlim⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_positive_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranch :
      Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < s →
              s < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let d := S.data q
  have h0target : Degree.BeltPassage.lower d.radius 0 u.val v.val ∈ d.chart.splitChart.target := by
    rw [Degree.BeltPassage.lower_zero]
    apply d.block
    constructor
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]
      linarith [d.radius_pos]
    · exact Metric.mem_closedBall_self (by linarith [d.radius_pos])
  have h0value :
    d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius 0 u.val v.val) =
      (d.surgery.attachingSphere u).val := by
    rw [Degree.BeltPassage.lower_zero, d.attaching_eq, d.chart.attachingCoreMap_coe]
  have hc :
    ContinuousAt
      (fun s : ℝ => d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius s u.val v.val))
      0 :=
    (d.chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
          (d.chart.splitChart.open_target.mem_nhds h0target)).comp
      (f := fun s : ℝ => Degree.BeltPassage.lower d.radius s u.val v.val)
      (Degree.BeltPassage.contDiff_lower d.radius u.val v.val).continuous.continuousAt
  have hbasin :
    d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius 0 u.val v.val) ∈
      {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
    rw [h0value]
    exact hbranch
  have hnear := hc.tendsto.eventually ((S.isOpen_minimum_forward_basin hf p hp).mem_nhds hbasin)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨Min.min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs₁ : s ≤ 1 := (hsε.trans_le (min_le_right _ _)).le
  apply (S.belt_passage_forward_limit_iff q hs hs₁ u v p.val).mpr
  apply hδsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
  exact hsε.trans_le (min_le_left _ _)

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_two_sided_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < |s| →
              |s| < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let u' : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 :=
    ⟨-u.val,
      mem_sphere_zero_iff_norm.mpr
        (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp u.property)⟩
  obtain ⟨εp, hεp, hεp1, hplus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u v (hbranches u)
  obtain ⟨εn, hεn, -, hminus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u' v (hbranches u')
  refine ⟨Min.min εp εn, lt_min hεp hεn, (min_le_left _ _).trans hεp1, ?_⟩
  intro s hs hsmall
  by_cases hpos : 0 < s
  · apply hplus s hpos
    rw [abs_of_pos hpos] at hsmall
    exact hsmall.trans_le (min_le_left _ _)
  · have hneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp hs)
    have heq :
      Degree.BeltPassage.upper (S.data q).radius s u.val v.val =
        Degree.BeltPassage.upper (S.data q).radius (-s) u'.val v.val := by
      simpa only [neg_neg] using Degree.BeltPassage.upper_neg (S.data q).radius (-s) u.val v.val
    rw [heq]
    apply hminus (-s) (neg_pos.mpr hneg)
    rw [abs_of_neg hneg] at hsmall
    exact hsmall.trans_le (min_le_right _ _)

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeBeltArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) : M :=
  (S.data q).chart.splitChart.symm (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_coordinates_mem_target {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Degree.BeltPassage.upper (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target :=
  (S.data q).block
    (Degree.BeltPassage.upper_mem_block (S.data q).radius_pos hs
      (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    f (nativeBeltArc S q u v s) = S.toSurgeryWindows.upper q := by
  rw [nativeBeltArc,
    (S.data q).chart.splitChart_inverse_equation
      (nativeBeltArc_coordinates_mem_target S q u v hs)]
  have hh :=
    Degree.BeltPassage.upper_height (S.data q).radius s (mem_sphere_zero_iff_norm.mp u.property)
      (mem_sphere_zero_iff_norm.mp v.property)
  change
    -‖(Degree.BeltPassage.upper (S.data q).radius s u.val v.val).1‖ ^ 2 +
        ‖(Degree.BeltPassage.upper (S.data q).radius s u.val v.val).2‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [Smale.ManifoldMorse.SurgeryWindows.upper]
  linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeBeltArc S q u v 0 = ((S.data q).surgery.beltSphere v).val := by
  rw [nativeBeltArc, Degree.BeltPassage.upper_zero, (S.data q).belt_eq,
    (S.data q).chart.beltCoreMap_coe]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_belt_eq_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v w : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val ↔ s = 0 ∧ v = w := by
  constructor
  · intro heq
    have hzero := nativeBeltArc_coordinates_mem_target S q u w (s := 0) (by simp)
    rw [Degree.BeltPassage.upper_zero] at hzero
    rw [nativeBeltArc, (S.data q).belt_eq, (S.data q).chart.beltCoreMap_coe] at heq
    have hcoords :=
      (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
        (nativeBeltArc_coordinates_mem_target S q u v hs) hzero heq
    have hu : u.val ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp u.property
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hs0 : s = 0 := by
      have hfst : ((S.data q).radius * s) • u.val = 0 := congrArg Prod.fst hcoords
      have hz : (S.data q).radius * s = 0 := (smul_eq_zero.mp hfst).resolve_right hu
      exact (mul_eq_zero.mp hz).resolve_left (S.data q).radius_pos.ne'
    refine ⟨hs0, ?_⟩
    rw [hs0, Degree.BeltPassage.upper_zero] at hcoords
    exact
      Subtype.ext (smul_right_injective _ (S.data q).radius_pos.ne' (congrArg Prod.snd hcoords))
  · rintro ⟨rfl, rfl⟩
    exact nativeBeltArc_zero S q u v

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    Set.InjOn (nativeBeltArc S q u v) (Set.Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have hcoords :=
    (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr hs))
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ht)) hst
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hfst : ((S.data q).radius * s) • u.val = ((S.data q).radius * t) • u.val :=
    congrArg Prod.fst hcoords
  exact mul_left_cancel₀ (S.data q).radius_pos.ne' (smul_left_injective ℝ hu hfst)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (nativeBeltArc S q u v) (Set.Ioo (-1 : ℝ) 1) := by
  apply
    (S.data q).chart.splitChart.contMDiffOn_invFun.comp
      (Degree.BeltPassage.contDiff_upper (S.data q).radius u.val v.val).contMDiff.contMDiffOn
  intro s hs
  exact nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

theorem MorseCancellation.nativeLowerMeridian_coordinates_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    Degree.BeltPassage.lower (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target := by
  have hh :=
    Degree.BeltPassage.upper_mem_block (S.data q).radius_pos
      (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  exact (S.data q).block ⟨hh.2, hh.1⟩

theorem MorseCancellation.nativeLowerMeridian_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    f
        ((S.data q).chart.splitChart.symm
          (Degree.BeltPassage.lower (S.data q).radius s u.val v.val)) =
      S.toSurgeryWindows.lower q := by
  rw [(S.data q).chart.splitChart_inverse_equation
      (nativeLowerMeridian_coordinates_mem_target S q u v s)]
  have hh :=
    Degree.BeltPassage.upper_height (S.data q).radius (s : ℝ)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  change
    -‖(Degree.BeltPassage.lower (S.data q).radius s u.val v.val).2‖ ^ 2 +
        ‖(Degree.BeltPassage.lower (S.data q).radius s u.val v.val).1‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [Smale.ManifoldMorse.SurgeryWindows.lower]
  linarith

def MorseCancellation.nativeLowerMeridianFamily {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    C(unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      (S.data q).LowerLevel)
    where
  toFun
    z :=
    ⟨(S.data q).chart.splitChart.symm
        (Degree.BeltPassage.lower (S.data q).radius z.1 z.2.val v.val),
      nativeLowerMeridian_height S q z.2 v z.1⟩
  continuous_toFun := by
    have hsize :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hdir :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hcoords :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          Degree.BeltPassage.lower (S.data q).radius (z.1 : ℝ) z.2.val v.val) := by
      unfold Degree.BeltPassage.lower
      exact
        ((continuous_const.mul
                  (Real.continuous_sqrt.comp (continuous_const.add (hsize.pow 2)))).smul
              hdir).prodMk
          ((continuous_const.mul hsize).smul continuous_const)
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun z => nativeLowerMeridian_coordinates_mem_target S q z.2 v z.1)).subtype_mk
        _

def MorseCancellation.nativeLowerMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).LowerLevel) :=
  (nativeLowerMeridianFamily S q v).comp ((ContinuousMap.const _ s).prodMk (ContinuousMap.id _))

def MorseCancellation.nativeUpperMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).UpperLevel)
    where
  toFun
    u :=
    ⟨nativeBeltArc S q u v s,
      nativeBeltArc_height S q u v (by rw [abs_of_nonneg s.property.1]; exact s.property.2)⟩
  continuous_toFun := by
    have hcoords :
      Continuous
        (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          Degree.BeltPassage.upper (S.data q).radius (s : ℝ) u.val v.val) := by
      unfold Degree.BeltPassage.upper
      have hneg :
        Continuous
          (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * (s : ℝ)) • u.val) :=
        (continuous_subtype_val :
              Continuous
                (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
                  u.val)).const_smul
          ((S.data q).radius * (s : ℝ))
      have hpos :
        Continuous
          (fun _ : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * Real.sqrt (1 + (s : ℝ) ^ 2)) • v.val) :=
        continuous_const
      exact hneg.prodMk hpos
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun u =>
              nativeBeltArc_coordinates_mem_target S q u v
                (by rw [abs_of_nonneg s.property.1]; exact s.property.2))).subtype_mk
        _

theorem MorseCancellation.nativeLowerMeridian_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeLowerMeridian S q v 0 = (S.data q).surgery.attachingSphere := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm (Degree.BeltPassage.lower (S.data q).radius 0 u.val v.val) =
      _
  rw [Degree.BeltPassage.lower_zero, (S.data q).attaching_eq,
    (S.data q).chart.attachingCoreMap_coe]

theorem MorseCancellation.nativeUpperMeridian_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    S.flow (Degree.BeltPassage.time s) ((nativeUpperMeridian S q v s) u).val =
      ((nativeLowerMeridian S q v s) u).val :=
  S.flow_belt_passage q hs s.property.2 u v

theorem MorseCancellation.nativeLowerMeridian_homotopic_attaching {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    (nativeLowerMeridian S q v s).Homotopic (S.data q).surgery.attachingSphere := by
  let shrink : C(unitInterval, unitInterval) :=
    ⟨fun t => unitInterval.symm t * s, unitInterval.continuous_symm.mul continuous_const⟩
  have h0 : shrink 0 = s := by simp [shrink]
  have h1 : shrink 1 = 0 := by simp [shrink]
  let H : (nativeLowerMeridian S q v s).Homotopy (S.data q).surgery.attachingSphere :=
    { toFun := fun z => nativeLowerMeridianFamily S q v (shrink z.1, z.2)
      continuous_toFun :=
        (nativeLowerMeridianFamily S q v).continuous.comp
          ((shrink.continuous.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := by
        intro u
        rw [h0]
        rfl
      map_one_left := by
        intro u
        rw [h1]
        exact
          congrArg
            (fun g :
                C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                  (S.data q).LowerLevel) =>
              g u)
            (nativeLowerMeridian_zero S q v) }
  exact ⟨H⟩

theorem MorseCancellation.nativeUpperMeridian_avoids_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    nativeUpperMeridian S q v s u ∉ Set.range (S.data q).surgery.beltSphere := by
  rintro ⟨w, hw⟩
  have he :=
    (nativeBeltArc_belt_eq_iff S q u v w
          (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)).mp
      (congrArg Subtype.val hw.symm)
  exact hs.ne' he.1

end Mathoverflow1973
