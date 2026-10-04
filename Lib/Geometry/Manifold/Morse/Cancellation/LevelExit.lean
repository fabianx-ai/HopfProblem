/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement

/-!
# Level exits of the Morse model flow

In a signed Morse chart `c` of `f` at a critical point `p` the descending flow
is the linear model flow `MorseHandle.descentFlow`, and a point with nonzero
positive (resp. negative) coordinate leaves the chart block backward (resp.
forward) through the level `f p + r ^ 2` (resp. `f p - r ^ 2`)
(`exists_backward_morse_quadratic_level_exit`,
`exists_forward_morse_quadratic_level_exit`, and their chart versions
`exists_native_backward_morse_level_exit`,
`exists_native_forward_morse_level_exit`).

Points near `p` exit near the belt sphere (resp. attaching sphere): for an open
set `U` containing the belt core (resp. attaching core), every point in a
neighbourhood of `p` with nonzero positive (resp. negative) coordinate exits
into `U` (`eventually_backward_exit_in_belt_neighborhood`,
`eventually_forward_exit_in_attaching_neighborhood`). The uniform estimate is
`exists_uniform_small_of_zero_set` together with the section neighbourhoods
`exists_upper_morse_section_neighborhood`,
`exists_lower_morse_section_neighborhood`.

These are the local flow facts behind the description of stable and unstable
manifolds of a critical point, cf. Milnor, *Lectures on the h-cobordism
theorem*, §3 and §4.

## Tags

morse-theory, gradient-like-flow, morse-chart
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Level exits in a Morse chart -/

/-- The backward flow exits at a quadratic level. -/
theorem MorseCancellation.exists_backward_morse_quadratic_level_exit {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ}
    (hr : 0 < r) {z : N × P} (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ s : ℝ,
      s < 0 ∧
        MorseHandle.quadratic (MorseHandle.descentFlow s z) = r ^ 2 ∧
          (∀ t ∈ Set.Icc s (0 : ℝ),
              MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(MorseHandle.descentFlow s z).1‖ ≤ ‖z.1‖ := by
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
  have hnorm : ‖(MorseHandle.descentFlow T z).2‖ = R := by
    rw [MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ R hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(MorseHandle.descentFlow t z).1‖ ≤ ‖z.1‖ := by
    rw [MorseHandle.norm_descentFlow_fst]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)
  have hstay (t : ℝ) (ht : t ∈ Set.Icc T (0 : ℝ)) :
    MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r) := by
    constructor
    · exact mem_closedBall_zero_iff.mpr ((hsmall t ht.2).trans (by linarith))
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = R := by rw [hexp, div_mul_cancel₀ R hn.ne']
        _ ≤ 2 * r := by dsimp [R]; linarith
  have hheightT : r ^ 2 < MorseHandle.quadratic (MorseHandle.descentFlow T z) := by
    change
      r ^ 2 <
        -‖(MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr ((hsmall T hT.le).trans_lt hzn)
    dsimp [R]
    nlinarith [sq_pos_of_pos hr]
  have hheight0 : MorseHandle.quadratic (MorseHandle.descentFlow 0 z) < r ^ 2 := by
    rw [Flow.map_zero_apply]
    change -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hzp
    nlinarith [sq_nonneg ‖z.1‖]
  have hc :
    Continuous (fun t : ℝ => MorseHandle.quadratic (MorseHandle.descentFlow t z)) := by
    change
      Continuous
        (fun t : ℝ =>
          -‖(MorseHandle.descentFlow t z).1‖ ^ 2 +
            ‖(MorseHandle.descentFlow t z).2‖ ^ 2)
    exact
      (((MorseHandle.descentFlow.continuous continuous_id continuous_const).fst.norm.pow
              2).neg).add
        ((MorseHandle.descentFlow.continuous continuous_id continuous_const).snd.norm.pow 2)
  obtain ⟨s, hs, hlevel⟩ :=
    intermediate_value_Icc' hT.le hc.continuousOn
      (show
        r ^ 2 ∈
          Set.Icc (MorseHandle.quadratic (MorseHandle.descentFlow 0 z))
            (MorseHandle.quadratic (MorseHandle.descentFlow T z))
        from ⟨hheight0.le, hheightT.le⟩)
  have hs0 : s < 0 :=
    lt_of_le_of_ne hs.2
      (by
        intro heq
        rw [heq] at hlevel
        linarith)
  exact ⟨s, hs0, hlevel, fun t ht => hstay t ⟨hs.1.trans ht.1, ht.2⟩, hsmall s hs0.le⟩

/-- The descent flow swaps the Morse coordinates. -/
theorem MorseCancellation.morse_descentFlow_swap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    MorseHandle.descentFlow t z.swap = (MorseHandle.descentFlow (-t) z).swap := by
  simp only [MorseHandle.descentFlow, neg_neg, Prod.swap]

/-- The quadratic swap of Morse coordinates. -/
theorem MorseCancellation.morse_quadratic_swap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : N × P) :
    MorseHandle.quadratic z.swap = -MorseHandle.quadratic z := by
  change -‖z.2‖ ^ 2 + ‖z.1‖ ^ 2 = -(-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  ring

/-- The forward flow exits at a quadratic level. -/
theorem MorseCancellation.exists_forward_morse_quadratic_level_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ s : ℝ,
      0 < s ∧
        MorseHandle.quadratic (MorseHandle.descentFlow s z) = -(r ^ 2) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s,
              MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(MorseHandle.descentFlow s z).2‖ ≤ ‖z.2‖ := by
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

/-- A uniform small bound off a zero set exists. -/
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
/-- An upper Morse section neighborhood exists. -/
theorem MorseCancellation.exists_upper_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          MorseHandle.quadratic z = r ^ 2 → ‖z.1‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | MorseHandle.quadratic z = r ^ 2}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq MorseHandle.continuous_quadratic continuous_const)
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
    let v : PuncturedHandle.UnitSphere c.PositiveCoordinates :=
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
/-- A lower Morse section neighborhood exists. -/
theorem MorseCancellation.exists_lower_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          MorseHandle.quadratic z = -(r ^ 2) → ‖z.2‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | MorseHandle.quadratic z = -(r ^ 2)}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq MorseHandle.continuous_quadratic continuous_const)
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
    let v : PuncturedHandle.UnitSphere c.NegativeCoordinates :=
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
/-- The native backward flow exits at a level. -/
theorem MorseCancellation.exists_native_backward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
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
  have hcoord : c.splitChart (F T x) = MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        r ^ 2 at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨le_rfl, hT.le⟩

attribute [local instance 100] Classical.propDecidable in
/-- The native forward flow exits at a level. -/
theorem MorseCancellation.exists_native_forward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
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
  have hcoord : c.splitChart (F T x) = MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        -(r ^ 2) at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨hT.le, le_rfl⟩

attribute [local instance 100] Classical.propDecidable in
/-- The backward exit eventually lies in the belt neighborhood. -/
theorem MorseCancellation.eventually_backward_exit_in_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
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
      ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).2 ≠ 0 → ∃ T : ℝ, T < 0 ∧ f (F T x) = f p + r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_upper_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c (lt_min hr hδ) hr] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_backward_morse_level_exit c hV F hF hr hblock hfield hx.1
      (hx.2.1.trans_le (min_le_left _ _)) hx.2.2 hne
  have hq : MorseHandle.quadratic (c.splitChart (F T x)) = r ^ 2 := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = r ^ 2
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.1.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

attribute [local instance 100] Classical.propDecidable in
/-- The forward exit eventually lies in the attaching neighborhood. -/
theorem MorseCancellation.eventually_forward_exit_in_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
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
      ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).1 ≠ 0 → ∃ T : ℝ, 0 < T ∧ f (F T x) = f p - r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_lower_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c hr (lt_min hr hδ)] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_forward_morse_level_exit c hV F hF hr hblock hfield hx.1 hx.2.1
      (hx.2.2.trans_le (min_le_left _ _)) hne
  have hq : MorseHandle.quadratic (c.splitChart (F T x)) = -(r ^ 2) := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = -(r ^ 2)
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.2.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

end
