/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection

/-!
# Cancellation along a transverse connection

The cancellation theorems. `MorseCancellation.cancel_of_transverse_level_isotopy`
starts with an excellent Morse function on a compact finite-dimensional smooth
manifold, a pair of critical points of adjacent index, and an isotopy of a
regular level giving one transverse connecting orbit, and produces a smooth
Morse function whose critical set is the old set minus the pair, with the
germ unchanged outside the isolating band. The module holds the surviving
critical-point control (nowhere-dense critical pieces, quadratic germs, the
native Morse index, the native cancellation data), the band Lyapunov
function (`FlowCancellation.exists_global_band_lyapunov`), the native cubic
cancellation `MorseCancellation.NativeConnectionCancellationData.cancel`,
the transversality of the cancellation data, basin sheets and the Morse
count after pair removal. The connection machinery is imported from
`Morse.Connection`.

## Main definitions and results

* `MorseCancellation.NativeConnectionCancellationData.Transverse`.
* `MorseCancellation.NativeConnectionCancellationData.cancel`.
* `MorseCancellation.cancel_of_transverse_level_isotopy`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4.

## Tags

morse-theory, cancellation, gradient-like-flow, h-cobordism
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

/-! ### The cancelled descent field -/

/-- The cancelled descent field. -/
def MorseCancellation.cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (φ : Model m → ℝ) (p : Model m) :
    Model m :=
  (a ^ 2 - p.1 ^ 2 - 2 * a ^ 2 * φ p, fun i => -σ i * p.2 i)

/-- The cancelled descent field is smooth. -/
theorem MorseCancellation.contDiff_cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (cancelledDescent σ a φ) := by
  unfold cancelledDescent
  fun_prop

/-- The cancelled descent points negatively on the axis. -/
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

/-- The cancelled descent is nonvanishing. -/
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

/-- The cancelled descent's germ off the support. -/
theorem MorseCancellation.cancelledDescent_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    {φ : Model m → ℝ} {p : Model m} (hp : p ∉ tsupport φ) :
    cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  apply Prod.ext
  · simp only [cancelledDescent, cubicDescent, hq, Pi.zero_apply, MulZeroClass.mul_zero, sub_zero]
    ring
  · rfl

/-- A cubic field cancellation exists. -/
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
    exists_compact_smooth_cutoff (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hU
      haxis
  have hone' (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : φ (s, (0 : Fin m → ℝ)) = 1 := by
    have hn : ∀ᶠ p in 𝓝 (s, (0 : Fin m → ℝ)), φ p = 1 :=
      (nhds_le_nhdsSet (show (s, (0 : Fin m → ℝ)) ∈ Set.Icc (-a) a ×ˢ {0} from ⟨hs, rfl⟩)) hone
    exact hn.self_of_nhds
  exact
    ⟨φ, hφ, hc, hsupp, hrange, hone', contDiff_cancelledDescent σ a hφ,
      cancelledDescent_ne_zero σ hσ ha (fun p => (hrange p).1) hone', fun p hp =>
      cancelledDescent_germ_off_support σ a hp⟩

/-- The cubic descent vanishes exactly at the critical point. -/
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

/-- A native cubic field cancellation inside a set exists. -/
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
                            FlowConstruction.partialChartField Φ.symm
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
  let W := FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ)
  have hW :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
      Φ.target :=
    FlowConstruction.contMDiffOn_partialChartField Φ.symm hD
  have hfix (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' tsupport φ) : W x = V x := by
    have hinv : Φ.symm x ∉ tsupport φ := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    have he := (hoff (Φ.symm x) hinv).eq_of_nhds
    rw [hmodel x hx]
    unfold W nativeCubicDescent FlowConstruction.partialChartField
    simp only [VectorField.mpullback_apply, he]
  have hreg (x : M) (hx : x ∈ Φ.target) : W x ≠ 0 := by
    intro hz
    exact hnonzero _ ((partialChartField_zero_iff Φ (cancelledDescent σ a φ) hx).mp hz)
  obtain ⟨V', hV', heq, hzero, hkeep⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement Φ V W hV hW hc hsupp hfix hreg
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
    have hz : FlowConstruction.partialChartField Φ.symm (cubicDescent σ (-(a ^ 2))) x = 0 :=
      (hmodel x hxt).symm.trans hx
    have hd := (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) hxt).mp hz
    rcases (cubicDescent_zero_iff σ hσ a (Φ.symm x)).mp hd with hh | hh
    · exact hxp ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))
    · exact hxq ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))

/-! ### Nowhere-dense critical pieces -/

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

/-! ### Quadratic germs and surviving critical points -/

/-- A surgery pair's band isolation. -/
theorem MorseCancellation.surgery_pair_band_isolation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f,
      f z ∈ Set.Icc (S.lower p) (S.upper q) → z = p.val ∨ z = q.val := by
  intro z hz hband
  by_cases hzp : f z ≤ f p
  · exact Or.inl (S.isolated p z hz ⟨hband.1, hzp.trans (S.value_lt_upper p).le⟩)
  by_cases hqz : f q ≤ f z
  · exact Or.inr (S.isolated q z hz ⟨(S.lower_lt_value q).le.trans hqz, hband.2⟩)
  exact (hconsecutive ⟨z, hz⟩ ⟨lt_of_not_ge hzp, lt_of_not_ge hqz⟩).elim

/-- The surviving critical germs after removing a pair band. -/
theorem MorseCancellation.surviving_critical_germs_of_pair_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {l u : ℝ}
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hexterior : ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f) :
    ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f := by
  intro z hz
  obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
  apply hexterior z
  intro hband
  exact (hpair z hzf ⟨hband.1.le, hband.2.le⟩).elim hzp hzq

/-- The surviving critical points have distinct values. -/
theorem MorseCancellation.distinct_critical_values_of_surviving_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hsub : ManifoldMorse.criticalPoints E g ⊆ ManifoldMorse.criticalPoints E f)
    (hgerms : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) :
    Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  rw [← (hgerms x hx).self_of_nhds, ← (hgerms y hy).self_of_nhds]
  exact hxy

/-- A signed Morse chart of a germ exists. -/
theorem MorseCancellation.exists_signed_morse_chart_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p,
      d.weights = c.weights ∧
        d.chart.source ⊆ c.chart.source ∧
          (∀ x, d.chart x = c.chart x) ∧ ∀ z, d.chart.symm z = c.chart.symm z := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let P := PartialChart.restrictSource c.chart hU
  let d : ManifoldMorse.SignedMorseChart (E := E) g p :=
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

/-- Adapted surgeries after the pair removal. -/
theorem MorseCancellation.adapted_surgeries_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : ManifoldMorse.IsMorse E g)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val)
    (hexterior : ∀ z, f z ∉ Set.Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 z] f) :
    (∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation S p q hconsecutive) hcrit
      hexterior
  have hinj :=
    distinct_critical_values_of_surviving_germs S.distinct (fun z hz => ((hcrit z).mp hz).1) hkeep
  exact ⟨hkeep, hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

attribute [local instance 100] Classical.propDecidable in
/-- The negative rank depends only on the germ. -/
theorem MorseCancellation.signed_morse_chart_negative_finrank_eq_of_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (d : ManifoldMorse.SignedMorseChart (E := E) g p) (hgerm : g =ᶠ[𝓝 p] f) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  obtain ⟨c', hw, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
  have heq := signed_morse_chart_negative_card_eq c' d
  rw [hw] at heq
  simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    MorseHandle.NegativeSpace, finrank_euclideanSpace] using heq

/-! ### The native Morse index -/

/-- The native index depends only on the germ. -/
theorem MorseCancellation.nativeMorseIndex_congr_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hgerm : g =ᶠ[𝓝 p] f) : nativeMorseIndex E g p = nativeMorseIndex E f p := by
  classical
  by_cases h : Nonempty (ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    obtain ⟨d, -, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
    rw [nativeMorseIndex_eq_chart c, nativeMorseIndex_eq_chart d]
    exact (signed_morse_chart_negative_finrank_eq_of_germ c d hgerm).symm
  · have hg : ¬Nonempty (ManifoldMorse.SignedMorseChart (E := E) g p) := by
      rintro ⟨d⟩
      obtain ⟨c, -, -, -, -⟩ := exists_signed_morse_chart_of_germ d hgerm.symm
      exact h ⟨c⟩
    simp only [nativeMorseIndex, dif_neg h, dif_neg hg]

/-- The native index is at most the dimension. -/
theorem MorseCancellation.nativeMorseIndex_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} :
    nativeMorseIndex E f p ≤ Module.finrank ℝ E := by
  classical
  by_cases h : Nonempty (ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    rw [nativeMorseIndex_eq_chart c]
    have hc := c.finrank_negative_add_positive
    omega
  · simp only [nativeMorseIndex, dif_neg h, Nat.zero_le]

/-! ### Native cancellation data -/

/-- A unique descending connection equipped with cubic endpoint charts, a vertical cylinder, and matching slice data. -/
structure MorseCancellation.NativeConnectionCancellationData {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ)
    (p q : M) (m : ℕ) where
  σ : Fin m → ℝ
  signs : ∀ i, σ i = -1 ∨ σ i = 1
  field : (y : M) → TangentSpace 𝓘(ℝ, E) y
  smooth_field :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, field y⟩ : TangentBundle 𝓘(ℝ, E) M))
  flow : Flow ℝ M
  integral : ∀ y, IsMIntegralCurve (fun t => flow t y) field
  zero : ∀ y ∈ ManifoldMorse.criticalPoints E f, field y = 0
  descent : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (field y) < 0
  Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  endpointQ : Φq (-(1 / 2 : ℝ), 0) = q
  endpointP : Φp (1 / 2, 0) = p
  fieldQ : ∀ y ∈ Φq.target, field y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y
  fieldP : ∀ y ∈ Φp.target, field y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y
  A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞
  vertical :
    ∀ y ∈ A.target,
      field y =
        FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y
  speed : ℝ
  positive_speed : 0 < speed
  height : ℝ
  height_formula : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = height - speed * z.2
  Rq : ℝ
  Rp : ℝ
  Tq : ℝ
  Tp : ℝ
  positive_Rq : 0 < Rq
  positive_Rp : 0 < Rp
  boxQ : Metric.closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Φq.source
  boxP : Metric.closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Φp.source
  basinQ :
    ∀ z ∈ Φq.source,
      Filter.Tendsto (fun t => flow t (Φq z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0
  basinP :
    ∀ z ∈ Φp.source,
      Filter.Tendsto (fun t => flow t (Φp z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0
  unique :
    ∀ y,
      Filter.Tendsto (fun t => flow t y) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => flow t y) Filter.atTop (𝓝 p) → ∃ t, flow t (A (0, 0)) = y
  slices : NativeEndpointSliceData σ (1 / 2) Φq Φp A Rq Rp Tq Tp

/-! ### Lyapunov residence bounds -/

/-- A native Lyapunov residence bound exists. -/
theorem FlowCancellation.exists_native_lyapunov_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {C : Set M} (hC : IsCompact C) (hneg : ∀ x ∈ C, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -mvfderiv 𝓘(ℝ, E) f v (V v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
    have hh : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f v (V v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hf.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hf.continuous.continuousOn
  let T := (f q - f p + 1) / δ
  have hpq : f p ≤ f q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = f q - f p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf hγ t
  have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
      hdiff.differentiableOn
      (fun t ht => by
        rw [(hd t).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [Function.comp_apply, sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
  have hhi : f (γ 0) ≤ f q := hmax (hstay 0 h0)
  linarith

/-- Native residence bounds combine. -/
theorem FlowCancellation.combine_native_residence_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {B N U : Set M}
    (houter :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B \ N)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U)
    (hnoreturn :
      ∀ γ : ℝ → M,
        IsMIntegralCurve γ V → ∀ a b : ℝ, γ a ∈ N → γ b ∈ N → ∀ t ∈ Set.Icc a b, γ t ∈ U) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B := by
  obtain ⟨T₀, hT₀, hout⟩ := houter
  obtain ⟨T₁, hT₁, hin⟩ := hinner
  refine ⟨2 * T₀ + T₁, by linarith, ?_⟩
  intro γ hγ
  by_contra! hstay
  obtain ⟨a, ha, haout⟩ := hout γ hγ
  have haN : γ a ∈ N := by
    by_contra haN
    exact haout ⟨hstay a ⟨ha.1, by linarith [ha.2]⟩, haN⟩
  obtain ⟨b, hb, hbout⟩ := hout (γ ∘ (· + (T₀ + T₁))) (hγ.comp_add (T₀ + T₁))
  have hbN : γ (b + (T₀ + T₁)) ∈ N := by
    by_contra hbN
    exact hbout ⟨hstay (b + (T₀ + T₁)) ⟨by linarith [hb.1], by linarith [hb.2]⟩, hbN⟩
  obtain ⟨t, ht, htout⟩ := hin (γ ∘ (· + T₀)) (hγ.comp_add T₀)
  exact
    htout
      (hnoreturn γ hγ a (b + (T₀ + T₁)) haN hbN (t + T₀)
        ⟨by linarith [ha.2, ht.1], by linarith [hb.1, ht.2]⟩)

/-- A perturbed band residence bound exists. -/
theorem FlowCancellation.exists_perturbed_band_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
    {V' : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hV' : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {K N U : Set M}
    (hK : IsClosed K) (hN : IsOpen N) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  have hcompact : IsCompact (f ⁻¹' Set.Icc c d \ N) :=
    ((isClosed_Icc.preimage hf.continuous).inter hN.isClosed_compl).isCompact
  have houter :=
    exists_native_lyapunov_residence hf hV' hcompact
      (by
        intro x hx
        rw [hoff x (fun h => hx.2 (hKN h))]
        exact hneg x hx.1 hx.2)
  exact
    combine_native_residence_bounds houter hinner
      (fun γ hγ a b ha hb =>
        native_no_return_of_supported_perturbation (hV.of_le (by simp)) F hcurve hK hKN hNU hoff
          hnoreturn hγ ha hb)

/-! ### The transverse energy Lyapunov function -/

/-- The transverse energy Lyapunov function. -/
def MorseCancellation.transverseEnergy {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : ℝ :=
  ∑ i, (σ i * p.2 i) ^ 2

/-- The transverse energy is nonnegative. -/
theorem MorseCancellation.transverseEnergy_nonneg {m : ℕ} (σ : Fin m → ℝ) (p : Model m) :
    0 ≤ transverseEnergy σ p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The transverse energy vanishes exactly on the axis. -/
theorem MorseCancellation.transverseEnergy_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : transverseEnergy σ p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    funext i
    have hh :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp h i
        (Finset.mem_univ i)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hh)).resolve_left (hσ i)
  · intro h
    simp [transverseEnergy, h]

/-- The field Lyapunov function. -/
def MorseCancellation.fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) : ℝ :=
  p.1 + k * ∑ i, σ i * p.2 i ^ 2

/-- The field Lyapunov function is smooth. -/
theorem MorseCancellation.contDiff_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) :
    ContDiff ℝ ∞ (fieldLyapunov σ k) := by
  unfold fieldLyapunov
  fun_prop

/-- The field Lyapunov function is differentiable. -/
theorem MorseCancellation.hasFDerivAt_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) :
    HasFDerivAt (fieldLyapunov σ k)
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
        k •
          ∑ i,
            (2 * σ i * p.2 i) •
              ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))
      p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! hx.add (hq.const_mul k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_assoc, mul_comm]

/-- The Lyapunov decay speed of the field. -/
theorem MorseCancellation.fieldLyapunov_speed {m : ℕ} (σ : Fin m → ℝ) (k a : ℝ) (φ : Model m → ℝ)
    (p : Model m) :
    fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) =
      (cancelledDescent σ a φ p).1 - 2 * k * transverseEnergy σ p := by
  rw [(hasFDerivAt_fieldLyapunov σ k p).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change
    (cancelledDescent σ a φ p).1 + k * (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = _
  have hsum :
    (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = -2 * transverseEnergy σ p := by
    rw [transverseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change 2 * σ i * p.2 i * (-σ i * p.2 i) = _
    ring
  rw [hsum]
  ring

/-- A compact field Lyapunov bound exists. -/
theorem MorseCancellation.exists_compact_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) {C : Set (Model m)} (hC : IsCompact C) :
    ∃ k : ℝ,
      0 ≤ k ∧
        ContDiff ℝ ∞ (fieldLyapunov σ k) ∧
          ∀ p ∈ C, fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) < 0 := by
  let O : ℕ → Set (Model m) := fun n =>
    {p | (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0}
  have henergy : Continuous (transverseEnergy σ) := by
    unfold transverseEnergy
    fun_prop
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt
      ((contDiff_cancelledDescent σ a hφ).continuous.fst.sub (continuous_const.mul henergy))
      continuous_const
  have hcover : C ⊆ ⋃ n, O n := by
    intro p hp
    by_cases hz : p.2 = 0
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
      have hh := cancelledDescent_axis_negative σ ha hφnonneg hone p.1
      have hneg : (cancelledDescent σ a φ p).1 < 0 :=
        (congrArg (fun q : Model m => (cancelledDescent σ a φ q).1) he).trans_lt hh
      simpa only [O, Set.mem_ofPred_eq, Nat.cast_zero, MulZeroClass.mul_zero,
        MulZeroClass.zero_mul, sub_zero] using hneg
    · have hpos : 0 < transverseEnergy σ p :=
        lt_of_le_of_ne (transverseEnergy_nonneg σ p)
          (Ne.symm (fun he => hz ((transverseEnergy_zero_iff σ hσ p).mp he)))
      obtain ⟨n, hn⟩ := exists_nat_gt ((cancelledDescent σ a φ p).1 / (2 * transverseEnergy σ p))
      have hh := (div_lt_iff₀ (mul_pos (by norm_num) hpos)).mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0
      nlinarith
  have hmono : Monotone O := by
    intro i j hij p hp
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have he := transverseEnergy_nonneg σ p
    change (cancelledDescent σ a φ p).1 - 2 * (i : ℝ) * transverseEnergy σ p < 0 at hp
    change (cancelledDescent σ a φ p).1 - 2 * (j : ℝ) * transverseEnergy σ p < 0
    nlinarith
  obtain ⟨n, hn⟩ :=
    hC.elim_directed_cover O hO hcover
      (fun i j => ⟨Max.max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨n, by positivity, contDiff_fieldLyapunov σ n, ?_⟩
  intro p hp
  rw [fieldLyapunov_speed]
  exact hn hp

/-- A compact Lyapunov residence bound exists. -/
theorem MorseCancellation.exists_compact_lyapunov_residence {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W)
    {C : Set D} (hC : IsCompact C) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → D,
          (∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ C → HasDerivAt γ (W (γ t)) t) →
            ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed : Continuous (fun x => fderiv ℝ L x (W x)) :=
    (hL.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hW)
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -fderiv ℝ L v (W v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : D) (hx : x ∈ C) : fderiv ℝ L x (W x) ≤ -δ := by
    have hh : fderiv ℝ L x (W x) ≤ fderiv ℝ L v (W v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hL.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hL.continuous.continuousOn
  let T := (L q - L p + 1) / δ
  have hpq : L p ≤ L q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = L q - L p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun u => L (γ u)) (fderiv ℝ L (γ t) (W (γ t))) t :=
    (hL.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t ht (hstay t ht))
  have hcont : ContinuousOn (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).differentiableAt.differentiableWithinAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hcont (hdiff.mono interior_subset)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : L p ≤ L (γ T) := hmin (hstay T hlast)
  have hhi : L (γ 0) ≤ L q := hmax (hstay 0 h0)
  linarith

/-- A partial chart integral curve's derivative. -/
theorem MorseCancellation.hasDerivAt_partialChart_integralCurve {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, D) M D ∞) (W : D → D)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ}
    (ht : γ t ∈ e.source) (hV : V (γ t) = FlowConstruction.partialChartField e W (γ t)) :
    HasDerivAt (e ∘ γ) (W (e (γ t))) t := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, D) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hinv := he.comp_symm_deriv (e'.map_source ht)
  rw [e'.left_inv ht] at hinv
  have hd := (he.mdifferentiableAt ht).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D) e (γ t) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) •
        (NormedSpace.fromTangentSpace (e (γ t))).symm (W (e (γ t)))
  rw [map_smul, hV, FlowConstruction.partialChartField_eq_mfderiv_symm e W ht]
  have hv := congrArg (fun A : D →L[ℝ] D => A (W (e (γ t)))) hinv
  exact congrArg (fun v => (NormedSpace.fromTangentSpace t r) • v) hv

/-- A native compact Lyapunov residence bound exists. -/
theorem MorseCancellation.exists_native_compact_lyapunov_residence {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W) {C : Set D}
    (hC : IsCompact C) (hsource : C ⊆ Φ.source) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ∀ x ∈ Φ '' C, V x = FlowConstruction.partialChartField Φ.symm W x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨T, hT, hTbound⟩ := exists_compact_lyapunov_residence hL hW hC hneg
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hcoords (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : Φ.symm (γ t) ∈ C := by
    obtain ⟨z, hz, he⟩ := hstay t ht
    have hh : Φ.symm (Φ z) = z := Φ.left_inv' (hsource hz)
    rw [← he, hh]
    exact hz
  obtain ⟨t, ht, hout⟩ :=
    hTbound (Φ.symm ∘ γ)
      (fun t ht _ =>
        hasDerivAt_partialChart_integralCurve Φ.symm W hγ
          (by
            obtain ⟨z, hz, he⟩ := hstay t ht
            exact he ▸ Φ.map_source' (hsource hz))
          (hV (γ t) (hstay t ht)))
  exact hout (hcoords t ht)

/-- A cancelled-descent residence bound exists. -/
theorem MorseCancellation.exists_native_cancelledDescent_residence_bound {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    {C : Set (Model m)} (hC : IsCompact C) (hsource : C ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV :
      ∀ x ∈ Φ '' C,
        V x = FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨k, -, hL, hneg⟩ := exists_compact_fieldLyapunov σ hσ ha hφ hφnonneg hone hC
  exact
    exists_native_compact_lyapunov_residence Φ hL (contDiff_cancelledDescent σ a hφ).continuous hC
      hsource hneg hV

/-- A native cubic field has finite passage time. -/
theorem MorseCancellation.exists_native_cubic_field_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {N U : Set M} (hN : IsOpen N)
    (hNU : N ⊆ U) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) {C : Set (Model m)}
    (hC : IsCompact C) (hCΦ : C ⊆ Φ.source) (hUC : U ⊆ Φ '' C)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ N ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                ∃ T : ℝ,
                  0 < T ∧
                    ∀ γ : ℝ → M,
                      IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  obtain ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, hzero, hkeep⟩ :=
    exists_native_cubic_field_cancellation_in σ hσ ha Φ haxis V hV hmodel hN haxisN
  have hK : IsCompact (Φ '' tsupport φ) :=
    hc.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsupp)
  obtain ⟨T₀, hT₀, hres⟩ :=
    exists_native_cancelledDescent_residence_bound σ hσ ha Φ hφ (fun p => (hrange p).1) hone hC
      hCΦ
      (fun x hx =>
        heq x
          (by
            obtain ⟨z, hz, rfl⟩ := hx
            exact Φ.map_source' (hCΦ hz)))
  have hinner :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U := by
    refine ⟨T₀, hT₀, ?_⟩
    intro γ hγ
    obtain ⟨t, ht, hout⟩ := hres γ hγ
    exact ⟨t, ht, fun h => hout (hUC h)⟩
  refine ⟨Φ '' tsupport φ, V', hK, hsuppN, hV', hzero, hkeep, ?_⟩
  exact
    FlowCancellation.exists_perturbed_band_residence hf hV hV' F hcurve hK.isClosed hN
      hsuppN hNU (fun x hx => (hkeep x hx).self_of_nhds) hneg hnoreturn hinner

/-! ### The cubic axis flow -/

/-- The native cubic axis flow. -/
theorem MorseCancellation.native_cubic_axis_flow {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    F t (Φ (0, 0)) = Φ (cubicModelOrbit a t) := by
  have hmem (s : ℝ) : cubicModelOrbit a s ∈ Φ.source := by
    have hs := cubicAxisParameter_mem ha s
    exact haxis ⟨⟨hs.1.le, hs.2.le⟩, rfl⟩
  have hΓ : IsMIntegralCurve (Φ ∘ cubicModelOrbit a) V := by
    intro s
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
        (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicModelOrbit σ a s) (hmem s)
    have he := hmodel (Φ (cubicModelOrbit a s)) (Φ.map_source' (hmem s))
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ ∘ cubicModelOrbit a) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (nativeCubicDescent σ Φ (-(a ^ 2)) (Φ (cubicModelOrbit a s)))) at hd
    rw [← he] at hd
    exact hd
  have hinit : F 0 (Φ (0, 0)) = (Φ ∘ cubicModelOrbit a) 0 := by
    simp only [F.map_zero_apply, Function.comp_apply, cubicModelOrbit_zero]
    rfl
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve (Φ (0, 0))) hΓ hinit
  exact congrFun heq t

/-- The native cubic axis orbit. -/
theorem MorseCancellation.native_cubic_axis_orbit {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Set.range (fun t : ℝ => F t (Φ (0, 0))) = Φ '' (Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)}) ∧
      Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atTop (𝓝 (Φ (a, 0))) ∧
        Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atBot (𝓝 (Φ (-a, 0))) := by
  have heq : (fun t : ℝ => F t (Φ (0, 0))) = Φ ∘ cubicModelOrbit a :=
    funext (native_cubic_axis_flow σ ha Φ haxis hV hmodel F hcurve)
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.range_comp, range_cubicModelOrbit ha]
  · exact
      (Φ.mdifferentiableAt (by simp) hp).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atTop ha)
  · exact
      (Φ.mdifferentiableAt (by simp) hq).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atBot ha)

/-- The native cubic closed axis. -/
theorem MorseCancellation.native_cubic_closed_axis {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Φ '' (Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}) =
      Insert.insert (Φ (a, 0))
        (Insert.insert (Φ (-a, 0)) (Set.range (fun t : ℝ => F t (Φ (0, 0))))) := by
  rw [(native_cubic_axis_orbit σ ha Φ haxis hV hmodel F hcurve).1]
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsright : s = a
    · exact Or.inl (congrArg (fun r => Φ (r, 0)) hsright)
    by_cases hsleft : s = -a
    · exact Or.inr (Or.inl (congrArg (fun r => Φ (r, 0)) hsleft))
    · exact
        Or.inr
          (Or.inr
            ⟨(s, 0), ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hsleft), lt_of_le_of_ne hs.2 hsright⟩, rfl⟩,
              rfl⟩)
  · rintro (hx | hx | hx)
    · exact ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, hx.symm⟩
    · exact ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, hx.symm⟩
    · obtain ⟨⟨s, z⟩, ⟨hs, hz⟩, he⟩ := hx
      exact ⟨(s, z), ⟨⟨hs.1.le, hs.2.le⟩, hz⟩, he⟩

/-! ### Band crossings -/

/-- A uniform directed band crossing exists. -/
theorem FlowCancellation.exists_uniform_directed_band_crossing {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x) := by
  obtain ⟨T, hT, hexit⟩ := hres
  have hforward : ∀ x, f x ≤ d → f (F T x) < c := by
    intro x hx
    obtain ⟨t, ht, hout⟩ := hexit x
    have hhi := forwardInvariant_sublevel_of_boundary F hf hD hder hupper x hx t ht.1
    have hlo : f (F t x) < c := lt_of_not_ge (fun h => hout ⟨h, hhi⟩)
    rcases ht.2.eq_or_lt with he | he
    · simpa only [he] using hlo
    · have hh :=
        strict_sublevel_entry_of_boundary F hf hD hder hlower (F t x) hlo.le (T - t)
          (sub_pos.mpr he)
      simpa only [← F.map_add, sub_add_cancel] using hh
  refine ⟨T, hT, hforward, ?_⟩
  intro x hx
  apply lt_of_not_ge
  intro hback
  have hh := hforward (F (-T) x) hback
  rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
  exact (not_lt_of_ge hx) hh

/-- The band entry time is continuous. -/
theorem FlowCancellation.continuousOn_band_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  obtain ⟨T, hT, hforward, -⟩ :=
    exists_uniform_directed_band_crossing F hf hD hder hlower hupper hres
  have hclosed : IsClosed {x | f x ≤ c} := isClosed_le hf continuous_const
  have hentry : ∀ x ∈ {y | f y ≤ c}, ∀ t : ℝ, 0 < t → F t x ∈ interior {y | f y ≤ c} := by
    intro x hx t ht
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hlower x hx t ht
    exact
      Eq.mpr
        (congrArg (fun S : Set X => F t x ∈ S)
          (interior_sublevel_eq_of_boundary F hf hder hlower))
        hh
  exact
    FlowConstruction.continuousOn_entryTime F hclosed
      (forwardInvariant_sublevel_of_boundary F hf hD hder hlower) hentry
      (fun x hx => ⟨T, hT.le, (hforward x hx).le⟩)

/-- A native flow band crossing exists. -/
theorem FlowCancellation.exists_native_flow_band_crossing {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {c d : ℝ} (hlower : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hupper : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hres :
      ∃ T : ℝ,
        0 < T ∧
          ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) :
    ∃ F : Flow ℝ M,
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
        (∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) ∧
          ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let F := FlowConstruction.compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V :=
    FlowConstruction.isMIntegralCurve_compactFlow hV₁ x
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hres' : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d := by
    obtain ⟨T, hT, hbound⟩ := hres
    exact ⟨T, hT, fun x => hbound (fun t => F t x) (hcurve x)⟩
  exact
    ⟨F, hcurve, exists_uniform_directed_band_crossing F hf.continuous hD hder hlower hupper hres',
      continuousOn_band_entryTime F hf.continuous hD hder hlower hupper hres'⟩

/-- A cubic connection has finite passage. -/
theorem MorseCancellation.exists_cubic_connection_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                (∃ T : ℝ,
                    0 < T ∧
                      ∀ γ : ℝ → M,
                        IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) ∧
                  ∃ G : Flow ℝ M,
                    (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
                      (∃ T : ℝ,
                          0 < T ∧
                            (∀ x, f x ≤ d → f (G T x) < c) ∧ ∀ x, c ≤ f x → d < f (G (-T) x)) ∧
                        ContinuousOn (FlowConstruction.entryTime G {x | f x ≤ c})
                          {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  obtain ⟨hrange, htop, hbot⟩ := native_cubic_axis_orbit σ ha Φ haxis hV₁ hmodel F hcurve
  have hclosed := native_cubic_closed_axis σ ha Φ haxis hV₁ hmodel F hcurve
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc (Φ (0, 0))
  have hztop := hf.continuous.continuousAt.tendsto.comp htop
  have hzbot := hf.continuous.continuousAt.tendsto.comp hbot
  have hzband (t : ℝ) : f (F t (Φ (0, 0))) ∈ Set.Icc (f (Φ (a, 0))) (f (Φ (-a, 0))) :=
    ⟨hmono.le_of_tendsto hztop t, hmono.ge_of_tendsto hzbot t⟩
  let A := Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}
  have hAband : Φ '' A ⊆ f ⁻¹' Set.Ioo c d := by
    intro x hx
    rw [hclosed] at hx
    rcases hx with hx | hx | ⟨t, ht⟩
    · rw [hx]
      exact ⟨hc, lt_trans hpq hd⟩
    · rw [hx]
      exact ⟨lt_trans hc hpq, hd⟩
    · rw [← ht]
      exact ⟨lt_of_lt_of_le hc (hzband t).1, lt_of_le_of_lt (hzband t).2 hd⟩
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d)) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_Ioo.preimage hf.continuous)
  have hAsub : A ⊆ Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d) := fun x hx =>
    ⟨haxis hx, hAband ⟨x, hx, rfl⟩⟩
  obtain ⟨C, hC, hAC, hCsub⟩ :=
    exists_compact_between
      (show IsCompact A from CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hopen hAsub
  have hCΦ : C ⊆ Φ.source := fun x hx => (hCsub hx).1
  let U := Φ '' interior C
  have hU : IsOpen U :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (fun x hx => hCΦ (interior_subset hx))
  have hAU : Φ '' A ⊆ U := Set.image_mono hAC
  have hpU : Φ (a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
  have hqU : Φ (-a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
  have hzU (t : ℝ) : F t (Φ (0, 0)) ∈ U := by
    apply hAU
    rw [hclosed]
    exact Or.inr (Or.inr ⟨t, rfl⟩)
  obtain ⟨N, hN, hNU, hpN, hqN, hzN, hnoreturn⟩ :=
    FlowCancellation.exists_native_connection_no_return hf hV F hcurve hzero hdesc hinj hp
      hq hpq (fun x hx hh => hpair x hx ⟨le_trans hc.le hh.1, le_trans hh.2 hd.le⟩) hzband hunique
      hU hpU hqU hzU
  have haxisN (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : Φ (s, (0 : Fin m → ℝ)) ∈ N := by
    have hh : Φ (s, (0 : Fin m → ℝ)) ∈ Φ '' A := ⟨(s, 0), ⟨hs, rfl⟩, rfl⟩
    rw [hclosed] at hh
    rcases hh with hh | hh | ⟨t, ht⟩
    · exact hh ▸ hpN
    · exact hh ▸ hqN
    · exact ht ▸ hzN t
  have hneg (x : M) (hx : f x ∈ Set.Icc c d) (hout : x ∉ N) : mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    apply hdesc x
    intro hcrit
    rcases hpair x hcrit hx with he | he
    · exact hout (he ▸ hpN)
    · exact hout (he ▸ hqN)
  obtain ⟨K, V', hK, hKN, hV', hzeros, hkeep, hpass⟩ :=
    exists_native_cubic_field_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hN hNU haxisN
      hC hCΦ (Set.image_mono interior_subset) hneg hnoreturn
  have hKsub : K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hNU (hKN hx)
    exact ⟨Φ.map_source' (hCΦ (interior_subset hz)), (hCsub (interior_subset hz)).2⟩
  have hcd : c ≤ d := by linarith
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd⟩
        · exact ⟨hcd, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  refine ⟨K, V', hK, hKsub, hV', hzeros, hkeep, hpass, ?_⟩
  exact
    FlowCancellation.exists_native_flow_band_crossing hf hV'
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hpass

/-- A function along a native integral curve differentiates at a point. -/
theorem FlowCancellation.hasDerivAt_comp_native_integralCurve_at {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ t)) (hγ : IsMIntegralCurve γ V) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t := by
  have hd := hf.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (V (γ t))
  exact map_smul _ _ _

/-- The manifold derivative of the signed level time. -/
theorem FlowCancellation.mvfderiv_signedLevelTime {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hx : x ∈ levelBasin F f c) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 := by
  obtain ⟨hB, hsmooth, hshift⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  have hlocal := (hsmooth x hx).contMDiffAt (hB.mem_nhds hx)
  have hlocal0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (signedLevelTime F f c) (F 0 x) := by
    rw [F.map_zero_apply]
    exact hlocal.mdifferentiableAt (by simp)
  have hd := hasDerivAt_comp_native_integralCurve_at hlocal0 (hcurve x)
  have heq :
    (signedLevelTime F f c ∘ (fun t => F t x)) = fun t : ℝ => signedLevelTime F f c x - t :=
    funext (hshift x hx)
  rw [heq] at hd
  have hh := hd.unique ((hasDerivAt_id (0 : ℝ)).const_sub (signedLevelTime F f c x))
  have he :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) y (V y)) (F.map_zero_apply x)
  exact he.symm.trans hh

/-- The basin of a band crossing. -/
def FlowCancellation.crossingBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) : Set X :=
  levelBasin F f c ∩ levelBasin F f d

/-- The duration of a band crossing. -/
def FlowCancellation.crossingDuration {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  signedLevelTime F f c x - signedLevelTime F f d x

/-- The height of the flow band. -/
def FlowCancellation.flowBandHeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x

/-- The crossing duration is positive. -/
theorem FlowCancellation.crossingDuration_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hcd : c < d) {x : X} (hx : x ∈ crossingBasin F f c d) :
    0 < crossingDuration F f c d x := by
  apply sub_pos.mpr
  by_contra h
  have hle := le_of_not_gt h
  have hh :=
    forwardInvariant_sublevel_of_boundary F hf hD hder hc (F (signedLevelTime F f c x) x)
      (signedLevelTime_hits F f c hx.1).le (signedLevelTime F f d x - signedLevelTime F f c x)
      (sub_nonneg.mpr hle)
  rw [← F.map_add, sub_add_cancel, signedLevelTime_hits F f d hx.2] at hh
  exact (not_le_of_gt hcd) hh

/-- The crossing duration under the flow. -/
theorem FlowCancellation.crossingDuration_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    crossingDuration F f c d (F s x) = crossingDuration F f c d x := by
  simp only [crossingDuration, signedLevelTime_flow F hf hD hder hc hx.1 s,
    signedLevelTime_flow F hf hD hder hd hx.2 s]
  ring

/-- The band height under the flow. -/
theorem FlowCancellation.flowBandHeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    flowBandHeight F f c d (F s x) =
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * s := by
  simp only [flowBandHeight, crossingDuration_flow F hf hD hder hc hd hx s,
    signedLevelTime_flow F hf hD hder hc hx.1 s]
  ring

/-- The band height's lower bound. -/
theorem FlowCancellation.flowBandHeight_lower {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : flowBandHeight F f c d x = c := by
  simp only [flowBandHeight, signedLevelTime_eq_zero F hf hD hder hc hx, MulZeroClass.mul_zero,
    zero_div, add_zero]

/-- The band height's upper bound. -/
theorem FlowCancellation.flowBandHeight_upper {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) (hcd : c < d) {x : X}
    (hx : x ∈ crossingBasin F f c d) (hfx : f x = d) : flowBandHeight F f c d x = d := by
  have hz := signedLevelTime_eq_zero F hf hD hder hd hfx
  have hpos := crossingDuration_pos F hf hD hder hc hcd hx
  have heq : signedLevelTime F f c x = crossingDuration F f c d x := by
    simp only [crossingDuration, hz, sub_zero]
  rw [flowBandHeight, heq, mul_div_cancel_right₀ _ hpos.ne']
  ring

/-- The band height is smooth. -/
theorem FlowCancellation.smooth_flowBandHeight {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (crossingBasin F f c d) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) ∧
        ∀ x ∈ crossingBasin F f c d,
          mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
              -((d - c) / crossingDuration F f c d x) ∧
            mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) < 0 := by
  obtain ⟨hBc, htc, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  obtain ⟨hBd, htd, -⟩ := smooth_signed_level_time hf hV F hcurve hd
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hB : IsOpen (crossingBasin F f c d) := hBc.inter hBd
  have hpos (x : M) (hx : x ∈ crossingBasin F f c d) : 0 < crossingDuration F f c d x :=
    crossingDuration_pos F hf.continuous hD hder hc hcd hx
  have hsc := htc.mono (Set.inter_subset_left : crossingBasin F f c d ⊆ levelBasin F f c)
  have hsd := htd.mono (Set.inter_subset_right : crossingBasin F f c d ⊆ levelBasin F f d)
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossingDuration F f c d) (crossingBasin F f c d) :=
    hsc.sub hsd
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) :=
    contMDiffOn_const.add ((contMDiffOn_const.mul hsc).div₀ hA (fun x hx => (hpos x hx).ne'))
  refine ⟨hB, hg, ?_⟩
  intro x hx
  have hlocal : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (flowBandHeight F f c d) (F 0 x) := by
    rw [F.map_zero_apply]
    exact ((hg x hx).contMDiffAt (hB.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_comp_native_integralCurve_at hlocal (hcurve x)
  have heq :
    (flowBandHeight F f c d ∘ (fun t => F t x)) = fun t =>
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * t :=
    funext (fun t => flowBandHeight_flow F hf.continuous hD hder hc hd hx t)
  rw [heq] at hchain
  have hline :=
    ((hasDerivAt_id (0 : ℝ)).const_mul ((d - c) / crossingDuration F f c d x)).const_sub
      (flowBandHeight F f c d x)
  have hnative :
    mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) = -((d - c) / crossingDuration F f c d x) :=
    by
    have he :=
      congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) y (V y))
        (F.map_zero_apply x)
    exact he.symm.trans (by simpa using hchain.unique hline)
  exact ⟨hnative, hnative ▸ neg_neg_of_pos (div_pos (sub_pos.mpr hcd) (hpos x hx))⟩

/-! ### The logarithmic coordinate -/

/-- The logarithmic coordinate of a positive height. -/
def FlowCancellation.logarithmicCoordinate (η L t : ℝ) : ℝ :=
  Real.log (1 + (t / η) ^ 2) / L

/-- The logarithmic coordinate is smooth. -/
theorem FlowCancellation.contDiff_logarithmicCoordinate (η L : ℝ) :
    ContDiff ℝ ∞ (logarithmicCoordinate η L) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.add ((contDiff_id.div_const η).pow 2)
  · intro t
    positivity

/-- The logarithmic coordinate's derivative. -/
theorem FlowCancellation.hasDerivAt_logarithmicCoordinate {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) :
    HasDerivAt (logarithmicCoordinate η L) (2 * t / (L * (η ^ 2 + t ^ 2))) t := by
  have hp : 1 + (t / η) ^ 2 ≠ 0 := by positivity
  have hh := (((((hasDerivAt_id t).div_const η).pow 2).const_add 1).log hp).div_const L
  convert hh using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

/-- The weighted derivative bound of the logarithmic coordinate. -/
theorem FlowCancellation.logarithmicCoordinate_weighted_deriv_bound {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) : |t * deriv (logarithmicCoordinate η L) t| ≤ 2 / L := by
  rw [(hasDerivAt_logarithmicCoordinate hη hL t).deriv]
  have hden : 0 < η ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) (sq_nonneg t)
  have heq : t * (2 * t / (L * (η ^ 2 + t ^ 2))) = (2 / L) * (t ^ 2 / (η ^ 2 + t ^ 2)) := by
    field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hden).mpr (by nlinarith))

/-- A logarithmic cutoff exists. -/
theorem FlowCancellation.exists_logarithmic_cutoff {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          (∀ᶠ t in 𝓝 0, χ t = 1) ∧
            (∀ t, ε ≤ |t| → χ t = 0) ∧
              (∀ t, χ t ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ t, |t * deriv χ t| < δ := by
  obtain ⟨β, hβ, hcompact, hsupp, hone, hrange⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : ℝ)}) (U := Metric.ball 0 1) isCompact_singleton
      Metric.isOpen_ball (by simp)
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous (hβ.continuous_deriv (by simp))
  let B : ℝ := Max.max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (t : ℝ) : |deriv β t| ≤ B := by
    have hh := hC t
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [B]; linarith [le_max_left C 0])
  let L : ℝ := 2 * B / δ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : B * (2 / L) < δ := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    have hd : δ * (2 * B / δ) = 2 * B := by field_simp
    nlinarith
  let η : ℝ := ε / Real.exp L
  have hη : 0 < η := div_pos hε (Real.exp_pos L)
  let q := logarithmicCoordinate η L
  have hq : ContDiff ℝ ∞ q := contDiff_logarithmicCoordinate η L
  have hqzero : q 0 = 0 := by simp [q, logarithmicCoordinate]
  let χ : ℝ → ℝ := β ∘ q
  have hχ : ContDiff ℝ ∞ χ := hβ.comp hq
  have hout (t : ℝ) (ht : ε ≤ |t|) : χ t = 0 := by
    have hratio : Real.exp L ≤ |t / η| := by
      rw [abs_div, abs_of_pos hη, le_div_iff₀ hη]
      have he : Real.exp L * η = ε := by dsimp [η]; field_simp
      simpa only [he] using ht
    have heone : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL.le
    have hlower : L ≤ Real.log (1 + (t / η) ^ 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      nlinarith [sq_abs (t / η)]
    have honeq : 1 ≤ q t := (le_div_iff₀ hL).mpr (by simpa using hlower)
    have hnotsupp : q t ∉ tsupport β := by
      intro hh
      have hball := hsupp hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hball
      linarith [hball.2]
    change β (q t) = 0
    exact image_eq_zero_of_notMem_tsupport hnotsupp
  have hcompactχ : HasCompactSupport χ := by
    apply HasCompactSupport.intro (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro t ht
    apply hout
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨hh.1.le, hh.2.le⟩
  have hnear : ∀ᶠ t in 𝓝 0, χ t = 1 := by
    have hb : ∀ᶠ r in 𝓝 (0 : ℝ), β r = 1 := by simpa only [nhdsSet_singleton] using hone
    have ht : Filter.Tendsto q (𝓝 0) (𝓝 0) := by
      have hh : Filter.Tendsto q (𝓝 0) (𝓝 (q 0)) := hq.continuous.continuousAt
      simpa only [hqzero] using hh
    exact ht.eventually hb
  refine ⟨χ, hχ, hcompactχ, hnear, hout, fun t => hrange (q t), ?_⟩
  intro t
  have hder : deriv χ t = deriv β (q t) * deriv q t :=
    ((hβ.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
        (hq.differentiable (by simp)).differentiableAt.hasDerivAt).deriv
  rw [hder]
  have he : |t * (deriv β (q t) * deriv q t)| = |deriv β (q t)| * |t * deriv q t| := by
    rw [← abs_mul]; congr 1; ring
  rw [he]
  exact
    lt_of_le_of_lt
      (mul_le_mul (hbound _) (logarithmicCoordinate_weighted_deriv_bound hη hL t) (abs_nonneg _)
        hB.le)
      hsmall

/-- A nonnegative function vanishing at a point has zero derivative. -/
theorem FlowCancellation.deriv_eq_zero_of_nonneg_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (hnonneg : ∀ t, 0 ≤ χ t) {t : ℝ} (ht : χ t = 0) : deriv χ t = 0 := by
  have hm : IsLocalMin χ t :=
    Filter.Eventually.of_forall
      (fun s => by
        change χ t ≤ χ s
        rw [ht]
        exact hnonneg s)
  exact hm.hasDerivAt_eq_zero (hχ t).hasDerivAt

/-- The weighted blend is negative. -/
theorem FlowCancellation.weighted_blend_neg {α a b r s z μ C δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (ha : a ≤ -μ) (hb : b ≤ -μ) (hC : 0 ≤ C) (hr : |r| ≤ C * |s|)
    (hz : |s * z| ≤ δ) (hsmall : C * δ < μ) : b + α * (a - b) - z * r < 0 := by
  have hbase : b + α * (a - b) ≤ -μ := by
    nlinarith [mul_nonneg hα.1 (sub_nonneg.mpr ha),
      mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hb)]
  have herr : |z * r| ≤ C * δ :=
    calc
      |z * r| = |z| * |r| := abs_mul _ _
      _ ≤ |z| * (C * |s|) := (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
      _ = C * |s * z| := by rw [abs_mul]; ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hz hC
  linarith [neg_abs_le (z * r)]

/-- The flow height's derivative at a critical point is zero. -/
theorem FlowCancellation.hasDerivAt_flow_height_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (F : Flow ℝ M)
    (hcurve : IsMIntegralCurve (fun t => F t x) V) :
    HasDerivAt (fun t => f (F t x)) (mvfderiv 𝓘(ℝ, E) f x (V x)) 0 := by
  have hf0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (F 0 x) := by
    rw [F.map_zero_apply]
    exact hf
  have hh := hasDerivAt_comp_native_integralCurve_at hf0 hcurve
  have he := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  exact he ▸ hh

/-! ### The descent blend -/

/-- The descent blend of two Lyapunov functions. -/
def FlowCancellation.descentBlend {M : Type*} (χ : ℝ → ℝ) (θ f g : M → ℝ) (x : M) : ℝ :=
  g x + χ (θ x) * (f x - g x)

/-- The descent blend's manifold derivative. -/
theorem FlowCancellation.mvfderiv_descentBlend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {χ : ℝ → ℝ} {θ f g : M → ℝ} {x : M}
    (hχ : ContDiff ℝ ∞ χ) (hθ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ x)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V)
    (htime : mvfderiv 𝓘(ℝ, E) θ x (V x) = -1) :
    mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) =
      mvfderiv 𝓘(ℝ, E) g x (V x) +
          χ (θ x) * (mvfderiv 𝓘(ℝ, E) f x (V x) - mvfderiv 𝓘(ℝ, E) g x (V x)) -
        deriv χ (θ x) * (f x - g x) := by
  have dθ := hasDerivAt_flow_height_zero (hθ.mdifferentiableAt (by simp)) F hcurve
  have df := hasDerivAt_flow_height_zero (hf.mdifferentiableAt (by simp)) F hcurve
  have dg := hasDerivAt_flow_height_zero (hg.mdifferentiableAt (by simp)) F hcurve
  rw [htime] at dθ
  have dχ := ((hχ.differentiable (by simp)) (θ (F 0 x))).hasDerivAt.comp 0 dθ
  have db := dg.add (dχ.mul (df.sub dg))
  have hb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (descentBlend χ θ f g) x :=
    hg.add ((hχ.contMDiff.contMDiffAt.comp x hθ).mul (hf.sub hg))
  have dn := hasDerivAt_flow_height_zero (hb.mdifferentiableAt (by simp)) F hcurve
  have he := dn.unique db
  simp only [Pi.sub_apply, Function.comp_apply, F.map_zero_apply] at he
  exact he.trans (by ring)

/-- A native descent blend exists. -/
theorem FlowCancellation.exists_native_descent_blend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {θ f g : M → ℝ}
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (htime : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) θ x (V x) = -1)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {ε μ C : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hC : 0 ≤ C)
    (hcollar :
      ∀ x ∈ U,
        |θ x| < ε →
          mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
            mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |θ x|) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x ∈ U, θ x = 0 → b =ᶠ[𝓝 x] f) ∧
            (∀ x, ε ≤ |θ x| → b x = g x) ∧ ∀ x ∈ U, ε < |θ x| → b =ᶠ[𝓝 x] g := by
  let δ := μ / (C + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  have hsmall : C * δ < μ := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  obtain ⟨χ, hχ, -, hone, hzero, hrange, hweight⟩ := exists_logarithmic_cutoff hε hδ
  let b := descentBlend χ θ f g
  have hb : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U :=
    hg.add ((hχ.contMDiff.comp_contMDiffOn hθ).mul (hf.sub hg))
  have hout (x : M) (hx : ε ≤ |θ x|) : b x = g x := by
    simp only [b, descentBlend, hzero _ hx, MulZeroClass.zero_mul, add_zero]
  refine ⟨b, hb, ?_, ?_, hout, ?_⟩
  · intro x hx
    have hder :=
      mvfderiv_descentBlend hχ ((hθ x hx).contMDiffAt (hU.mem_nhds hx))
        ((hf x hx).contMDiffAt (hU.mem_nhds hx)) ((hg x hx).contMDiffAt (hU.mem_nhds hx)) F
        (hcurve x) (htime x hx)
    change mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) < 0
    rw [hder]
    by_cases hnear : |θ x| < ε
    · obtain ⟨hdf, hdg, hdiff⟩ := hcollar x hx hnear
      exact weighted_blend_neg (hrange _) hdf hdg hC hdiff (hweight _).le hsmall
    · have hz := hzero (θ x) (le_of_not_gt hnear)
      have hdχ :=
        deriv_eq_zero_of_nonneg_zero (hχ.differentiable (by simp)) (fun t => (hrange t).1) hz
      simpa only [hz, hdχ, MulZeroClass.zero_mul, add_zero, sub_zero] using hgneg x hx
  · intro x hx hxzero
    have ht : ContinuousAt θ x := (hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hone' : ∀ᶠ t in 𝓝 (θ x), χ t = 1 := by simpa only [hxzero] using hone
    filter_upwards [ht.eventually hone'] with y hy
    change g y + χ (θ y) * (f y - g y) = f y
    rw [hy]
    ring
  · intro x hx hxout
    have ht : ContinuousAt (fun y => |θ y|) x :=
      ((hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)).abs
    filter_upwards [ht (eventually_gt_nhds hxout)] with y hy
    exact hout y hy.le

/-! ### Flow tubes -/

/-- The flow tube of a compact set. -/
def FlowCancellation.flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (S : Set X)
    (ε : ℝ) : Set X :=
  (fun q : ℝ × X => F q.1 q.2) '' (Set.Icc (-ε) ε ×ˢ S)

/-- The flow tube is compact. -/
theorem FlowCancellation.isCompact_flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {S : Set X} (hS : IsCompact S) (ε : ℝ) : IsCompact (flowTube F S ε) :=
  (CompactIccSpace.isCompact_Icc.prod hS).image (F.continuous continuous_fst continuous_snd)

/-- A flow tube inside an open set exists. -/
theorem FlowCancellation.exists_flowTube_subset {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S N : Set X} (hS : IsCompact S) (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ ε : ℝ, 0 < ε ∧ flowTube F S ε ⊆ N := by
  have hopen : IsOpen {t : ℝ | ∀ x ∈ S, F t x ∈ N} :=
    MorsePerturbation.isOpen_forall_mem_compact hS
      (hN.preimage (F.continuous continuous_fst continuous_snd))
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∀ x ∈ S, F t x ∈ N} := by
    intro x hx
    simpa only [F.map_zero_apply] using hSN hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  apply hball ?_ x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- Signed-time membership in the flow tube. -/
theorem FlowCancellation.mem_flowTube_of_signedTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {ε : ℝ} {x : X} (hx : x ∈ levelBasin F f c)
    (ht : |signedLevelTime F f c x| ≤ ε) : x ∈ flowTube F {y | f y = c} ε := by
  refine
    ⟨(-signedLevelTime F f c x, F (signedLevelTime F f c x) x),
      ⟨?_, signedLevelTime_hits F f c hx⟩, ?_⟩
  · constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  · simp only [← F.map_add, neg_add_cancel, F.map_zero_apply]

/-- A compact negative margin exists. -/
theorem FlowCancellation.exists_compact_negative_margin {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {D : X → ℝ} (hD : ContinuousOn D S) (hneg : ∀ x ∈ S, D x < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ S, D x < -μ := by
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn hne hD
    refine ⟨-D p / 2, by linarith [hneg p hp], ?_⟩
    intro x hx
    have hle : D x ≤ D p := hmax hx
    linarith [hneg p hp]
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- The directional derivative is smooth on a set. -/
theorem FlowCancellation.contMDiffOn_directionalDerivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U)
    {g : M → ℝ} (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) g x (V x)) U := by
  have ht :=
    (hg.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp hV.contMDiffOn
      (fun x hx => hx)
  have hh := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn ht
  apply hh.congr
  intro x hx
  change
    (NormedSpace.fromTangentSpace (g x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (V x)) =
      (NormedSpace.fromTangentSpace (g x)) (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g U x (V x))
  rw [mfderivWithin_of_isOpen hU hx]

/-- Native time collar bounds exist. -/
theorem FlowCancellation.exists_native_time_collar_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {U : Set M}
    (hU : IsOpen U) {f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ ε μ C : ℝ,
      0 < ε ∧
        0 < μ ∧
          0 ≤ C ∧
            ∀ x ∈ U,
              |signedLevelTime F f c x| < ε →
                mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
                  mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |signedLevelTime F f c x| :=
  by
  let S : Set M := {x | f x = c}
  have hS : IsCompact S := (isClosed_eq hf.continuous continuous_const).isCompact
  let Df (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let Dg (x : M) := mvfderiv 𝓘(ℝ, E) g x (V x)
  have hDf : Continuous Df := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hDg : ContinuousOn Dg U := (contMDiffOn_directionalDerivative hU hg hV).continuousOn
  have hmax : ContinuousOn (fun x => Max.max (Df x) (Dg x)) U :=
    continuous_max.comp_continuousOn (hDf.continuousOn.prodMk hDg)
  obtain ⟨μ, hμ, hmargin⟩ :=
    exists_compact_negative_margin hS (hmax.mono hlevel)
      (fun x hx => max_lt (hfc x hx) (hgc x hx))
  let N : Set M := U ∩ (fun x => Max.max (Df x) (Dg x)) ⁻¹' Set.Iio (-μ)
  have hN : IsOpen N := hmax.isOpen_inter_preimage hU isOpen_Iio
  have hSN : S ⊆ N := fun x hx => ⟨hlevel hx, hmargin x hx⟩
  obtain ⟨ε, hε, htube⟩ := exists_flowTube_subset F hS hN hSN
  let K := flowTube F S ε
  have hK : IsCompact K := isCompact_flowTube F hS ε
  have hKU : K ⊆ U := fun x hx => (htube hx).1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hDf.continuousOn.sub (hDg.mono hKU))
  let C : ℝ := Max.max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) (hx : x ∈ K) : ‖Df x - Dg x‖ ≤ C := (hC₀ x hx).trans (le_max_left _ _)
  refine ⟨ε, μ, C, hε, hμ, hC, ?_⟩
  intro x hx hxε
  have hxK : x ∈ K := mem_flowTube_of_signedTime F f c (hbasin hx) hxε.le
  have hxN := htube hxK
  have hneg : Max.max (Df x) (Dg x) < -μ := hxN.2
  refine
    ⟨(lt_of_le_of_lt (le_max_left _ _) hneg).le, (lt_of_le_of_lt (le_max_right _ _) hneg).le, ?_⟩
  let θ := signedLevelTime F f c x
  let y := F θ x
  have hy : f y = c := signedLevelTime_hits F f c (hbasin hx)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : F t y ∈ K := ⟨(t, y), ⟨ht, hy⟩, rfl⟩
  let ℓ (t : ℝ) := f (F t y) - g (F t y)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : HasDerivAt ℓ (Df (F t y) - Dg (F t y)) t := by
    have hgpoint :=
      ((hg (F t y) (hKU (hpoint t ht))).contMDiffAt
            (hU.mem_nhds (hKU (hpoint t ht)))).mdifferentiableAt
        (by simp)
    exact
      (hasDerivAt_comp_native_integralCurve_at (hf.mdifferentiableAt (by simp)) (hcurve y)).sub
        (hasDerivAt_comp_native_integralCurve_at hgpoint (hcurve y))
  have h0 : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hθ : -θ ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith [(abs_lt.mp hxε).1, (abs_lt.mp hxε).2]
  have hmvt :=
    (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).differentiableAt)
      (fun t ht => by rw [(hd t ht).deriv]; exact hbound _ (hpoint t ht)) h0 hθ
  have hreturn : F (-θ) y = x := by
    dsimp [y]
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  simpa only [ℓ, F.map_zero_apply, hreturn, heq y hy, sub_self, sub_zero, Real.norm_eq_abs,
    abs_neg] using hmvt

/-- A boundary germ correction exists. -/
theorem FlowCancellation.exists_boundary_germ_correction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {r : ℝ} (hr : 0 < r) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x ∈ U, r ≤ |signedLevelTime F f c x| → b =ᶠ[𝓝 x] g := by
  obtain ⟨ε₀, μ, C, hε₀, hμ, hC, hbounds⟩ :=
    exists_native_time_collar_bounds hU hf hg hV F hcurve hlevel hbasin heq hfc
      (fun x hx => hgneg x (hlevel hx))
  let ε := Min.min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hr)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hfc
  have htime (x : M) (hx : x ∈ U) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 :=
    mvfderiv_signedLevelTime hf hV F hcurve hfc (hbasin hx)
  obtain ⟨b, hb, hbneg, hbone, -, hboff⟩ :=
    exists_native_descent_blend hU (hθ.mono hbasin) hf.contMDiffOn hg F hcurve htime hgneg hε hμ
      hC (fun x hx ht => hbounds x hx (lt_of_lt_of_le ht (min_le_left _ _)))
  refine ⟨b, hb, hbneg, ?_, fun x hx ht => hboff x hx (hεr.trans_le ht)⟩
  intro x hx
  apply hbone x (hlevel hx)
  let D (y : M) := mvfderiv 𝓘(ℝ, E) f y (V y)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  exact
    signedLevelTime_eq_zero F hf.continuous hD
      (fun y t => FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve y) t) hfc hx

/-- A signed-time level separation exists. -/
theorem FlowCancellation.exists_signedTime_level_separation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hlevel : {x | f x = d} ⊆ levelBasin F f c) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, f x = d → r < |signedLevelTime F f c x| := by
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  have hS : IsCompact {x | f x = d} := (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨r, hr, hmargin⟩ :=
    exists_compact_negative_margin hS ((hθ.continuousOn.mono hlevel).abs.neg)
      (fun x hx => by
        apply neg_neg_of_pos
        apply abs_pos.mpr
        intro hz
        have hhit := signedLevelTime_hits F f c (hlevel hx)
        rw [hz, F.map_zero_apply] at hhit
        exact hcd (hhit.symm.trans hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  have hh : -|signedLevelTime F f c x| < -r := hmargin x hx
  linarith

/-- A level-preserving boundary correction exists. -/
theorem FlowCancellation.exists_boundary_correction_preserving_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hcU : {x | f x = c} ⊆ U) (hdU : {x | f x = d} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x) (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x, f x = d → b =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hsep⟩ :=
    exists_signedTime_level_separation hf hV F hcurve hcd hfc (hdU.trans hbasin)
  obtain ⟨b, hb, hbneg, hbc, hboff⟩ :=
    exists_boundary_germ_correction hU hf hg hV F hcurve hcU hbasin heq hfc hgneg hr
  exact ⟨b, hb, hbneg, hbc, fun x hx => hboff x (hdU hx) (hsep x hx).le⟩

/-- The band lies in the crossing basin. -/
theorem FlowCancellation.band_subset_crossingBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {c d T : ℝ} (hT : 0 < T)
    (hforward : ∀ x, f x ≤ d → f (F T x) < c) (hbackward : ∀ x, c ≤ f x → d < f (F (-T) x)) :
    f ⁻¹' Set.Icc c d ⊆ crossingBasin F f c d := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  constructor
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' hT.le hcont.continuousOn
        (show c ∈ Set.Icc (f (F T x)) (f (F 0 x)) from
          ⟨(hforward x hx.2).le, by simpa only [F.map_zero_apply] using hx.1⟩)
    exact ⟨t, ht⟩
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' (show -T ≤ (0 : ℝ) by linarith) hcont.continuousOn
        (show d ∈ Set.Icc (f (F 0 x)) (f (F (-T) x)) from
          ⟨by simpa only [F.map_zero_apply] using hx.2, (hbackward x hx.1).le⟩)
    exact ⟨t, ht⟩

/-- Smooth band height germs exist. -/
theorem FlowCancellation.exists_smooth_band_height_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ (U : Set M) (g : M → ℝ),
      IsOpen U ∧
        f ⁻¹' Set.Icc c d ⊆ U ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧
            (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧ ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f := by
  let U := crossingBasin F f c d
  let g := flowBandHeight F f c d
  obtain ⟨hU, hg, hgder⟩ := smooth_flowBandHeight hf hV F hcurve hcd hc hd
  obtain ⟨T, hT, hforward, hbackward⟩ := hcross
  have hband : f ⁻¹' Set.Icc c d ⊆ U :=
    band_subset_crossingBasin F hf.continuous hT hforward hbackward
  have hcU : {x | f x = c} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx], by rw [hx]; exact hcd.le⟩)
  have hdU : {x | f x = d} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx]; exact hcd.le, by rw [hx]⟩)
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hgc (x : M) (hx : f x = c) : g x = f x :=
    (flowBandHeight_lower F hf.continuous hD hder hc hx).trans hx.symm
  have hgd (x : M) (hx : f x = d) : g x = f x :=
    (flowBandHeight_upper F hf.continuous hD hder hc hd hcd (hdU hx) hx).trans hx.symm
  obtain ⟨b, hb, hbneg, hbc, hbd⟩ :=
    exists_boundary_correction_preserving_level hU hf hg hV F hcurve hcd.ne hcU hdU
      Set.inter_subset_left hgc hc (fun x hx => (hgder x hx).2)
  have hbdval (x : M) (hx : f x = d) : b x = f x := (hbd x hx).eq_of_nhds.trans (hgd x hx)
  obtain ⟨k, hk, hkneg, hkd, hkc⟩ :=
    exists_boundary_correction_preserving_level hU hf hb hV F hcurve hcd.ne' hdU hcU
      Set.inter_subset_right hbdval hd hbneg
  refine ⟨U, k, hU, hband, hk, hkneg, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hkc x hx).trans (hbc x hx)
  · exact hkd x hx

/-! ### Band replacement -/

/-- The band replacement of a function. -/
def FlowCancellation.bandReplacement {X : Type*} (f g : X → ℝ) (c d : ℝ) (x : X) : ℝ := by
  classical exact if f x ∈ Set.Ioo c d then g x else f x

/-- The band replacement's germ on the boundary. -/
theorem FlowCancellation.bandReplacement_germ_boundary {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} {x : X} (heq : g =ᶠ[𝓝 x] f) :
    bandReplacement f g c d =ᶠ[𝓝 x] f ∧ bandReplacement f g c d =ᶠ[𝓝 x] g := by
  have hh : bandReplacement f g c d =ᶠ[𝓝 x] f := by
    filter_upwards [heq] with y hy
    simp only [bandReplacement, hy, ite_self]
  exact ⟨hh, hh.trans heq.symm⟩

/-- The band replacement's germ in the interior. -/
theorem FlowCancellation.bandReplacement_germ_interior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∈ Set.Ioo c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_Ioo.preimage hf).mem_nhds hx] with y hy
  exact if_pos hy

/-- The band replacement's germ in the exterior. -/
theorem FlowCancellation.bandReplacement_germ_exterior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∉ Set.Icc c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] f := by
  filter_upwards [((isClosed_Icc.preimage hf).isOpen_compl).mem_nhds hx] with y hy
  exact if_neg (fun h => hy ⟨h.1.le, h.2.le⟩)

/-- The band replacement's germ on a closed set. -/
theorem FlowCancellation.bandReplacement_germ_on_closed {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∈ Set.Icc c d) : bandReplacement f g c d =ᶠ[𝓝 x] g := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).2
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).2
  exact
    bandReplacement_germ_interior hf ⟨lt_of_le_of_ne hx.1 (Ne.symm hc), lt_of_le_of_ne hx.2 hd⟩

/-- The band replacement's germ off an open set. -/
theorem FlowCancellation.bandReplacement_germ_off_open {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∉ Set.Ioo c d) : bandReplacement f g c d =ᶠ[𝓝 x] f := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).1
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).1
  apply bandReplacement_germ_exterior hf
  intro h
  exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hc), lt_of_le_of_ne h.2 hd⟩

/-- The band replacement is smooth. -/
theorem FlowCancellation.contMDiff_bandReplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {c d : ℝ} {U : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (hU : IsOpen U)
    (hband : f ⁻¹' Set.Icc c d ⊆ U) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (bandReplacement f g c d) := by
  intro x
  by_cases hx : f x ∈ Set.Icc c d
  · exact
      ((hg x (hband hx)).contMDiffAt (hU.mem_nhds (hband hx))).congr_of_eventuallyEq
        (bandReplacement_germ_on_closed hf.continuous hboundary hx)
  · exact hf.contMDiffAt.congr_of_eventuallyEq (bandReplacement_germ_exterior hf.continuous hx)

/-- Equal germs give equal manifold derivatives. -/
theorem FlowCancellation.mvfderiv_eq_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f g : M → ℝ} {x : M} (heq : f =ᶠ[𝓝 x] g) :
    mvfderiv 𝓘(ℝ, E) f x (V x) = mvfderiv 𝓘(ℝ, E) g x (V x) := by
  unfold mvfderiv
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

/-- A global band Lyapunov function exists. -/
theorem FlowCancellation.exists_global_band_lyapunov {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ b : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
        (∀ x, f x ∈ Set.Icc c d → mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          ∀ x, f x ∉ Set.Ioo c d → b =ᶠ[𝓝 x] f := by
  obtain ⟨U, g, hU, hband, hg, hgneg, hgerm⟩ :=
    exists_smooth_band_height_germs hf hV F hcurve hcd hc hd hcross
  refine ⟨bandReplacement f g c d, contMDiff_bandReplacement hf hg hU hband hgerm, ?_, ?_⟩
  · intro x hx
    rw [mvfderiv_eq_of_germ (V := V) (bandReplacement_germ_on_closed hf.continuous hgerm hx)]
    exact hgneg x (hband hx)
  · intro x hx
    exact bandReplacement_germ_off_open hf.continuous hgerm hx

/-! ### The cubic Hessian -/

/-- The Hessian of the cubic model. -/
def MorseCancellation.hessian {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : Model m →L[ℝ] Model m →L[ℝ] ℝ :=
  (2 * p.1) •
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).smulRight
        (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) +
    ∑ i,
      (2 * σ i) •
        (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).smulRight
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))

/-- The Hessian computes the second derivative. -/
theorem MorseCancellation.hessian_apply {m : ℕ} (σ : Fin m → ℝ) (p v w : Model m) :
    hessian σ p v w = 2 * p.1 * v.1 * w.1 + ∑ i, 2 * σ i * v.2 i * w.2 i := by
  simp [hessian, mul_assoc]

/-- The differential is differentiable. -/
theorem MorseCancellation.hasFDerivAt_differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (differential σ t) (hessian σ p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  let L (i : Fin m) : Model m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
  have hq :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (((L i).hasFDerivAt (x := p)).const_mul (2 * σ i)).smul_const (L i))
  convert
      (((hx.pow 2).add_const t).smul_const (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))).add hq using
      1 <;>
    first
    | rfl
    | ( apply ContinuousLinearMap.ext; intro v
        apply ContinuousLinearMap.ext; intro w
        simp [hessian, L, mul_assoc])

/-- The cubic's Hessian derivative. -/
theorem MorseCancellation.fderiv_cubic_hessian {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (fderiv ℝ (cubic σ t)) p = hessian σ p := by
  rw [show fderiv ℝ (cubic σ t) = differential σ t from funext (fderiv_cubic σ t)]
  exact (hasFDerivAt_differential σ t p).fderiv

/-- The cubic Hessian is bijective at the critical point. -/
theorem MorseCancellation.hessian_bijective {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {p : Model m}
    (hp : p.1 ≠ 0) : Function.Bijective (hessian σ p) := by
  have hi : Function.Injective (hessian σ p) := by
    apply (injective_iff_map_eq_zero (hessian σ p)).mpr
    intro v hv
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hv
    have hx' : 2 * p.1 * v.1 = 0 := by simpa [hessian_apply] using hx
    have hvx : v.1 = 0 := (mul_eq_zero.mp hx').resolve_left (mul_ne_zero (by norm_num) hp)
    apply Prod.ext hvx
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hv
    have hy' : 2 * σ i * v.2 i = 0 := by simpa [hessian_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  have hd : Module.finrank ℝ (Model m) = Module.finrank ℝ (Model m →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Model m →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = _ :=
        (LinearMap.toContinuousLinearMap : (Model m →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Model m →L[ℝ] ℝ)).finrank_eq
  exact
    ⟨hi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (hessian σ p).toLinearMap)
            hd).mp
        hi⟩

/-- The cubic critical point is Morse. -/
theorem MorseCancellation.cubic_isMorse {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) : MorsePerturbation.IsMorse (cubic σ t) := by
  intro p hcrit
  rw [fderiv_cubic_hessian]
  apply hessian_bijective σ hσ
  intro hp
  have h := ((critical_iff σ hσ t p).mp hcrit).1
  exact ht (by simpa [hp] using h)

/-! ### Native cubic cancellation -/

/-- A cutoff for the native cubic cancellation exists. -/
theorem NativeCubicCancellation.exists_cutoff {m : ℕ} {V : Set (MorseCancellation.Model m)}
    (hV : IsOpen V) (h0 : (0 : MorseCancellation.Model m) ∈ V) :
    ∃ φ : MorseCancellation.Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ V ∧
            ∃ U : Set (MorseCancellation.Model m),
              IsOpen U ∧ (0 : MorseCancellation.Model m) ∈ U ∧ Set.EqOn φ (fun _ => 1) U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let φ : ContDiffBump (0 : MorseCancellation.Model m) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine
    ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, Metric.ball 0 (r / 4), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), ?_⟩
  · rw [φ.tsupport_eq]
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (by change r / 2 < r; linarith)
  · intro p hp
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp)

/-- The Morse property transfers across equal germs. -/
theorem MorseCancellationPreservation.isMorseAt_of_same_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {x : M} (hf : ManifoldMorse.IsMorseAt E f x) (heq : g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorseAt E g x := by
  obtain ⟨e, he, hx, hgood⟩ := hf
  refine ⟨e, he, hx, ?_⟩
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.symm.continuousAt (e.map_source hx)
    rw [ContinuousAt, e.left_inv hx] at h
    exact h
  have hc : g ∘ e.symm =ᶠ[𝓝 (e x)] f ∘ e.symm := heq.comp_tendsto ht
  rw [hc.fderiv_eq, (hc.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hgood

/-- A regular point of the replacement is Morse. -/
theorem MorseCancellationPreservation.isMorseAt_of_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {x : M}
    (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) : ManifoldMorse.IsMorseAt E g x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  refine ⟨e, he, hx, Or.inl ?_⟩
  intro hc
  exact hreg ((ManifoldMorse.mem_criticalPoints_iff hg he hx).mpr hc)

/-- A function whose critical germs are Morse is Morse. -/
theorem MorseCancellationPreservation.isMorse_of_critical_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} (hf : ManifoldMorse.IsMorse E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hkeep : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 → g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorse E g := by
  intro x
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
  · exact isMorseAt_of_same_germ (hf x) (hkeep x hx)
  · exact isMorseAt_of_regular hg hx

/-- A negative directional derivative excludes criticality. -/
theorem FlowCancellation.not_critical_of_directional_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {g : M → ℝ} {x : M}
    (hneg : mvfderiv 𝓘(ℝ, E) g x (V x) < 0) : x ∉ ManifoldMorse.criticalPoints E g := by
  intro hx
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 at hx
  unfold mvfderiv at hneg
  rw [hx] at hneg
  simp at hneg

/-- The band replacement removes the Morse pair. -/
theorem FlowCancellation.remove_morse_band_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x))
    {p q : M} (hpq : p ≠ q) (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpc : f p ∈ Set.Icc c d)
    (hqc : f q ∈ Set.Icc c d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hneg, hgerm⟩ := exists_global_band_lyapunov hf hV F hcurve hcd hc hd hcross
  have hreg (x : M) (hx : f x ∈ Set.Icc c d) : x ∉ ManifoldMorse.criticalPoints E g :=
    not_critical_of_directional_neg (hneg x hx)
  have hnew (x : M) :
    x ∈ ManifoldMorse.criticalPoints E g ↔
      x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q := by
    constructor
    · intro hx
      have hout : f x ∉ Set.Icc c d := fun h => hreg x h hx
      have he := hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)
      have hcrit : x ∈ ManifoldMorse.criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
        rw [← he.mfderiv_eq]
        exact hx
      exact ⟨hcrit, fun h => hout (h ▸ hpc), fun h => hout (h ▸ hqc)⟩
    · rintro ⟨hx, hxp, hxq⟩
      have hout : f x ∉ Set.Icc c d := fun h => (hpair x hx h).elim hxp hxq
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [(hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)).mfderiv_eq]
      exact hx
  have hmg : ManifoldMorse.IsMorse E g := by
    apply MorseCancellationPreservation.isMorse_of_critical_germs hm hg
    intro x hx
    apply hgerm x
    intro h
    exact hreg x ⟨h.1.le, h.2.le⟩ hx
  have heq :
    ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f \ { p, q } := by
    ext x
    simpa only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hnew x
  have hsub : { p, q } ⊆ ManifoldMorse.criticalPoints E f := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact Set.mem_singleton_iff.mp hx ▸ hq
  refine ⟨g, hg, hmg, ?_, hnew, hgerm⟩
  rw [heq, ← Set.ncard_pair hpq]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub (ManifoldMorse.finite_criticalPoints hf hm)

/-- A unique native cubic connection can be cancelled. -/
theorem MorseCancellation.cancel_unique_native_cubic_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨K, V', -, hKsub, hV', -, hkeep, -, G, hGcurve, hcross, -⟩ :=
    exists_cubic_connection_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hzero hdesc
      hinj hp hq hpq hc hd hpair hunique
  have hcd : c < d := lt_trans hc (lt_trans hpq hd)
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd.le⟩
        · exact ⟨hcd.le, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  have hneq : Φ (a, (0 : Fin m → ℝ)) ≠ Φ (-a, 0) := by
    intro h
    exact hpq.ne (congrArg f h)
  exact
    FlowCancellation.remove_morse_band_pair hf hm hV' G hGcurve hcd
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hcross hneq hp
      hq ⟨hc.le, (hpq.trans hd).le⟩ ⟨(hc.trans hpq).le, hd.le⟩ hpair

attribute [local instance 100] Classical.propDecidable in
/-- A unique native transverse connection can be cancelled. -/
theorem MorseCancellation.cancel_unique_native_transverse_connection {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (Q P :
      PartialDiffeomorph
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) 𝓘(ℝ, Z)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) Z ∞)
    (H :
      PartialDiffeomorph
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) ∞)
    (h0 : 0 ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hQsource : Q.source = H.source) (hPsource : P.source = H.target) (hQtarget : Q.target = U)
    (hPtarget : P.target = U) (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace σ)
        𝓘(ℝ, MorseHandle.PositiveSpace σ)
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (fun x => H (x, 0)) (fun y => (0, y)) 0 0)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Q.source,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ P.source,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Q.source,
        Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ P.source,
        Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hV1 := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : A (z, t) = F t (A (z, 0)) := by
    simpa only [zero_add] using
      (FlowSuspension.native_vertical_cylinder_flow A hAsource hV1 hAfield F hF z hz 0
          t).symm
  have hleft :=
    FlowSuspension.cylinder_outgoing_basin_labels F A Q (fun z hz => hflow z (hQU hz))
      (fun u => Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)))
      (fun u => Tq + v₀ u) hphaseq
      (fun u hu => outgoing_cubic_slice_basin σ hσ a Tq Φq F hqbasin u (hboxq (hsliceq u hu)))
  have hright :=
    FlowSuspension.cylinder_incoming_basin_labels F A P (fun z hz => hflow z (hPU hz))
      (fun u => Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)))
      (fun u => Tp + v₁ u) hphasep
      (fun u hu => incoming_cubic_slice_basin σ a Tp Φp F hpbasin u (hboxp (hslicep u hu)))
  rw [hQtarget, hQsource] at hleft
  rw [hPtarget, hPsource] at hright
  have hheightAux : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) / s = b / s - z.2 := by
    intro z hz ht
    rw [hheight z hz ht]
    field_simp
  obtain
    ⟨L₁, L₂, N, W, G, Ξ, _, hNsub, hW, hG, hzeroW, hdescW, hgerm, hΞsource, hΞtarget, hΞfield,
      hΞaxis, hunique, hmatch⟩ :=
    FlowSuspension.exists_unique_phase_corrected_cylinder A hAsource (hf.div_const s)
      hheightAux V hV hAfield F hF Q P H h0 hH0 hQ0 hP0 (fun _ hz => hQsource ▸ hz)
      (fun _ hz => hPsource ▸ hz) hQtarget hPtarget hdiagram htrans (fun z hz => hleft z hz 0)
      (fun z hz => hright z hz 1) hold hv₀ hv₁ hv₀zero hv₁zero
  have hdescWf (x : M) (hx : x ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x (W x) < 0 :=
    (FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hs
          (W x)).mp
      (hdescW x
        ((FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp))
              hs (V x)).mpr
          (hdesc x hx)))
  have hAregular (x : M) (hx : x ∈ A.target) : V x ≠ 0 := by
    intro hz
    rw [hAfield x hx] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqN : Φq (-a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hq)
  have hpN : Φp (a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hp)
  have hQ0source : 0 ∈ Q.source := hQsource ▸ h0
  have hP0source : 0 ∈ P.source := by
    rw [hPsource, ← hH0]
    exact H.map_source' h0
  have hne : Φq (-a, 0) ≠ Φp (a, 0) := by
    intro h
    exact hpq.ne (congrArg f h.symm)
  obtain ⟨Γ, hΓaxis, hΓfield, hΓq, hΓp, hΓcenter⟩ :=
    exists_full_cubic_chart_from_corrected_cylinder σ hσ ha Φq Φp A hAsource hV1 hqfield hpfield
      hAfield F hF L₁ L₂ Q P v₀ v₁ Q.open_source P.open_source hQ0source hP0source
      (fun u hu => hQU (Q.map_source' hu)) (fun u hu => hPU (P.map_source' hu)) hRq hRp hboxq
      hboxp hsliceq hslicep hphaseq hphasep Ξ Q.open_source hQ0source hΞsource hΞtarget
      (hW.of_le (by simp)) hΞfield G hG (hgerm _ hqN) (hgerm _ hpN) hne
      (hmatch.mono fun _ h => h.1) (hmatch.mono fun _ h => h.2)
  have hΓ0 : Γ (0, 0) = A (0, 0) := hΓcenter.trans (hΞaxis 0)
  have hσne : ∀ i, σ i ≠ 0 := by
    intro i
    rcases hσ i with hi | hi <;> rw [hi] <;> norm_num
  have hcancel :=
    cancel_unique_native_cubic_connection σ hσne ha Γ hΓaxis hf hm W hW hΓfield G hG
      (fun x hx => (hzeroW x).mpr (hzero x hx)) hdescWf hinj (by rw [hΓp]; exact hp)
      (by rw [hΓq]; exact hq) (by rw [hΓp, hΓq]; exact hpq) (by rw [hΓp]; exact hc)
      (by rw [hΓq]; exact hd) (by simpa only [hΓp, hΓq] using hpair)
      (by
        intro x _ hbot htop
        rw [hΓq] at hbot
        rw [hΓp] at htop
        rw [hΓ0]
        exact hunique x hbot htop)
  simpa only [hΓp, hΓq] using hcancel

/-- Native endpoint slice data can be cancelled. -/
theorem MorseCancellation.cancel_native_endpoint_slice_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞) {Rq Rp Tq Tp : ℝ}
    (D : NativeEndpointSliceData σ a Φq Φp A Rq Rp Tq Tp)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace σ)
        𝓘(ℝ, MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.Q (x, 0))
        (fun y => D.P (0, y)) 0 0)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y =
          FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hrelative :=
    TransverseGerms.relative_transverse_of_label_sheets D.Q D.P D.H D.zero_source D.H_zero
      D.Q_zero D.P_zero (fun _ hz => D.Q_source ▸ hz) (fun _ hz => D.P_source ▸ hz) D.diagram
      htrans
  exact
    cancel_unique_native_transverse_connection σ hσ ha Φq Φp A D.source hf hm hs hheight V hV
      hqfield hpfield hAfield F hF hzero hdesc hinj D.Q D.P D.H D.zero_source D.H_zero D.Q_zero
      D.P_zero D.Q_source D.P_source D.Q_target D.P_target D.diagram hrelative D.phaseQ D.phaseP
      D.smooth_phaseQ D.smooth_phaseP D.zero_phaseQ D.zero_phaseP hRq hRp hboxq hboxp D.sliceQ
      D.sliceP D.formulaQ D.formulaP hqbasin hpbasin hold hp hq hpq hc hd hpair

/-! ### Transversality of the cancellation data -/

/-- The cancellation data's sheets are transverse. -/
def MorseCancellation.NativeConnectionCancellationData.Transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ}
    {f : M → ℝ} {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    Prop :=
  NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace D.σ)
    𝓘(ℝ, MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.slices.Q (x, 0))
    (fun y => D.slices.P (0, y)) 0 0

/-- The cancellation of a native connection datum. -/
theorem MorseCancellation.NativeConnectionCancellationData.cancel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) (htrans : D.Transverse)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ y,
                y ∈ ManifoldMorse.criticalPoints E g ↔
                  y ∈ ManifoldMorse.criticalPoints E f ∧ y ≠ p ∧ y ≠ q) ∧
              ∀ y, f y ∉ Set.Ioo c d → g =ᶠ[𝓝 y] f := by
  have hh :=
    MorseCancellation.cancel_native_endpoint_slice_data D.σ D.signs (by norm_num) D.Φq D.Φp D.A D.slices
      htrans hf hm D.positive_speed D.height_formula D.field D.smooth_field D.fieldQ D.fieldP
      D.vertical D.flow D.integral D.zero D.descent hinj D.positive_Rq D.positive_Rp D.boxQ D.boxP
      (by simpa only [D.endpointQ] using D.basinQ) (by simpa only [D.endpointP] using D.basinP)
      (by simpa only [D.endpointQ, D.endpointP] using D.unique) (by rw [D.endpointP]; exact hp)
      (by rw [D.endpointQ]; exact hq) (by rw [D.endpointP, D.endpointQ]; exact hpq)
      (by rw [D.endpointP]; exact hc) (by rw [D.endpointQ]; exact hd)
      (by simpa only [D.endpointP, D.endpointQ] using hpair)
  simpa only [D.endpointP, D.endpointQ] using hh

attribute [local instance 100] Classical.propDecidable in
/-- Native connection cancellation data exists. -/
theorem MorseCancellation.exists_native_connection_cancellation_data {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q x : M} (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ ManifoldMorse.criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (hunique :
      ∀ y,
        Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) → ∃ t, F t x = y)
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ D : NativeConnectionCancellationData (E := E) f p q m,
      (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, D.field z = V z) ∧
        (∀ y,
            Set.range (fun t => D.flow t y) = Set.range (fun t => F t y) ∧
              (∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 z)) ∧
                ∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 z)) ∧
          ∃ t, F t x = D.A 0 := by
  obtain
    ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hneg, hgerms, hmono, hp₀, hq₀, hunique₀,
      _, h0U, hAsource, hAaxis, hheight, hAfield, hgeometry, hreference⟩ :=
    FlowTimeChange.exists_normalized_connection_cylinder hf hdim V hV hzero hdesc F hF hpq
      hc hd hpair hp hq hunique
  have hgp : ∀ᶠ y in 𝓝 p, W y = cp.descentField y := by
    filter_upwards [hgerms p hpc, heqp] with y h₁ h₂
    exact h₁.trans h₂
  have hgq : ∀ᶠ y in 𝓝 q, W y = cq.descentField y := by
    filter_upwards [hgerms q hqc, heqq] with y h₁ h₂
    exact h₁.trans h₂
  obtain
    ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp, hqval, hpval, hqbox, hpbox, hqfield, hpfield,
      hqbasin, hpbasin, hBsub, _, hBmap, hBfield, ⟨D⟩⟩ :=
    exists_actual_connection_slice_data cp cq hf.continuous hdim hindex hW G hG hmono hxp hxq hp₀
      hq₀ hgp hgq A hAsource h0U hAfield hAaxis
  have hB0 : B (0, 0) = x₀ := by rw [hBmap, hAaxis, G.map_zero_apply]
  refine
    ⟨{  σ := σ
        signs := hσ
        field := W
        smooth_field := hW
        flow := G
        integral := hG
        zero := hzeros
        descent := hneg
        Φq := Ψq
        Φp := Ψp
        endpointQ := hqval
        endpointP := hpval
        fieldQ := hqfield
        fieldP := hpfield
        A := B
        vertical := hBfield
        speed := r
        positive_speed := hr
        height := b
        height_formula := ?_
        Rq := Rq
        Rp := Rp
        Tq := Tq
        Tp := Tp
        positive_Rq := hRq
        positive_Rp := hRp
        boxQ := hqbox
        boxP := hpbox
        basinQ := hqbasin
        basinP := hpbasin
        unique := ?_
        slices := D }, hgerms, hgeometry, ?_⟩
  · intro z hz ht
    rw [hBmap]
    exact hheight z (hBsub hz) ⟨ht.1.le, ht.2.le⟩
  · intro y hyq hyp
    rw [hB0]
    exact hunique₀ y hyq hyp
  · change ∃ t, F t x = B (0, 0)
    rw [hB0]
    exact hreference

/-- The first derivative of a time-independent label. -/
theorem TransverseGerms.derivative_first_of_time_independent_label {A Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : ℝ × A → Z × ℝ} {f : A → Z} (hF : DifferentiableAt ℝ F 0) (hf : DifferentiableAt ℝ f 0)
    (hlabel : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2)) :
    ∀ u : ℝ × A, (fderiv ℝ F 0 u).1 = fderiv ℝ f 0 u.2 := by
  have hsnd : HasFDerivAt (fun u : ℝ × A => u.2) (ContinuousLinearMap.snd ℝ ℝ A) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ A).hasFDerivAt
  have hd :
    HasFDerivAt (fun u : ℝ × A => f u.2) ((fderiv ℝ f 0).comp (ContinuousLinearMap.snd ℝ ℝ A))
      0 :=
    hf.hasFDerivAt.comp (f := fun u : ℝ × A => u.2) 0 hsnd
  have heq : fderiv ℝ (fun u : ℝ × A => (F u).1) 0 = fderiv ℝ (fun u : ℝ × A => f u.2) 0 :=
    hlabel.fderiv_eq
  rw [hF.hasFDerivAt.fst.fderiv, hd.fderiv] at heq
  intro u
  exact congrArg (fun L : (ℝ × A) →L[ℝ] Z => L u) heq

/-- Transverse labels of time-independent flow sheets. -/
theorem TransverseGerms.transverse_labels_of_time_independent_flow_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : ℝ × A → Z × ℝ} {G : ℝ × B → Z × ℝ} {f : A → Z}
    {g : B → Z} (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (G u).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Function.Surjective ((fderiv ℝ F 0).coprod (fderiv ℝ G 0))) :
    Function.Surjective ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) := by
  have hfirstF := derivative_first_of_time_independent_label hF hf hlabelF
  have hfirstG := derivative_first_of_time_independent_label hG hg hlabelG
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans (z, 0)
  refine ⟨(u.2, v.2), ?_⟩
  change fderiv ℝ f 0 u.2 + fderiv ℝ g 0 v.2 = z
  rw [← hfirstF u, ← hfirstG v]
  exact congrArg Prod.fst huv

/-- Transverse labels of native flow sheets. -/
theorem TransverseGerms.transverse_labels_of_native_flow_sheets {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) (hC0 : (0 : Z × ℝ) ∈ C.source)
    (F : ℝ × A → M) (G : ℝ × B → M) (hF : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F 0)
    (hG : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) G 0) (hF0 : F 0 = C 0) (hG0 : G 0 = C 0)
    {f : A → Z} {g : B → Z} (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (C.symm (F u)).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (C.symm (G u)).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) F G 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) f g 0 0 := by
  have hFt : F 0 ∈ C.target := hF0.symm ▸ C.map_source' hC0
  have hGt : G 0 ∈ C.target := hG0.symm ▸ C.map_source' hC0
  have hFb : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, Z × ℝ) (C.symm ∘ F) 0 :=
    (C.symm.mdifferentiableAt (by simp) hFt).comp (f := F) 0 hF
  have hGb : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z × ℝ) (C.symm ∘ G) 0 :=
    (C.symm.mdifferentiableAt (by simp) hGt).comp (f := G) 0 hG
  have hcross : G 0 = F 0 := hG0.trans hF0.symm
  have ht :=
    ChartMapPerturbation.transverse_in_chart C.symm hF hG hcross hFt (htrans hcross)
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at ht
  have hl :=
    transverse_labels_of_time_independent_flow_sheets hFb.differentiableAt hGb.differentiableAt hf
      hg hlabelF hlabelG ht
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  exact hl

/-! ### Basin sheets and factorizations -/

/-- The outgoing basin sheet of the cancellation data. -/
def MorseCancellation.NativeConnectionCancellationData.outgoingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.NegativeSpace D.σ) : M :=
  D.flow (w.1 - D.Tq)
    (D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (w.2, 0), D.Tq)))

/-- The incoming basin sheet of the cancellation data. -/
def MorseCancellation.NativeConnectionCancellationData.incomingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.PositiveSpace D.σ) : M :=
  D.flow (w.1 - D.Tp)
    (D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (0, w.2), D.Tp)))

/-- The outgoing sheet's properties. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, E) ∞ D.outgoingSheet 0 ∧
      D.outgoingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.NegativeSpace D.σ =>
            (D.A.symm (D.outgoingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.NegativeSpace D.σ => D.slices.Q (w.2, 0)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero
      (fun u =>
        D.Φq
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq)))
      D.slices.phaseQ D.Tq D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

/-- The incoming sheet's properties. -/
theorem MorseCancellation.NativeConnectionCancellationData.incomingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) ∞ D.incomingSheet 0 ∧
      D.incomingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.PositiveSpace D.σ =>
            (D.A.symm (D.incomingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.PositiveSpace D.σ => D.slices.P (0, w.2)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero
      (fun u =>
        D.Φp
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp)))
      D.slices.phaseP D.Tp D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

/-- The native sheets are transverse. -/
theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ)
        𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) D.outgoingSheet D.incomingSheet 0
        0) :
    D.Transverse := by
  obtain ⟨hout, hout0, houtlabel⟩ := D.outgoingSheet_properties
  obtain ⟨hin, hin0, hinlabel⟩ := D.incomingSheet_properties
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hQdiff :=
    (D.slices.Q.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.Q.open_source.mem_nhds hQ0)).differentiableAt
      (by simp)
  have hPdiff :=
    (D.slices.P.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.P.open_source.mem_nhds hP0)).differentiableAt
      (by simp)
  have hq :
    DifferentiableAt ℝ (fun x : MorseHandle.NegativeSpace D.σ => D.slices.Q (x, 0)) 0 :=
    hQdiff.comp (f := fun x : MorseHandle.NegativeSpace D.σ => (x, 0)) 0
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hp :
    DifferentiableAt ℝ (fun y : MorseHandle.PositiveSpace D.σ => D.slices.P (0, y)) 0 :=
    hPdiff.comp (f := fun y : MorseHandle.PositiveSpace D.σ => (0, y)) 0
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hA0 : (0 : (Fin m → ℝ) × ℝ) ∈ D.A.source := by
    rw [D.slices.source]
    exact ⟨D.slices.zero_domain, Set.mem_univ _⟩
  exact
    TransverseGerms.transverse_labels_of_native_flow_sheets D.A hA0 D.outgoingSheet
      D.incomingSheet (hout.mdifferentiableAt (by simp)) (hin.mdifferentiableAt (by simp)) hout0
      hin0 hq hp houtlabel hinlabel htrans

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing basin chart of the cancellation data. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.outgoingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.NegativeSpace D.σ => P ((w.2, 0), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q) ↔ w.1.2 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  let S := fun u =>
    D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq))
  have hbasin (u) (hu : u ∈ D.slices.Q.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atBot (𝓝 q) ↔ u.2 = 0 :=
    MorseCancellation.outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow D.basinQ u
      (D.boxQ (D.slices.sliceQ u hu))
  obtain ⟨P, -, h0P, hP0, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero S D.slices.phaseQ D.Tq D.slices.smooth_phaseQ
      D.slices.zero_phaseQ D.slices.formulaQ
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q))
      (fun t y => MorseCancellation.flow_time_atBot_limit_iff D.flow t y q) (fun u => u.2 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.Q.open_source hQ0 D.flow S
      D.Tq hformula
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hP0, ?_, hplane⟩
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply] using heq

attribute [local instance 100] Classical.propDecidable in
/-- The incoming basin chart of the cancellation data. -/
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.incomingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.PositiveSpace D.σ => P ((0, w.2), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p) ↔ w.1.1 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  let S := fun u =>
    D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp))
  have hbasin (u) (hu : u ∈ D.slices.P.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atTop (𝓝 p) ↔ u.1 = 0 :=
    MorseCancellation.incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow D.basinP u
      (D.boxP (D.slices.sliceP u hu))
  obtain ⟨P, -, h0P, hPzero, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero S D.slices.phaseP D.Tp D.slices.smooth_phaseP
      D.slices.zero_phaseP D.slices.formulaP
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p))
      (fun t y => MorseCancellation.flow_time_atTop_limit_iff D.flow t y p) (fun u => u.1 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.P.open_source hP0 D.flow S
      D.Tp hformula
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hPzero, ?_, hplane⟩
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply] using heq

/-- Native transversality from sheet factorizations. -/
theorem TransverseGerms.native_transversality_of_sheet_factorizations
    {A B U V E HU HV HE X Y M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace HE]
    {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y] [ChartedSpace HV Y]
    [TopologicalSpace M] [ChartedSpace HE M] {F : X → M} {G : Y → M} {f : A → M} {g : B → M}
    {u : X → A} {v : Y → B} {x : X} {y : Y} (hf : MDifferentiableAt 𝓘(ℝ, A) J f 0)
    (hg : MDifferentiableAt 𝓘(ℝ, B) J g 0) (hu : MDifferentiableAt I 𝓘(ℝ, A) u x)
    (hv : MDifferentiableAt I' 𝓘(ℝ, B) v y) (hu0 : u x = 0) (hv0 : v y = 0)
    (hF : F =ᶠ[𝓝 x] (f ∘ u)) (hG : G =ᶠ[𝓝 y] (g ∘ v)) (hcross : G y = F x)
    (htrans : NativeTransversality.At I I' J F G x y) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) J f g 0 0 := by
  have hfx : MDifferentiableAt 𝓘(ℝ, A) J f (u x) := hu0 ▸ hf
  have hgy : MDifferentiableAt 𝓘(ℝ, B) J g (v y) := hv0 ▸ hg
  have hFd :
    (mfderiv I J F x : U →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, A) J f 0 : A →L[ℝ] E).comp (mfderiv I 𝓘(ℝ, A) u x) := by
    have heq : (mfderiv I J F x : U →L[ℝ] E) = mfderiv I J (f ∘ u) x := hF.mfderiv_eq
    rw [heq, mfderiv_comp x hfx hu, hu0]
  have hGd :
    (mfderiv I' J G y : V →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, B) J g 0 : B →L[ℝ] E).comp (mfderiv I' 𝓘(ℝ, B) v y) := by
    have heq : (mfderiv I' J G y : V →L[ℝ] E) = mfderiv I' J (g ∘ v) y := hG.mfderiv_eq
    rw [heq, mfderiv_comp y hgy hv, hv0]
  intro _ z
  obtain ⟨⟨a, b⟩, hab⟩ := htrans hcross z
  refine ⟨(mfderiv I 𝓘(ℝ, A) u x a, mfderiv I' 𝓘(ℝ, B) v y b), ?_⟩
  rw [hFd, hGd] at hab
  exact hab

/-- A native plane factorization exists. -/
theorem TransverseGerms.exists_native_plane_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (fun y => P (L (u y))) := by
  let u : X → A := fun y => R (P.symm (F y))
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hi := (P.symm.mdifferentiableAt (by simp) hxt).comp x hF
  have hu : MDifferentiableAt I 𝓘(ℝ, A) u x := R.differentiableAt.mdifferentiableAt.comp x hi
  have hu0 : u x = 0 := by
    change R (P.symm (F x)) = 0
    have hi0 : P.symm (P 0) = 0 := P.left_inv' hP0
    rw [hx, hi0, map_zero]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hplane] with y hy hplaneY
  obtain ⟨a, ha⟩ := hplaneY
  change F y = P (L (R (P.symm (F y))))
  rw [ha, hRL]
  exact (P.right_inv' hy).symm.trans (congrArg P ha)

/-- A native plane sheet factorization exists. -/
theorem TransverseGerms.exists_native_plane_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) {f : A → M}
    (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := exists_native_plane_factorization P hP0 L R hRL hF hx hplane
  have hut : Filter.Tendsto u (𝓝 x) (𝓝 (0 : A)) := hu0 ▸ hu.continuousAt
  have hcomp := hmodel.comp_tendsto hut
  exact ⟨u, hu, hu0, hfactor.trans hcomp.symm⟩

/-- A native basin sheet factorization exists. -/
theorem TransverseGerms.exists_native_basin_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0) (Basin : M → Prop)
    (hbasin : ∀ z ∈ P.source, Basin (P z) → ∃ a, z = L a) (hFbasin : ∀ᶠ y in 𝓝 x, Basin (F y))
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a := by
    filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hFbasin] with y hy hby
    have hb : Basin (P (P.symm (F y))) := (P.right_inv' hy).symm ▸ hby
    exact hbasin (P.symm (F y)) (P.map_target' hy) hb
  exact exists_native_plane_sheet_factorization P hP0 L R hRL hF hx hplane hmodel

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing basin factorization. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atBot (𝓝 q)) :
    ∃ u : X → ℝ × MorseHandle.NegativeSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.outgoingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.outgoing_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × A) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inl ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ A)).prod
      (ContinuousLinearMap.fst ℝ ℝ A)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × A) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × A) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.1), ?_⟩
    exact Prod.ext (Prod.ext rfl hz) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q)) hp
      hbasin hmodel

attribute [local instance 100] Classical.propDecidable in
/-- The incoming basin factorization. -/
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atTop (𝓝 p)) :
    ∃ u : X → ℝ × MorseHandle.PositiveSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.incomingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.incoming_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × B) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inr ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ B)).prod
      (ContinuousLinearMap.fst ℝ ℝ B)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × B) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × B) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.2), ?_⟩
    exact Prod.ext (Prod.ext hz rfl) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p)) hp
      hbasin hmodel

/-- The native basin sheets are transverse. -/
theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y) : D.Transverse := by
  obtain ⟨u, hu, hu0, hFu⟩ := D.outgoing_basin_factorization hF hx hFbasin
  obtain ⟨v, hv, hv0, hGv⟩ := D.incoming_basin_factorization hG hy hGbasin
  apply D.transverse_of_native_sheets
  exact
    TransverseGerms.native_transversality_of_sheet_factorizations
      (D.outgoingSheet_properties.1.mdifferentiableAt (by simp))
      (D.incomingSheet_properties.1.mdifferentiableAt (by simp)) hu hv hu0 hv0 hFu hGv
      (hy.trans hx.symm) htrans

/-- Transverse basin sheets give a cancellation. -/
theorem MorseCancellation.NativeConnectionCancellationData.cancel_of_transverse_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc c d → z = p ∨ z = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ z,
                z ∈ ManifoldMorse.criticalPoints E g ↔
                  z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
              ∀ z, f z ∉ Set.Ioo c d → g =ᶠ[𝓝 z] f :=
  D.cancel (D.transverse_of_native_basin_sheets hF hG hx hy hFbasin hGbasin htrans) hf hm hinj hp
    hq hpq hc hd hpair

attribute [local instance 100] Classical.propDecidable in
/-- A unique connection with transverse basin sheets cancels. -/
theorem MorseCancellation.cancel_unique_connection_of_transverse_basin_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q z : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x)
    {S : X → M} {T : Y → M} {x : X} {y : Y} (hS : MDifferentiableAt I 𝓘(ℝ, E) S x)
    (hT : MDifferentiableAt I' 𝓘(ℝ, E) T y) (hS0 : S x = z) (hT0 : T y = z)
    (hSbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q))
    (hTbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) S T x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨D, -, hgeometry, t₀, ht₀⟩ :=
    exists_native_connection_cancellation_data cp cq hf hdim hindex V hV hzero hdesc F hF hpc hqc
      hpq hc hd hpair hp hq hunique heqp heqq
  let τ := SmoothODE.nativeFlowTimeDiffeomorph_of_field hV F hF t₀
  have hτ (u : M) : τ u = F t₀ u := rfl
  have hS' : MDifferentiableAt I 𝓘(ℝ, E) (τ ∘ S) x :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp x hS
  have hT' : MDifferentiableAt I' 𝓘(ℝ, E) (τ ∘ T) y :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp y hT
  have hS0' : (τ ∘ S) x = D.A 0 := by rw [Function.comp_apply, hτ, hS0, ht₀]
  have hT0' : (τ ∘ T) y = D.A 0 := by rw [Function.comp_apply, hτ, hT0, ht₀]
  have hSb : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => D.flow t ((τ ∘ S) u)) Filter.atBot (𝓝 q) := by
    filter_upwards [hSbasin] with u hu
    apply ((hgeometry ((τ ∘ S) u)).2.2 q).mpr
    exact (flow_time_atBot_limit_iff F t₀ (S u) q).mpr hu
  have hTb : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => D.flow t ((τ ∘ T) u)) Filter.atTop (𝓝 p) := by
    filter_upwards [hTbasin] with u hu
    apply ((hgeometry ((τ ∘ T) u)).2.1 p).mpr
    exact (flow_time_atTop_limit_iff F t₀ (T u) p).mpr hu
  have ht : NativeTransversality.At I I' 𝓘(ℝ, E) (τ ∘ S) (τ ∘ T) x y :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff τ.toPartialDiffeomorph
          hS hT (hT0.trans hS0.symm) (Set.mem_univ _)).mp
      htrans
  exact
    D.cancel_of_transverse_basin_sheets hS' hT' hS0' hT0' hSb hTb ht hf hm hinj hpc hqc hpq hc hd
      hpair

attribute [local instance 100] Classical.propDecidable in
/-- The cancellation theorem: a unique transverse connection can be cancelled by a level isotopy. -/
theorem MorseCancellation.cancel_of_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (z : M) → TangentSpace 𝓘(ℝ, E) z)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0)
    (hdesc : ∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0)
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) {l u a b c : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (ha : a < c) (hb : c < b) (hpc' : f p < c) (hqc' : c < f q)
    (hband : ∀ z, f z ∈ Set.Icc a b → z ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    (heqp : ∀ᶠ z in 𝓝 p, V z = cp.descentField z) (heqq : ∀ᶠ z in 𝓝 q, V z = cq.descentField z) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { z : M // f z = c } { z : M // f z = c } ∞,
      SupportedDiffeomorph.IsotopicToIdentity D →
        {z : { w : M // f w = c } |
                Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
                  Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)}.ncard =
            1 →
          ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
                β y = α x →
                  NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
                    (∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => F t (α z)) Filter.atBot (𝓝 q)) →
                      (∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => F t (D (β z))) Filter.atTop (𝓝 p)) →
                        ∃ g : M → ℝ,
                          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                            ManifoldMorse.IsMorse E g ∧
                              (ManifoldMorse.criticalPoints E g).ncard + 2 =
                                  (ManifoldMorse.criticalPoints E f).ncard ∧
                                (∀ z,
                                    z ∈ ManifoldMorse.criticalPoints E g ↔
                                      z ∈ ManifoldMorse.criticalPoints E f ∧
                                        z ≠ p ∧ z ≠ q) ∧
                                  ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro D hD hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain
    ⟨r, C, W, V', H, G, -, -, -, -, -, -, hgeometry, hV', hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf hV hdesc F hF ha hb
      hband hreg (α x) D hD
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy F H G Subtype.val D
      (fun z => (hgeometry z).2.1) (fun z => (hgeometry z).2.2) hend hleft hright
  have hαb : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => G t (α z)) Filter.atBot (𝓝 q) := by
    filter_upwards [hαbasin] with z hz
    exact (hback (α z) q).mpr hz
  have hβb : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => G t (β z)) Filter.atTop (𝓝 p) := by
    filter_upwards [hβbasin] with z hz
    exact (hforward (β z) p).mpr hz
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hαq : Filter.Tendsto (fun t => F t (α x)) Filter.atBot (𝓝 q) := hαbasin.self_of_nhds
  have hαp : Filter.Tendsto (fun t => F t (D (α x))) Filter.atTop (𝓝 p) := by
    rw [← hcross]
    exact hβbasin.self_of_nhds
  have hαeq : α x = z₀ := by
    have hh :
      α x ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hαq, hαp⟩
    rw [hz₀] at hh
    exact Set.mem_singleton_iff.mp hh
  have huniq (z : { w : M // f w = c }) (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hzp : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)) : z = α x := by
    have hh :
      z ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hzq, hzp⟩
    rw [hz₀] at hh
    exact (Set.mem_singleton_iff.mp hh).trans hαeq.symm
  obtain ⟨hqG, hpG, huniqueG⟩ :=
    FlowSuspension.unique_connection_of_level_basin_intersection F G hf.continuous hqc'
      hpc' D (fun z => hback z q) (fun z => hforward z p) (α x) hαq hαp huniq
  obtain ⟨hS, hT, hS0, hT0, hSb, hTb, ht⟩ :=
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf hreg hV' G hG
      (fun z hz => hneg z (hreg z hz)) α β x y hα hβ hcross htrans hαb hβb
  have hgermp : ∀ᶠ z in 𝓝 p, V' z = cp.descentField z := by
    filter_upwards [hgerms p hpc, heqp] with z hz hz'
    exact hz.trans hz'
  have hgermq : ∀ᶠ z in 𝓝 q, V' z = cq.descentField z := by
    filter_upwards [hgerms q hqc, heqq] with z hz hz'
    exact hz.trans hz'
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V' hV'
      (fun z hz => (hzeros z).mpr (hzero z hz)) hneg G hG hinj hpc hqc (hpc'.trans hqc') hl hu
      hpair hpG hqG huniqueG hgermp hgermq hS hT hS0 hT0 hSb hTb ht

/-! ### The Morse count after pair removal -/

/-- The number of Morse critical points. -/
def MorseCancellation.nativeMorseCount (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) : ℕ :=
  {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.ncard

/-- The indexed critical points after removing a pair. -/
theorem MorseCancellation.indexed_criticalPoints_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    {z : M | z ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hzg, hindex⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hzg
    rw [nativeMorseIndex_congr_germ (hkeep z hzg)] at hindex
    exact ⟨⟨hzf, hindex⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hindex⟩, hzp, hzq⟩
    have hzg := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hzg, (nativeMorseIndex_congr_germ (hkeep z hzg)).trans hindex⟩

attribute [local instance 100] Classical.propDecidable in
/-- The index-`k` Morse count of the new function plus the removed pair's index-`k` contributions equals that of the old. -/
theorem MorseCancellation.nativeMorseCount_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_after_pair_removal hcrit hkeep k]
  exact (Nat.add_assoc _ _ _).trans hc

attribute [local instance 100] Classical.propDecidable in
/-- Removing an adjacent-index pair lowers the counts at the two indices by one each and fixes the others. -/
theorem MorseCancellation.nativeMorseCount_adjacent_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) {k : ℕ}
    (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_after_pair_removal hfinite hp hq hpq hcrit hkeep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

end
