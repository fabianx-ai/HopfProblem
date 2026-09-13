/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Geometry.Manifold.Morse.ConnectionCancellation

/-!
# Birth of a pair of Morse critical points

`MorseCancellation.exists_excellent_indexed_morse_birth` inserts two critical
points of prescribed adjacent indices `k` and `k + 1` in a specified open
neighborhood of a regular point, with `k < Module.finrank ℝ E`. For an
excellent Morse function on a compact smooth manifold and a critical-point-free
value band, the new function remains excellent, keeps all old critical germs,
and agrees with the old function outside the neighborhood. The new values
lie in the band, and the indexed critical-point counts increase by exactly
one in each of the two prescribed degrees.

## Outline of the proof

1. Build the exact local cubic birth and its positive-height coordinates
   (`exists_exact_cubic_birth`, `exists_positive_cubic_height_diffeomorph`).
2. Insert the model in a centered native height chart, preserving the exterior
   germs (`insert_morse_chart_pair`, `exists_native_morse_birth`).
3. Separate the new critical values from the old ones
   (`exists_excellent_native_morse_birth`).
4. Compute the indices from the signed cubic germs and count the new pair
   (`native_indices_of_cubic_birth_germs`, `exists_excellent_indexed_morse_birth`).

The local cubic model is the coordinate model underlying Morse cancellation;
this file gives its explicit reverse construction with support and counting
control rather than asserting that cancellation alone supplies a birth.

## Main definitions and results

* `MorseCancellation.exists_exact_cubic_birth`.
* `MorseCancellation.exists_excellent_native_morse_birth`.
* `MorseCancellation.exists_excellent_indexed_morse_birth`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §5
  (the local cancellation model).

## Tags

morse-theory, birth, cubic-model, critical-points
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

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def MorseCancellation.cancelled {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ (-t) p + 2 * t * φ p * p.1

theorem MorseCancellation.contDiff_cancelled_family {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Function.uncurry (cancelled σ φ)) := by
  exact
    ((contDiff_cubic_family σ).comp (contDiff_fst.neg.prodMk contDiff_snd)).add
      (((contDiff_const.mul contDiff_fst).mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

theorem MorseCancellation.cancelled_zero {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) :
    cancelled σ φ 0 = cubic σ 0 := by
  funext p
  simp [cancelled]

theorem MorseCancellation.cancelled_germ_plateau {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    {U : Set (Model m)} (hU : IsOpen U) (hφU : Set.EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [cancelled, cubic, hφU hq]
  ring

theorem MorseCancellation.cancelled_eq_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t p = cubic σ (-t) p := by
  simp [cancelled, image_eq_zero_of_notMem_tsupport hp]

theorem MorseCancellation.cancelled_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ (-t) := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact cancelled_eq_off_support σ φ t hq

theorem MorseCancellation.exists_exact_cubic_birth {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {U : Set (Model m)}
    (hU : IsOpen U) (h0 : (0 : Model m) ∈ U) (hφU : Set.EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ,
      0 < a ∧
        (a, (0 : Fin m → ℝ)) ∈ U ∧
          (-a, (0 : Fin m → ℝ)) ∈ U ∧
            ∃ g : Model m → ℝ,
              ContDiff ℝ ∞ g ∧
                (∀ p, fderiv ℝ g p = 0 ↔ p = (a, 0) ∨ p = (-a, 0)) ∧
                  (∀ p ∈ U, g =ᶠ[𝓝 p] cubic σ (-(a ^ 2))) ∧
                    ∀ p, p ∉ tsupport φ → g =ᶠ[𝓝 p] cubic σ (a ^ 2) := by
  let K := tsupport φ \ U
  have hK : IsCompact K := hc.diff hU
  have hD :=
    (MorsePerturbation.contDiff_spatialDerivative
        (contDiff_cancelled_family σ hφ)).continuous
  have hO : IsOpen {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} :=
    MorsePerturbation.isOpen_forall_mem_compact hK
      (isClosed_eq hD continuous_const).isOpen_compl
  have hO0 : (0 : ℝ) ∈ {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} := by
    intro p hp hcrit
    rw [cancelled_zero] at hcrit
    exact hp.2 ((cubic_zero_unique_critical σ hσ p).mp hcrit ▸ h0)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO0)
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨a, ha, har⟩ := exists_between (lt_min hr (lt_min zero_lt_one hδ))
  have ha1 : a < 1 := (lt_min_iff.mp (lt_min_iff.mp har).2).1
  have haδ : a < δ := (lt_min_iff.mp (lt_min_iff.mp har).2).2
  have haa : a ^ 2 < δ := by nlinarith
  have htrans : ∀ p ∈ K, fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 :=
    hδball (by simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg a)] using haa)
  have hp : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have hq : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine
    ⟨a, ha, hp, hq, cancelled σ φ (-(a ^ 2)),
      (contDiff_cancelled_family σ hφ).comp (contDiff_const.prodMk contDiff_id), ?_,
      (fun p hpU => cancelled_germ_plateau σ hU hφU _ hpU), ?_⟩
  · intro p
    by_cases hpU : p ∈ U
    · rw [(cancelled_germ_plateau σ hU hφU (-(a ^ 2)) hpU).fderiv_eq]
      exact negative_parameter_critical_iff σ hσ a p
    · have hreg : fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 := by
        by_cases hpS : p ∈ tsupport φ
        · exact htrans p ⟨hpS, hpU⟩
        · rw [(cancelled_germ_off_support σ φ (-(a ^ 2)) hpS).fderiv_eq, neg_neg]
          exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p
      constructor
      · exact fun h => False.elim (hreg h)
      · rintro (rfl | rfl)
        · exact False.elim (hpU hp)
        · exact False.elim (hpU hq)
  · intro p hpS
    simpa only [neg_neg] using cancelled_germ_off_support σ φ (-(a ^ 2)) hpS

theorem MorseCancellation.exists_positive_scalar_cubic_diffeomorph {a : ℝ} (ha : 0 < a) :
    ∃ e : ℝ ≃ₘ[ℝ] ℝ, ∀ s, e s = s ^ 3 / 3 + a ^ 2 * s := by
  let g : ℝ → ℝ := fun s => s ^ 3 / 3 + a ^ 2 * s
  have hg : ContDiff ℝ ∞ g := by unfold g; fun_prop
  have hd (s : ℝ) : HasDerivAt g (s ^ 2 + a ^ 2) s := by
    convert!
      (((hasDerivAt_id s).pow 3).div_const 3).add ((hasDerivAt_id s).const_mul (a ^ 2)) using 1;
    simp
  have hpos (s : ℝ) : 0 < s ^ 2 + a ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg s) (sq_pos_of_pos ha)
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd hpos
  have hbound {s t : ℝ} (hst : s ≤ t) : a ^ 2 * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; exact le_add_of_nonneg_left (sq_nonneg x)) hst
  have hzero : g 0 = 0 := by simp [g]
  have hsurj : Function.Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨Min.min 0 (y / a ^ 2), ?_⟩
      have hh := hbound (min_le_left 0 (y / a ^ 2))
      have hm : a ^ 2 * Min.min 0 (y / a ^ 2) ≤ y := by
        calc
          a ^ 2 * Min.min 0 (y / a ^ 2) ≤ a ^ 2 * (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg a)
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨Max.max 0 (y / a ^ 2), ?_⟩
      have hh := hbound (le_max_left 0 (y / a ^ 2))
      have hm : y ≤ a ^ 2 * Max.max 0 (y / a ^ 2) := by
        calc
          y = a ^ 2 * (y / a ^ 2) := by field_simp
          _ ≤ a ^ 2 * Max.max 0 (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg a)
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  have hi : ContDiff ℝ ∞ c.toHomeomorph.symm :=
    c.toHomeomorph.contDiff_symm_deriv (fun s => (hpos s).ne') hd hg
  let e : ℝ ≃ₘ[ℝ] ℝ :=
    { toEquiv := c.toEquiv
      contMDiff_toFun := hg.contMDiff
      contMDiff_invFun := hi.contMDiff }
  exact ⟨e, fun _ => rfl⟩

theorem MorseCancellation.exists_positive_cubic_height_diffeomorph {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ∃ D : Model m ≃ₘ[ℝ] Model m, ∀ p, D p = (cubic σ (a ^ 2) p, p.2) := by
  obtain ⟨e, he⟩ := exists_positive_scalar_cubic_diffeomorph ha
  let Q : (Fin m → ℝ) → ℝ := fun z => ∑ i, σ i * z i ^ 2
  have hQ : ContDiff ℝ ∞ Q := by unfold Q; fun_prop
  have hec : ContDiff ℝ ∞ e := contMDiff_iff_contDiff.mp e.contMDiff
  have hei : ContDiff ℝ ∞ e.symm := contMDiff_iff_contDiff.mp e.symm.contMDiff
  let D : Model m ≃ₘ[ℝ] Model m :=
    { toFun := fun p => (e p.1 + Q p.2, p.2)
      invFun := fun p => (e.symm (p.1 - Q p.2), p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((hec.comp contDiff_fst |>.add (hQ.comp contDiff_snd)).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hei.comp (contDiff_fst.sub (hQ.comp contDiff_snd))).prodMk contDiff_snd).contMDiff }
  refine ⟨D, ?_⟩
  intro p
  change (e p.1 + Q p.2, p.2) = _
  rw [he]
  rfl

theorem MorseCancellation.hessian_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E ≃L[ℝ] F) (x : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap).comp
        ((fderiv ℝ (fderiv ℝ f) (L x)).comp L.toContinuousLinearMap) := by
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hgrad : fderiv ℝ (f ∘ L) = fun y => A (fderiv ℝ f (L y)) := by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) (L y)) L.differentiableAt, L.fderiv]
    rfl
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hgrad]
  exact
    (A.hasFDerivAt.comp x
        ((hdf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)).fderiv

theorem MorseCancellation.euclidean_isMorse_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (hm : MorsePerturbation.IsMorse f) (L : E ≃L[ℝ] F) :
    MorsePerturbation.IsMorse (f ∘ L) := by
  intro x hx
  have hcrit : fderiv ℝ f (L x) = 0 := by
    rw [fderiv_comp x (hf.differentiable (by simp) (L x)) L.differentiableAt, L.fderiv] at hx
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := L.surjective v
    exact congrArg (fun k : E →L[ℝ] ℝ => k w) hx
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hA : Function.Bijective A := by
    constructor
    · intro k l hkl
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := L.surjective v
      exact congrArg (fun k : E →L[ℝ] ℝ => k w) hkl
    · intro k
      refine ⟨k.comp L.symm.toContinuousLinearMap, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      change k (L.symm (L v)) = k v
      rw [L.symm_apply_apply]
  rw [hessian_comp_linearEquiv hf L]
  exact hA.comp ((hm (L x) hcrit).comp L.bijective)

theorem MorseCancellation.isMorseAt_of_native_model_germ {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞) (L : E ≃L[ℝ] F) {f : M → ℝ} {b : F → ℝ} {p : F}
    (hp : p ∈ Φ.source) (hb : ContDiff ℝ ∞ b) (hmb : MorsePerturbation.IsMorse b)
    (hmodel : f ∘ Φ =ᶠ[𝓝 p] b) : ManifoldMorse.IsMorseAt E f (Φ p) := by
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hpΨ : Φ p ∈ Ψ.target := by exact ⟨Φ.map_source' hp, Set.mem_univ _⟩
  have he : Ψ.symm.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    Ψ.symm.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Ψ.contMDiffOn_invFun
      Ψ.contMDiffOn_toFun
  apply
    ManifoldMorse.isMorseAt_of_chart_eventuallyEq he hpΨ
      (euclidean_isMorse_comp_linearEquiv hb hmb L)
  have hcenter : Ψ.symm (Φ p) = L.symm p := by
    change L.symm (Φ.symm (Φ p)) = L.symm p
    exact congrArg L.symm (Φ.left_inv' hp)
  change f ∘ Ψ =ᶠ[𝓝 (Ψ.symm (Φ p))] b ∘ L
  rw [hcenter]
  have ht : Filter.Tendsto L (𝓝 (L.symm p)) (𝓝 p) := by
    simpa only [L.apply_symm_apply] using L.continuous.continuousAt.tendsto (x := L.symm p)
  exact hmodel.comp_tendsto ht

theorem MorseCancellation.euclidean_isMorse_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : MorsePerturbation.IsMorse f) {c : ℝ}
    (hc : c ≠ 0) (b : ℝ) : MorsePerturbation.IsMorse (fun x => b + c * f x) := by
  have hgrad : fderiv ℝ (fun x => b + c * f x) = fun x => c • fderiv ℝ f x := by
    funext x
    rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by simp) x)]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  intro x hx
  rw [hgrad] at hx ⊢
  have hcrit : fderiv ℝ f x = 0 := (smul_eq_zero.mp hx).resolve_left hc
  change Function.Bijective (fderiv ℝ (c • fderiv ℝ f) x)
  rw [fderiv_const_smul (hdf.differentiable (by simp) x)]
  exact (isUnit_iff_ne_zero.mpr hc).smul_bijective.comp (hm x hcrit)

theorem MorseCancellation.exists_pos_compact_smul_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (h0 : (0 : E) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ (fun x : E => δ • x) '' K ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R := Max.max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C < R := by dsimp [R]; linarith [le_max_left C 0]
  let δ := r / (2 * R)
  have hδ : 0 < δ := div_pos hr (mul_pos (by norm_num) hR)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hrU
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hnorm : ‖x‖ < R := (hC x hx).trans_lt hCR
  have hm : δ * ‖x‖ < δ * R := mul_lt_mul_of_pos_left hnorm hδ
  have heq : δ * R = r / 2 := by dsimp [δ]; field_simp
  rw [heq] at hm
  linarith

theorem MorseCancellation.exists_centered_native_height_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (0 : Model m) ∈ Φ.source ∧ Φ 0 = x ∧ Φ.target ⊆ U ∧ ∀ p ∈ Φ.source, f (Φ p) = f x + p.1 := by
  obtain ⟨Q, hxQ, hQ, hQx⟩ := RegularLevel.exists_native_height_chart hf hx
  have hdim' : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [Module.finrank_pi, Fintype.card_fin, RegularLevel.Model,
      finrank_euclideanSpace_fin]
    omega
  let L : (Fin m → ℝ) ≃L[ℝ] RegularLevel.Model E := ContinuousLinearEquiv.ofFinrankEq hdim'
  let D :
    Diffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, ℝ × RegularLevel.Model E) (Model m)
      (ℝ × RegularLevel.Model E) ∞ :=
    { toFun := fun p => (f x + p.1, L p.2)
      invFun := fun p => (p.1 - f x, L.symm p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((contDiff_const.add contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)).contMDiff
      contMDiff_invFun :=
        ((contDiff_fst.sub contDiff_const).prodMk (L.symm.contDiff.comp contDiff_snd)).contMDiff }
  let P := D.toPartialDiffeomorph.trans Q.symm
  let Φ := PartialChart.restrictTarget P hU
  have hD0 : D 0 = Q x := by
    rw [hQx]
    change (f x + (0 : ℝ), L 0) = (f x, 0)
    simp
  have h0P : (0 : Model m) ∈ P.source := by
    change (0 : Model m) ∈ Set.univ ∧ D 0 ∈ Q.target
    exact ⟨Set.mem_univ _, hD0.symm ▸ Q.map_source' hxQ⟩
  have hP0 : P 0 = x := by
    change Q.symm (D 0) = x
    rw [hD0]
    exact Q.left_inv' hxQ
  have h0Φ : (0 : Model m) ∈ Φ.source := by
    change (0 : Model m) ∈ P.source ∧ P 0 ∈ U
    exact ⟨h0P, hP0.symm ▸ hxU⟩
  refine ⟨Φ, h0Φ, hP0, fun _ hy => hy.2, ?_⟩
  intro p hp
  have hpt : D p ∈ Q.target := hp.1.2
  have hh := hQ (Q.symm (D p)) (Q.map_target' hpt)
  have hright : Q (Q.symm (D p)) = D p := Q.right_inv' hpt
  rw [hright] at hh
  exact hh.symm

theorem MorseCancellation.insert_morse_chart_pair {E D M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (L : E ≃L[ℝ] D) {f : M → ℝ} {b₀ b₁ : D → ℝ}
    {K : Set D} {p q : D} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hb₀ : ContDiff ℝ ∞ b₀) (hb₁ : ContDiff ℝ ∞ b₁)
    (hmb₁ : MorsePerturbation.IsMorse b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) (hp : p ∈ Φ.source)
    (hq : q ∈ Φ.source) (hpq : p ≠ q) (hreg : ∀ x, fderiv ℝ b₀ x ≠ 0)
    (hcrit : ∀ x, fderiv ℝ b₁ x = 0 ↔ x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard =
              (ManifoldMorse.criticalPoints E f).ncard + 2 ∧
            (∀ y,
                y ∈ ManifoldMorse.criticalPoints E g ↔
                  y ∈ ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q) ∧
              (∀ y, y ∉ Φ '' K → g =ᶠ[𝓝 y] f) ∧
                (∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                  ∀ z ∈ Φ.source, g (Φ z) = b₁ z := by
  let g := LocalFunctionReplacement.replace Φ f b₁
  have hg := LocalFunctionReplacement.contMDiff_replace Φ hf hb₁ hK hKΦ hmodel hfix
  have houtside (y : M) (hy : y ∉ Φ '' K) : g =ᶠ[𝓝 y] f :=
    LocalFunctionReplacement.replace_germ_off_support Φ hK hKΦ hmodel hfix hy
  have hnot (y : M) (hy : y ∈ Φ.target) : y ∉ ManifoldMorse.criticalPoints E f := by
    intro hc
    have he := LocalFunctionReplacement.replace_critical_iff Φ f hb₀ hy
    rw [LocalFunctionReplacement.replace_self Φ hmodel] at he
    exact hreg (Φ.symm y) (he.mp hc)
  have hcritg (y : M) :
    y ∈ ManifoldMorse.criticalPoints E g ↔
      y ∈ ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q := by
    by_cases hy : y ∈ Φ.target
    · have he := LocalFunctionReplacement.replace_critical_iff Φ f hb₁ hy
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
      rw [he, hcrit]
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inl ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
        · exact Or.inr (Or.inr ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
      · rintro (hc | rfl | rfl)
        · exact False.elim (hnot y hy hc)
        · exact Or.inl (Φ.left_inv' hp)
        · exact Or.inr (Φ.left_inv' hq)
    · have hyK : y ∉ Φ '' K := by
        rintro ⟨z, hz, rfl⟩
        exact hy (Φ.map_source' (hKΦ hz))
      have hyp : y ≠ Φ p := fun h => hy (h.symm ▸ Φ.map_source' hp)
      have hyq : y ≠ Φ q := fun h => hy (h.symm ▸ Φ.map_source' hq)
      have he :
        y ∈ ManifoldMorse.criticalPoints E g ↔ y ∈ ManifoldMorse.criticalPoints E f :=
        by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
        rw [(houtside y hyK).mfderiv_eq]
        rfl
      simpa only [hyp, hyq, or_false] using he
  have hmg : ManifoldMorse.IsMorse E g := by
    intro y
    by_cases hy : y ∈ Φ.target
    · have hx := Φ.map_target' hy
      have hmodelg : g ∘ Φ =ᶠ[𝓝 (Φ.symm y)] b₁ := by
        filter_upwards [Φ.open_source.mem_nhds hx] with z hz
        exact LocalFunctionReplacement.replace_chart Φ f b₁ hz
      have hh := isMorseAt_of_native_model_germ Φ L hx hb₁ hmb₁ hmodelg
      have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
      exact hright ▸ hh
    · apply MorseCancellationPreservation.isMorseAt_of_same_germ (hm y)
      apply houtside y
      rintro ⟨z, hz, rfl⟩
      exact hy (Φ.map_source' (hKΦ hz))
  have hneq : Φ p ≠ Φ q := fun h => hpq (Φ.toOpenPartialHomeomorph.injOn hp hq h)
  have hpnot := hnot (Φ p) (Φ.map_source' hp)
  have hqnot := hnot (Φ q) (Φ.map_source' hq)
  have heq :
    ManifoldMorse.criticalPoints E g =
      Insert.insert (Φ p) (Insert.insert (Φ q) (ManifoldMorse.criticalPoints E f)) := by
    ext y
    rw [hcritg]
    simp only [Set.mem_insert_iff]
    tauto
  refine
    ⟨g, hg, hmg, ?_, hcritg, houtside, ?_, fun z hz =>
      LocalFunctionReplacement.replace_chart Φ f b₁ hz⟩
  · rw [heq,
      Set.ncard_insert_of_notMem
        (by simp only [Set.mem_insert_iff, hneq, hpnot, or_self, not_false_eq_true])
        ((ManifoldMorse.finite_criticalPoints hf hm).insert (Φ q)),
      Set.ncard_insert_of_notMem hqnot (ManifoldMorse.finite_criticalPoints hf hm)]
  · intro y hy
    apply houtside y
    rintro ⟨z, hz, rfl⟩
    exact hnot (Φ z) (Φ.map_source' (hKΦ hz)) hy

theorem MorseCancellation.exists_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  (∀ z ∈ Φ.source, f (Φ z) = f x + δ * cubic σ (a ^ 2) z) ∧
                    ∃ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                        ManifoldMorse.IsMorse E g ∧
                          (ManifoldMorse.criticalPoints E g).ncard =
                              (ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ ManifoldMorse.criticalPoints E g ↔
                                  y ∈ ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                    (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                      f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain ⟨H, h0H, -, hHU, hH⟩ := exists_centered_native_height_chart hf hx hdim hU hxU
  obtain ⟨φ, hφ, hc, -, W, hW, h0W, hφW⟩ :=
    NativeCubicCancellation.exists_cutoff (m := m) isOpen_univ (Set.mem_univ _)
  obtain ⟨a, ha, hpW, hqW, b, hb, hcritb, hgerms, hfix⟩ :=
    exists_exact_cubic_birth σ hσ hφ hc hW h0W hφW
  have hmb : MorsePerturbation.IsMorse b := by
    intro z hz
    have hzW : z ∈ W := (hcritb z).mp hz |>.elim (fun h => h ▸ hpW) (fun h => h ▸ hqW)
    have heq := hgerms z hzW
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    apply cubic_isMorse σ hσ (neg_ne_zero.mpr (pow_ne_zero 2 ha.ne'))
    rw [← heq.fderiv_eq]
    exact hz
  obtain ⟨D, hD⟩ := exists_positive_cubic_height_diffeomorph σ ha
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_compact_smul_subset (hc.image D.continuous) H.open_source h0H
  let A : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) δ hδ.ne').toContinuousLinearEquiv
  let C := D.trans A.toDiffeomorph
  let Φ := C.toPartialDiffeomorph.trans H
  have hC (z : Model m) : C z = δ • D z := rfl
  have hKΦ : tsupport φ ⊆ Φ.source := by
    intro z hz
    change z ∈ Set.univ ∧ C z ∈ H.source
    exact ⟨Set.mem_univ _, hsmall ⟨D z, Set.mem_image_of_mem D hz, rfl⟩⟩
  have hWK : W ⊆ tsupport φ := by
    intro z hz
    apply subset_tsupport φ
    change φ z ≠ 0
    rw [hφW hz]
    norm_num
  have hpΦ := hKΦ (hWK hpW)
  have hqΦ := hKΦ (hWK hqW)
  have hΦU : Φ.target ⊆ U := fun _ hy => hHU hy.1
  let b₀ : Model m → ℝ := fun z => f x + δ * cubic σ (a ^ 2) z
  let b₁ : Model m → ℝ := fun z => f x + δ * b z
  have hb₀ : ContDiff ℝ ∞ b₀ := contDiff_const.add (contDiff_const.mul (contDiff_cubic σ _))
  have hb₁ : ContDiff ℝ ∞ b₁ := contDiff_const.add (contDiff_const.mul hb)
  have hmb₁ : MorsePerturbation.IsMorse b₁ := euclidean_isMorse_affine hb hmb hδ.ne' (f x)
  have hmodel (z : Model m) (hz : z ∈ Φ.source) : f (Φ z) = b₀ z := by
    change f (H (C z)) = _
    rw [hH (C z) hz.2, hC, hD]
    rfl
  have hfix₁ (z : Model m) (hz : z ∉ tsupport φ) : b₁ z = b₀ z := by
    dsimp [b₁, b₀]
    rw [(hfix z hz).self_of_nhds]
  have hderiv (v : Model m → ℝ) (hv : ContDiff ℝ ∞ v) (z : Model m) :
    fderiv ℝ (fun y => f x + δ * v y) z = δ • fderiv ℝ v z := by
    rw [fderiv_const_add, fderiv_const_mul (hv.differentiable (by simp) z)]
  have hreg₀ (z : Model m) : fderiv ℝ b₀ z ≠ 0 := by
    rw [hderiv _ (contDiff_cubic σ _) z]
    exact smul_ne_zero hδ.ne' (positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) z)
  have hcrit₁ (z : Model m) : fderiv ℝ b₁ z = 0 ↔ z = (a, 0) ∨ z = (-a, 0) := by
    rw [hderiv b hb z, smul_eq_zero]
    simp only [hδ.ne', false_or, hcritb]
  have hpq : (a, (0 : Fin m → ℝ)) ≠ (-a, 0) := by
    intro h
    have hh := congrArg Prod.fst h
    change a = -a at hh
    linarith
  let L : E ≃L[ℝ] Model m :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Model, Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
          Fintype.card_fin]
        exact hdim.symm)
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior, hkeep, hnew⟩ :=
    insert_morse_chart_pair Φ L hf hm hb₀ hb₁ hmb₁ hc hKΦ hmodel hfix₁ hpΦ hqΦ hpq hreg₀ hcrit₁
  have hend (z : Model m) (hzΦ : z ∈ Φ.source) (hzW : z ∈ W) :
    g ∘ Φ =ᶠ[𝓝 z] fun w => f x + δ * cubic σ (-(a ^ 2)) w := by
    filter_upwards [Φ.open_source.mem_nhds hzΦ, hgerms z hzW] with w hw heq
    change g (Φ w) = _
    rw [hnew w hw]
    change f x + δ * b w = _
    rw [heq]
  refine
    ⟨a, δ, ha, hδ, Φ, hpΦ, hqΦ, hΦU, hmodel, g, hg, hmg, hcount, hcritg, ?_, hkeep,
      hend _ hpΦ hpW, hend _ hqΦ hqW⟩
  intro y hy
  apply hexterior y
  rintro ⟨z, hz, rfl⟩
  exact hy (hΦU (Φ.map_source' (hKΦ hz)))

theorem MorseCancellation.injOn_of_two_new_values {X : Type*} {f g : X → ℝ} {C : Set X} {p q : X}
    (hinj : Set.InjOn f C) (hkeep : ∀ y ∈ C, g y = f y) (hp : g p ∉ f '' C) (hq : g q ∉ f '' C)
    (hpq : g p ≠ g q) : Set.InjOn g {y | y ∈ C ∨ y = p ∨ y = q} := by
  intro y hy z hz heq
  rcases hy with hy | rfl | rfl
  · rcases hz with hz | rfl | rfl
    · exact hinj hy hz ((hkeep y hy).symm.trans (heq.trans (hkeep z hz)))
    · exact False.elim (hp ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
    · exact False.elim (hq ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hp ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · rfl
    · exact False.elim (hpq heq)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hq ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · exact False.elim (hpq heq.symm)
    · rfl

theorem MorseCancellation.exists_excellent_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  ∃ g : M → ℝ,
                    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                      ManifoldMorse.IsMorse E g ∧
                        Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
                          (ManifoldMorse.criticalPoints E g).ncard =
                              (ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ ManifoldMorse.criticalPoints E g ↔
                                  y ∈ ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  g (Φ (a, 0)) < g (Φ (-a, 0)) ∧
                                    g (Φ (a, 0)) ∈ Set.Ioo l u ∧
                                      g (Φ (-a, 0)) ∈ Set.Ioo l u ∧
                                        (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                          (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, hmodel, g, hg, hmg, hcount, hcrit, hexterior, hkeep, hgp,
      hgq⟩ :=
    exists_native_morse_birth hf hm (hband x hx) hdim σ hσ
      (hU.inter (isOpen_Ioo.preimage hf.continuous)) ⟨hxU, hx⟩
  have hpa : f (Φ (a, 0)) = f x + δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (a, 0) hp]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hqa : f (Φ (-a, 0)) = f x - δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (-a, 0) hq]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hpval : g (Φ (a, 0)) = f x - δ * (2 * a ^ 3 / 3) := by
    have hh := hgp.self_of_nhds
    change g (Φ (a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (a, 0) at hh
    rw [(cubic_critical_values σ a).1] at hh
    exact hh.trans (by ring)
  have hqval : g (Φ (-a, 0)) = f x + δ * (2 * a ^ 3 / 3) := by
    have hh := hgq.self_of_nhds
    change g (Φ (-a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (-a, 0) at hh
    rw [(cubic_critical_values σ a).2] at hh
    exact hh
  have hpos : 0 < δ * (2 * a ^ 3 / 3) := by positivity
  have hpq : g (Φ (a, 0)) < g (Φ (-a, 0)) := by rw [hpval, hqval]; linarith
  have hpband : g (Φ (a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hq)).2
    change f (Φ (-a, 0)) ∈ Set.Ioo l u at hb
    rw [hqa] at hb
    rw [hpval]
    constructor <;> nlinarith [hb.1, hx.2]
  have hqband : g (Φ (-a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hp)).2
    change f (Φ (a, 0)) ∈ Set.Ioo l u at hb
    rw [hpa] at hb
    rw [hqval]
    constructor <;> nlinarith [hx.1, hb.2]
  have hnot (v : ℝ) (hv : v ∈ Set.Ioo l u) : v ∉ f '' ManifoldMorse.criticalPoints E f := by
    rintro ⟨y, hy, rfl⟩
    exact hband y hv hy
  have hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    have hh :=
      injOn_of_two_new_values hinj (fun y hy => (hkeep y hy).self_of_nhds) (hnot _ hpband)
        (hnot _ hqband) hpq.ne
    intro y hy z hz heq
    exact hh ((hcrit y).mp hy) ((hcrit z).mp hz) heq
  refine
    ⟨a, δ, ha, hδ, Φ, hp, hq, fun _ hy => (hΦ hy).1, g, hg, hmg, hinjg, hcount, hcrit, ?_, hkeep,
      hpq, hpband, hqband, hgp, hgq⟩
  intro y hy
  exact hexterior y (fun hh => hy hh.1)

theorem MorseCancellation.exists_signed_chart_of_split_quadratic {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} {m : ℕ}
    (P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Model m) M (Model m) ∞) (hp : p ∈ P.source)
    (hcenter : P p = 0) (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (e : ℝ) (σ : Fin m → ℝ)
    (he : e = -1 ∨ e = 1) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hformula : ∀ y ∈ P.source, f y = f p + e * (P y).1 ^ 2 + ∑ i, σ i * (P y).2 i ^ 2) :
    ∃ c : ManifoldMorse.SignedMorseChart (E := E) f p,
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  let w : Fin (Module.finrank ℝ E) → ℝ := fun j => (ρ.symm j).elim e σ
  have hwn : w (ρ Option.none) = e := by simp [w]
  have hws (i : Fin m) : w (ρ (Option.some i)) = σ i := by simp [w]
  have hw (j : Fin (Module.finrank ℝ E)) : w j = -1 ∨ w j = 1 := by
    change (ρ.symm j).elim e σ = -1 ∨ (ρ.symm j).elim e σ = 1
    cases h : ρ.symm j with
    | none => exact he
    | some i => exact hσ i
  have hsum (z : Model m) :
    (∑ j, w j * splitEquiv ρ z j ^ 2) = e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2 := by
    rw [split_signed_sum, hwn]
    simp only [hws]
  let C := P.trans (splitEquiv ρ).toDiffeomorph.toPartialDiffeomorph
  have hpC : p ∈ C.source := ⟨hp, Set.mem_univ _⟩
  have hC0 : C p = 0 := by
    change splitEquiv ρ (P p) = 0
    rw [hcenter, map_zero]
  have hCformula (y : M) (hy : y ∈ C.source) : f y = f p + ∑ i, w i * (C y i) ^ 2 := by
    change f y = f p + ∑ i, w i * splitEquiv ρ (P y) i ^ 2
    rw [hsum, hformula y hy.1]
    ring
  let c : ManifoldMorse.SignedMorseChart (E := E) f p :=
    { weights := w
      signs := hw
      chart := C
      mem_source := hpC
      center := hC0
      equation := hCformula
      inverse_equation := by
        intro z hz
        have h := hCformula (C.symm z) (C.map_target' hz)
        have hr : C (C.symm z) = z := C.right_inv' hz
        rw [hr] at h
        exact h }
  exact ⟨c, hwn, hws⟩

theorem MorseCancellation.exists_signed_chart_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    ∃ c : ManifoldMorse.SignedMorseChart (E := E) f (Φ (e * a, 0)),
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hgerm
  let T := PartialChart.restrictSource Φ hW
  have hpT : (e * a, (0 : Fin m → ℝ)) ∈ T.source := ⟨hp, hpW⟩
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨P, hpP, hP0, -, hP⟩ := exists_endpoint_product_chart σ ha e he2
  let B : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) (Real.sqrt δ)
        (Real.sqrt_pos.mpr hδ).ne').toContinuousLinearEquiv
  let C := (T.symm.trans P).trans B.toDiffeomorph.toPartialDiffeomorph
  have hTinv : T.symm (Φ (e * a, 0)) = (e * a, 0) := T.left_inv' hpT
  have hpC : Φ (e * a, 0) ∈ C.source := by
    change (Φ (e * a, 0) ∈ T.target ∧ T.symm (Φ (e * a, 0)) ∈ P.source) ∧ _
    exact ⟨⟨T.map_source' hpT, hTinv.symm ▸ hpP⟩, Set.mem_univ _⟩
  have hC0 : C (Φ (e * a, 0)) = 0 := by
    change B (P (T.symm (Φ (e * a, 0)))) = 0
    rw [hTinv, hP0, map_zero]
  have hvalue : f (Φ (e * a, 0)) = b + δ * cubic σ (-(a ^ 2)) (e * a, 0) := hgerm.self_of_nhds
  have hscale (z : Model m) :
    e * (B z).1 ^ 2 + ∑ i, σ i * (B z).2 i ^ 2 = δ * (e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2) := by
    change e * (Real.sqrt δ * z.1) ^ 2 + (∑ i, σ i * (Real.sqrt δ * z.2 i) ^ 2) = _
    simp only [mul_pow, Real.sq_sqrt hδ.le]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  apply exists_signed_chart_of_split_quadratic C hpC hC0 ρ e σ he hσ
  intro y hy
  have hyT : y ∈ T.target := hy.1.1
  have hzT := T.map_target' hyT
  have hzP : T.symm y ∈ P.source := hy.1.2
  have hfy : f y = b + δ * cubic σ (-(a ^ 2)) (T.symm y) := by
    have hh := hWsub hzT.2
    change f (T (T.symm y)) = b + δ * cubic σ (-(a ^ 2)) (T.symm y) at hh
    have hr : T (T.symm y) = y := T.right_inv' hyT
    rw [hr] at hh
    exact hh
  change
    f y = f (Φ (e * a, 0)) + e * (B (P (T.symm y))).1 ^ 2 + ∑ i, σ i * (B (P (T.symm y))).2 i ^ 2
  rw [hfy, hvalue, hP (T.symm y) hzP]
  have hs := hscale (P (T.symm y))
  linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ) :
    Fintype.card { j // w j = -1 } =
      (if w (ρ Option.none) = -1 then 1 else 0) +
        Fintype.card { i // w (ρ (Option.some i)) = -1 } := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← ρ.sum_comp, Fintype.sum_option]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_index_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (e * a, 0)) =
      (if e = -1 then 1 else 0) + Fintype.card { i // σ i = -1 } := by
  let ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨c, hce, hcσ⟩ := exists_signed_chart_of_scaled_cubic_germ Φ ρ σ hσ ha hδ e he hp hgerm
  rw [nativeMorseIndex_eq_chart c]
  simp only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    MorseHandle.NegativeSpace, finrank_euclideanSpace]
  rw [negative_card_split ρ c.weights, hce]
  simp only [hcσ]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_indices_of_cubic_birth_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgp : f ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z)
    (hgq : f ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (a, 0)) = Fintype.card { i // σ i = -1 } ∧
      nativeMorseIndex E f (Φ (-a, 0)) = Fintype.card { i // σ i = -1 } + 1 := by
  constructor
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ 1 (Or.inr rfl)
        (by simpa only [one_mul] using hp) (by simpa only [one_mul] using hgp)
    simpa only [one_mul, if_neg (by norm_num : (1 : ℝ) ≠ -1), zero_add] using h
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ (-1) (Or.inl rfl)
        (by simpa only [neg_one_mul] using hq) (by simpa only [neg_one_mul] using hgq)
    simpa [Nat.add_comm] using h

theorem MorseCancellation.exists_transverse_signs_of_count {m k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin m → ℝ, (∀ i, σ i = -1 ∨ σ i = 1) ∧ {i | σ i = -1}.ncard = k := by
  classical
  let σ : Fin m → ℝ := fun i => if i.val < k then -1 else 1
  refine ⟨σ, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < k
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · have heq : {i : Fin m | σ i = -1} = {i : Fin m | i.val < k} := by
      ext i
      by_cases hi : i.val < k <;> norm_num [σ, hi]
    rw [heq, ← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
    simp only [Set.mem_ofPred_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]

theorem MorseCancellation.exists_excellent_indexed_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ (g : M → ℝ) (p q : M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            p ∈ U ∧
              q ∈ U ∧
                nativeMorseIndex E g p = k ∧
                  nativeMorseIndex E g q = k + 1 ∧
                    g p < g q ∧
                      g p ∈ Set.Ioo l u ∧
                        g q ∈ Set.Ioo l u ∧
                          (ManifoldMorse.criticalPoints E g).ncard =
                              (ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ ManifoldMorse.criticalPoints E g ↔
                                  y ∈ ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
                                    nativeMorseCount E g (k + 1) =
                                        nativeMorseCount E f (k + 1) + 1 ∧
                                      ∀ j,
                                        j ≠ k →
                                          j ≠ k + 1 →
                                            nativeMorseCount E g j = nativeMorseCount E f j := by
  classical
  let m := Module.finrank ℝ E - 1
  have hdim : 1 + m = Module.finrank ℝ E := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  obtain ⟨σ, hσ, hcard⟩ := exists_transverse_signs_of_count hkm
  have hσne (i : Fin m) : σ i ≠ 0 := by rcases hσ i with h | h <;> rw [h] <;> norm_num
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, g, hg, hmg, hinjg, hcount, hcrit, hexterior, hkeep, hpq, hpband,
      hqband, hgp, hgq⟩ :=
    exists_excellent_native_morse_birth hf hm hinj hband hx hdim σ hσne hU hxU
  obtain ⟨hip, hiq⟩ := native_indices_of_cubic_birth_germs Φ hdim σ hσ ha hδ hp hq hgp hgq
  have hc : Fintype.card { i // σ i = -1 } = k := (Set.fintypeCard_eq_ncard _).trans hcard
  rw [hc] at hip hiq
  have hpnot : Φ (a, 0) ∉ ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (a, 0)) = f (Φ (a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hpband) h
  have hqnot : Φ (-a, 0) ∉ ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (-a, 0)) = f (Φ (-a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hqband) h
  have hreverse (y : M) :
    y ∈ ManifoldMorse.criticalPoints E f ↔
      y ∈ ManifoldMorse.criticalPoints E g ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0) := by
    rw [hcrit]
    constructor
    · intro hy
      exact ⟨Or.inl hy, fun h => hpnot (h ▸ hy), fun h => hqnot (h ▸ hy)⟩
    · rintro ⟨hy | hp' | hq', hnp, hnq⟩
      · exact hy
      · exact False.elim (hnp hp')
      · exact False.elim (hnq hq')
  have hpcrit := (hcrit (Φ (a, 0))).mpr (Or.inr (Or.inl rfl))
  have hqcrit := (hcrit (Φ (-a, 0))).mpr (Or.inr (Or.inr rfl))
  have hneq : Φ (a, 0) ≠ Φ (-a, 0) := fun h => hpq.ne (congrArg g h)
  obtain ⟨hck, hck', hcothers⟩ :=
    nativeMorseCount_adjacent_pair (ManifoldMorse.finite_criticalPoints hg hmg) hpcrit
      hqcrit hneq hreverse (fun y hy => (hkeep y hy).symm) hip hiq
  exact
    ⟨g, Φ (a, 0), Φ (-a, 0), hg, hmg, hinjg, hΦ (Φ.map_source' hp), hΦ (Φ.map_source' hq), hip,
      hiq, hpq, hpband, hqband, hcount, hcrit, hexterior, hkeep, hck.symm, hck'.symm,
      fun j hj hj' => (hcothers j hj hj').symm⟩

end Mathoverflow1973

end
