/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension

/-!
# Nonvanishing approximations of maps into higher dimension

A continuous map `f : M → F` from a finite-dimensional manifold to a normed space with
`dim M < dim F` has, for every `ε > 0`, a smooth nonvanishing `ε`-approximation
(`exists_smooth_nonzero_approx`: Whitney approximation, then subtract a small vector off the
image, whose complement is dense by
`Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension`). Blending it with `f` by a cutoff
in `‖f‖` (`ZeroAvoidanceCutoff.blend`, with weights from the clamped linear ramp
`RealIntervalProgress.progress`) gives a nonvanishing map homotopic to `f` by an `ε`-small
homotopy fixed where `‖f‖ ≥ 2ε` (`exists_nonzero_homotopy_small`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- A continuous map into a higher-dimensional space has a smooth nonvanishing approximation. -/
theorem exists_smooth_nonzero_approx {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F), ContMDiff I 𝓘(ℝ, F) ∞ g ∧ (∀ x, g x ≠ 0) ∧ ∀ x, Dist.dist (g x) (f x) < ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨h, hh, -⟩ :=
    f.continuous.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ ε / 2) continuous_const
      (fun _ ↦ hhalf)
  have hdense : Dense (Set.range h)ᶜ := by
    simpa only [Set.image_univ] using
      dense_compl_manifold_image isOpen_univ h.contMDiff.contMDiffOn hd
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp (hdense (0 : F)) (ε / 2) hhalf
  have haNorm : ‖a‖ < ε / 2 := by simpa only [dist_zero_left, dist_zero_right] using hdist
  let g : C(M, F) := ⟨fun x ↦ h x - a, h.contMDiff.continuous.sub continuous_const⟩
  refine ⟨g, h.contMDiff.sub contMDiff_const, ?_, ?_⟩
  · intro x hx
    have he : h x = a := sub_eq_zero.mp hx
    exact ha ⟨x, he⟩
  · intro x
    have hnorm : ‖h x - a - f x‖ ≤ ‖h x - f x‖ + ‖a‖ := by
      have he : h x - a - f x = (h x - f x) - a := by abel
      rw [he]
      exact norm_sub_le _ _
    change Dist.dist (h x - a) (f x) < ε
    rw [dist_eq_norm]
    have hhx : ‖h x - f x‖ < ε / 2 := by simpa only [dist_eq_norm] using hh x
    linarith

/-- The cutoff progress between levels `l` and `u`. -/
noncomputable def RealIntervalProgress.progress (l u t : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((t - l) / (u - l))

/-- The progress cutoff is continuous. -/
theorem RealIntervalProgress.continuous_progress (l u : ℝ) : Continuous (progress l u) :=
  continuous_subtype_val.comp
    (continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _))

/-- The progress is zero below `l`. -/
theorem RealIntervalProgress.progress_before {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) :
    progress l u t = 0 := by
  have h :=
    Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) zero_le_one
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu))
  exact congrArg Subtype.val h

/-- The progress is one above `u`. -/
theorem RealIntervalProgress.progress_after {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) :
    progress l u t = 1 := by
  have hr : 1 ≤ (t - l) / (u - l) := by
    apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
    simpa only [one_mul] using sub_le_sub_right ht l
  exact congrArg Subtype.val (Set.projIcc_of_right_le zero_le_one hr)

/-- The blend weight keeping a perturbed map nonzero. -/
noncomputable def ZeroAvoidanceCutoff.weight {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) : C(X, ℝ) :=
  ⟨fun x ↦ 1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖,
    continuous_const.sub
      ((RealIntervalProgress.continuous_progress ε (2 * ε)).comp f.continuous.norm)⟩

/-- The weight lies in `[0, 1]`. -/
theorem ZeroAvoidanceCutoff.weight_bounds {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (x : X) : 0 ≤ weight f ε x ∧ weight f ε x ≤ 1 := by
  have hp : RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∈ Set.Icc (0 : ℝ) 1 :=
    (Set.projIcc (0 : ℝ) 1 zero_le_one ((‖f x‖ - ε) / (2 * ε - ε))).property
  change
    0 ≤ 1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∧
      1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ≤ 1
  constructor <;> linarith [hp.1, hp.2]

/-- The weight is one where the original map is small. -/
theorem ZeroAvoidanceCutoff.weight_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : ‖f x‖ ≤ ε) :
    weight f ε x = 1 := by
  simp only [weight, ContinuousMap.coe_mk,
    RealIntervalProgress.progress_before (by linarith : ε ≤ 2 * ε) hx, sub_zero]

/-- The weight is zero where the original map is large. -/
theorem ZeroAvoidanceCutoff.weight_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : 2 * ε ≤ ‖f x‖) :
    weight f ε x = 0 := by
  simp only [weight, ContinuousMap.coe_mk,
    RealIntervalProgress.progress_after (by linarith : ε < 2 * ε) hx, sub_self]

/-- The blend of the original and perturbed maps. -/
noncomputable def ZeroAvoidanceCutoff.blend {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) : C(X, F) :=
  ⟨fun x ↦ f x + weight f ε x • (g x - f x),
    f.continuous.add ((weight f ε).continuous.smul (g.continuous.sub f.continuous))⟩

/-- Where the original is small the blend is the original. -/
theorem ZeroAvoidanceCutoff.blend_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : ‖f x‖ ≤ ε) : blend f g ε x = g x := by
  change f x + weight f ε x • (g x - f x) = g x
  rw [weight_small f ε hε hx, one_smul]
  abel

/-- Where the original is large the blend is the perturbation. -/
theorem ZeroAvoidanceCutoff.blend_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : 2 * ε ≤ ‖f x‖) : blend f g ε x = f x := by
  change f x + weight f ε x • (g x - f x) = f x
  rw [weight_large f ε hε hx, zero_smul, add_zero]

/-- The blend stays within the perturbation distance. -/
theorem ZeroAvoidanceCutoff.dist_blend_le {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (x : X) :
    Dist.dist (blend f g ε x) (f x) ≤ Dist.dist (g x) (f x) := by
  simp only [dist_eq_norm]
  change ‖f x + weight f ε x • (g x - f x) - f x‖ ≤ ‖g x - f x‖
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_bounds f ε x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_bounds f ε x).2

/-- The blend is nonzero. -/
theorem ZeroAvoidanceCutoff.blend_ne_zero {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ x, g x ≠ 0) (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (x : X) : blend f g ε x ≠ 0 := by
  by_cases hx : ‖f x‖ ≤ ε
  · rw [blend_small f g ε hε hx]
    exact hg x
  · intro hz
    have hh := (dist_blend_le f g ε x).trans_lt (hclose x)
    rw [hz, dist_zero_left] at hh
    exact hx hh.le

/-- The blend as a homotopy between the two maps. -/
noncomputable def ZeroAvoidanceCutoff.homotopy {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyRel f (blend f g ε) {x | 2 * ε ≤ ‖f x‖}
    where
  toFun p := f p.2 + (p.1 : ℝ) • (blend f g ε p.2 - f p.2)
  continuous_toFun :=
    (f.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((blend f g ε).continuous.comp continuous_snd).sub (f.continuous.comp continuous_snd)))
  map_zero_left x := by simp
  map_one_left
    x := by
    change f x + (1 : ℝ) • (blend f g ε x - f x) = blend f g ε x
    rw [one_smul]
    abel
  prop' t x
    hx := by
    change f x + (t : ℝ) • (blend f g ε x - f x) = f x
    rw [blend_large f g ε hε hx, sub_self, smul_zero, add_zero]

/-- The homotopy stays within the perturbation distance. -/
theorem ZeroAvoidanceCutoff.homotopy_dist_lt {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (t : (unitInterval)) (x : X) :
    Dist.dist (homotopy f g ε hε (t, x)) (f x) < ε := by
  rw [dist_eq_norm]
  change ‖f x + (t : ℝ) • (blend f g ε x - f x) - f x‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖blend f g ε x - f x‖ ≤ ‖blend f g ε x - f x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ ≤ Dist.dist (g x) (f x) := by simpa only [dist_eq_norm] using dist_blend_le f g ε x
    _ < ε := hclose x

/-- A map into higher dimensions is homotopic to a nearby nonvanishing map. -/
theorem exists_nonzero_homotopy_small {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F),
      (∀ x, g x ≠ 0) ∧
        ∃ G : ContinuousMap.HomotopyRel f g {x | 2 * ε ≤ ‖f x‖},
          ∀ t x, Dist.dist (G (t, x)) (f x) < ε := by
  obtain ⟨h, -, hnonzero, hclose⟩ := exists_smooth_nonzero_approx (I := I) f ε hε hd
  refine
    ⟨ZeroAvoidanceCutoff.blend f h ε, ZeroAvoidanceCutoff.blend_ne_zero f h ε hε hnonzero hclose,
      ZeroAvoidanceCutoff.homotopy f h ε hε, ?_⟩
  exact ZeroAvoidanceCutoff.homotopy_dist_lt f h ε hε hclose

