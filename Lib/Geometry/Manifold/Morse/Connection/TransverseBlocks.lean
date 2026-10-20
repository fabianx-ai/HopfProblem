/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.FrameField
import Lib.Geometry.Manifold.Morse.Connection.TimeChange
import Lib.Geometry.Manifold.Morse.Connection.TransportedCorrections
import Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts

/-!
# Linearising a transverse germ by supported isotopies

Let `Φ` be a diffeomorphism germ of `A × B` fixing `0` such that the sheet `Φ (A × 0)` meets
`0 × B` transversally and only at `0`.

* `hasFDerivAt_scalar_displacement`, `exists_open_transverse_convex_blend`,
  `exists_supported_transverse_germ_linearization`: a compactly supported isotopy conjugates `Φ`
  to its derivative near `0` while the intersection stays unique.
* `transverseBlockMap P S Q R`, `exists_transverse_block_factorization`: the block form
  `[[P, Q], [R, S]]` of a linear automorphism of `A × B` with `P` invertible;
  `exists_supported_lower_shear_isotopy`: the shear `(x, y) ↦ (x, y + R x)` is realised by a
  supported isotopy fixing `0 × B`.
* `exists_supported_transverse_block_reduction`,
  `exists_projected_equiv_of_native_transverse`, `exists_block_reduction_of_native_transverse`:
  supported isotopies `Dₛ`, `Dₜ` of source and target with `Dₜ ∘ Φ ∘ Dₛ = P × S` near `0`.
* `label_sheets_transverse_in_incoming_chart`, `relative_label_sheet_germs`,
  `relative_transverse_of_label_sheets`, `relative_intersection_of_native_unique_connection`:
  transversality and uniqueness of the intersection of the stable and unstable sheets read in
  the base of a flow-box chart of a unique connecting orbit;
  `exists_cylinder_block_correction`: the supported isotopy of the base making the sheets linear
  blocks `(L₁, L₂)`.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5 (the assertions in the proof of
Theorem 5.4 that make the stable and unstable spheres meet the level in coordinate planes).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Transverse block corrections -/

/-- The scalar displacement is differentiable. -/
theorem TransverseGerms.hasFDerivAt_scalar_displacement {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f g : A → A} (hfzero : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ A) 0)
    (hscalar : ∀ x, ∃ α ∈ Set.Icc (0 : ℝ) 1, g x = x + α • (f x - x)) :
    HasFDerivAt g (ContinuousLinearMap.id ℝ A) 0 := by
  have hgzero : g 0 = 0 := by
    obtain ⟨α, -, he⟩ := hscalar 0
    simpa only [hfzero, sub_self, smul_zero, add_zero] using he
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf.isLittleO.bound hε] with x hx
  simp only [hfzero, hgzero, sub_zero, ContinuousLinearMap.id_apply] at hx ⊢
  obtain ⟨α, hα, he⟩ := hscalar x
  rw [he, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hα.2).trans hx

/-- An open transverse convex blend exists. -/
theorem TransverseGerms.exists_open_transverse_convex_blend {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {φ : (A × B) → (A × B)} {U : Set (A × B)} (hU : IsOpen U) (hzero : (0 : A × B) ∈ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hφzero : φ 0 = 0) (L : (A × B) →L[ℝ] (A × B))
    (hder : fderiv ℝ φ 0 = L) (P : A ≃L[ℝ] A) (hP : ∀ x : A, (L (x, 0)).1 = P x) :
    ∃ W : Set (A × B),
      IsOpen W ∧
        (0 : A × B) ∈ W ∧
          W ⊆ U ∧
            ∀ x : A,
              (x, (0 : B)) ∈ W →
                ∀ α ∈ Set.Icc (0 : ℝ) 1, (φ (x, 0) + α • (L (x, 0) - φ (x, 0))).1 = 0 ↔ x = 0 := by
  let ι := ContinuousLinearMap.inl ℝ A B
  let π := ContinuousLinearMap.fst ℝ A B
  let H : A → A := fun x => P.symm ((φ (x, 0)).1)
  let S : Set A := ι ⁻¹' U
  have hS : IsOpen S := hU.preimage ι.continuous
  have hSzero : (0 : A) ∈ S := hzero
  have hH : ContDiffOn ℝ ∞ H S :=
    P.symm.contDiff.comp_contDiffOn
      (π.contDiff.comp_contDiffOn (hφ.comp ι.contDiff.contDiffOn (fun x hx => hx)))
  have hfd : HasFDerivAt φ L 0 := by
    rw [← hder]
    exact ((hφ.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)).hasFDerivAt
  have hHd : HasFDerivAt H (P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι))) 0 :=
    P.symm.toContinuousLinearMap.hasFDerivAt.comp (0 : A)
      (π.hasFDerivAt.comp (0 : A) (hfd.comp (f := ι) (0 : A) ι.hasFDerivAt))
  have hlinear :
    P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι)) = ContinuousLinearMap.id ℝ A := by
    apply ContinuousLinearMap.ext
    intro x
    change P.symm ((L (x, 0)).1) = x
    rw [hP, P.symm_apply_apply]
  rw [hlinear] at hHd
  let u : A → A := fun x => H x - x
  have hu : ContDiffOn ℝ ∞ u S := hH.sub contDiffOn_id
  have hu0 : u 0 = 0 := by
    change P.symm ((φ (0 : A × B)).1) - 0 = 0
    rw [hφzero]
    simp
  have hdu : fderiv ℝ u 0 = 0 := by
    have hh := hHd.sub (hasFDerivAt_id (0 : A))
    change fderiv ℝ (H - id) 0 = 0
    simpa only [sub_self] using hh.fderiv
  obtain ⟨ρ, hρ, -, hlip⟩ :=
    SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero hS hSzero hu hdu
      (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let W := U ∩ Metric.ball (0 : A × B) ρ
  refine
    ⟨W, hU.inter Metric.isOpen_ball, ⟨hzero, Metric.mem_ball_self hρ⟩, Set.inter_subset_left, ?_⟩
  intro x hx α hα
  have hxρ : x ∈ Metric.closedBall (0 : A) ρ := by
    have hh := mem_ball_zero_iff.mp hx.2
    apply mem_closedBall_zero_iff.mpr
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)] using hh.le
  have h0ρ : (0 : A) ∈ Metric.closedBall (0 : A) ρ := Metric.mem_closedBall_self hρ.le
  have herr : ‖u x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
    have hh := hlip.dist_le_mul x hxρ 0 h0ρ
    simpa only [hu0, dist_zero_right, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  constructor
  · intro hz
    have he : x + (1 - α) • u x = 0 := by
      have hh := congrArg P.symm hz
      change P.symm ((φ (x, 0)).1 + α • ((L (x, 0)).1 - (φ (x, 0)).1)) = P.symm 0 at hh
      simp only [map_add, map_smul, map_sub, hP, P.symm_apply_apply, map_zero] at hh
      change H x + α • (x - H x) = 0 at hh
      calc
        x + (1 - α) • u x = H x + α • (x - H x) := by dsimp [u]; module
        _ = 0 := hh
    have he' : x = -((1 - α) • u x) := eq_neg_of_add_eq_zero_left he
    have hnorm : ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
      calc
        ‖x‖ = ‖-((1 - α) • u x)‖ := congrArg Norm.norm he'
        _ = ‖(1 - α) • u x‖ := (norm_neg _)
        _ = (1 - α) * ‖u x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hα.2])]
        _ ≤ ‖u x‖ := (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hα.1]))
        _ ≤ (1 / 2 : ℝ) * ‖x‖ := herr
    exact norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg x]) (norm_nonneg x))
  · rintro rfl
    simp only [show ((0 : A), (0 : B)) = (0 : A × B) from rfl, hφzero, map_zero, sub_self,
      smul_zero, add_zero, Prod.fst_zero]

/-- A supported transverse germ linearization exists. -/
theorem TransverseGerms.exists_supported_transverse_germ_linearization {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (C : (A × B) ≃L[ℝ] (A × B)) (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      C.toContinuousLinearMap = fderiv ℝ Φ 0 ∧
        IsCompact K ∧
          K ⊆ Φ.target ∧
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
              (∀ y, H (0, y) = y) ∧
                (∀ t,
                    ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
                      ∀ y, D y = H (t, y)) ∧
                  (∀ t y, y ∉ K → H (t, y) = y) ∧
                    (∀ t, H (t, 0) = 0) ∧
                      (∀ t x, (x, (0 : B)) ∈ Φ.source → ((H (t, Φ (x, 0))).1 = 0 ↔ x = 0)) ∧
                        (∀ t, fderiv ℝ (fun x => H (t, Φ x)) 0 = fderiv ℝ Φ 0) ∧
                          (fun x => H (1, Φ x)) =ᶠ[𝓝 (0 : A × B)] C := by
  have hΦ : ContDiffOn ℝ ∞ (Φ : (A × B) → A × B) Φ.source := Φ.contMDiffOn_toFun.contDiffOn
  have hbij : Function.Bijective (fderiv ℝ Φ 0) := by
    have hh := PartialChart.bijective_mfderiv Φ hzero
    change Function.Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ 0 : (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ 0).toLinearMap hbij).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ Φ 0 := rfl
  obtain ⟨W, hW, hWzero, hWsource, hblend⟩ :=
    exists_open_transverse_convex_blend Φ.open_source hzero hΦ hΦzero C.toContinuousLinearMap
      hC.symm P hP
  let U := Φ '' W
  have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW hWsource
  have hUzero : (0 : A × B) ∈ U := ⟨0, hWzero, hΦzero⟩
  have hUtarget : U ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hWsource hx)
  have htzero : (0 : A × B) ∈ Φ.target := hUtarget hUzero
  have hinvzero : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' hzero
    change Φ.symm (Φ 0) = 0 at hh
    rwa [hΦzero] at hh
  let G : (A × B) → A × B := C ∘ Φ.symm
  have hG : ContDiffOn ℝ ∞ G U :=
    C.contDiff.comp_contDiffOn (Φ.contMDiffOn_invFun.contDiffOn.mono hUtarget)
  have hGzero : G 0 = 0 := by simp only [G, Function.comp_apply, hinvzero, map_zero]
  have hdf :=
    ((hΦ.contDiffAt (Φ.open_source.mem_nhds hzero)).differentiableAt (by simp)).hasFDerivAt
  have hdi :=
    ((Φ.contMDiffOn_invFun.contDiffOn.contDiffAt (Φ.open_target.mem_nhds htzero)).differentiableAt
        (by simp)).hasFDerivAt
  have hdf' : HasFDerivAt (Φ : (A × B) → A × B) (fderiv ℝ Φ 0) (Φ.symm 0) := by
    rw [hinvzero]
    exact hdf
  have hcomp := hdf'.comp (f := Φ.symm) (0 : A × B) hdi
  have hid : (Φ ∘ Φ.symm) =ᶠ[𝓝 (0 : A × B)] id := by
    filter_upwards [Φ.open_target.mem_nhds htzero] with y hy
    exact Φ.right_inv' hy
  have hcancel : (fderiv ℝ Φ 0).comp (fderiv ℝ Φ.symm 0) = ContinuousLinearMap.id ℝ (A × B) :=
    hcomp.fderiv.symm.trans (hid.fderiv_eq.trans fderiv_id)
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ (A × B) := by
    have hh := C.toContinuousLinearMap.hasFDerivAt.comp (f := Φ.symm) (0 : A × B) hdi
    exact hh.fderiv.trans (by rw [hC]; exact hcancel)
  obtain ⟨H, K, hK, hKU, hH, hH0, hdiff, hfix, hscalar, hgerm⟩ :=
    SmallPerturbation.exists_supported_tangent_identity_isotopy hU hUzero hG hGzero hdG
  have hHorigin (t : ℝ) : H (t, 0) = 0 := by
    obtain ⟨α, -, hα⟩ := hscalar t 0
    simpa only [hGzero, sub_self, smul_zero, add_zero] using hα
  have hdG' : HasFDerivAt G (ContinuousLinearMap.id ℝ (A × B)) 0 := by
    rw [← hdG]
    exact ((hG.contDiffAt (hU.mem_nhds hUzero)).differentiableAt (by simp)).hasFDerivAt
  have hHder (t : ℝ) : HasFDerivAt (fun y => H (t, y)) (ContinuousLinearMap.id ℝ (A × B)) 0 :=
    hasFDerivAt_scalar_displacement hGzero hdG' (hscalar t)
  refine ⟨C, H, K, hC, hK, hKU.trans hUtarget, hH, hH0, hdiff, hfix, hHorigin, ?_, ?_, ?_⟩
  · intro t x hx
    by_cases hxin : Φ (x, 0) ∈ K
    · obtain ⟨z, hz, hzeq⟩ := hKU hxin
      have hzx : z = (x, 0) := Φ.toOpenPartialHomeomorph.injOn (hWsource hz) hx hzeq
      have hxW : (x, (0 : B)) ∈ W := hzx ▸ hz
      obtain ⟨α, hα, he⟩ := hscalar t (Φ (x, 0))
      have hGΦ : G (Φ (x, 0)) = C (x, 0) := by
        dsimp [G]
        exact congrArg C (Φ.left_inv' hx)
      rw [he, hGΦ]
      exact hblend x hxW α hα
    · rw [hfix t _ hxin]
      exact hunique x hx
  · intro t
    have hh : HasFDerivAt (fun y => H (t, y)) (ContinuousLinearMap.id ℝ (A × B)) (Φ 0) := by
      rw [hΦzero]
      exact hHder t
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using
      (hh.comp (f := Φ) (0 : A × B) hdf).fderiv
  · have hΦtend : Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh := Φ.toOpenPartialHomeomorph.continuousAt hzero
      change Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
      rwa [hΦzero] at hh
    filter_upwards [hgerm.comp_tendsto hΦtend, Φ.open_source.mem_nhds hzero] with x hx hxsource
    change H (1, Φ x) = C x
    change H (1, Φ x) = G (Φ x) at hx
    rw [hx]
    dsimp [G]
    exact congrArg C (Φ.left_inv' hxsource)

/-- The transverse block map. -/
def TransverseGerms.transverseBlockMap {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B)
    (Q : B →L[ℝ] A) (R : A →L[ℝ] B) : (A × B) →L[ℝ] (A × B) :=
  let T :=
    P.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ A B + Q.comp (ContinuousLinearMap.snd ℝ A B))
  T.prod (S.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ A B) + R.comp T)

/-- A transverse block factorization exists. -/
theorem TransverseGerms.exists_transverse_block_factorization {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] (C : (A × B) ≃L[ℝ] (A × B)) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (C (x, 0)).1 = P x) :
    ∃ (Q : B →L[ℝ] A) (R : A →L[ℝ] B) (S : B ≃L[ℝ] B),
      C.toContinuousLinearMap = transverseBlockMap P S Q R := by
  let Q : B →L[ℝ] A :=
    P.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ A B).comp
        (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  let R : A →L[ℝ] B :=
    (ContinuousLinearMap.snd ℝ A B).comp
      (C.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ A B).comp P.symm.toContinuousLinearMap))
  let S₀ : B →L[ℝ] B :=
    (ContinuousLinearMap.snd ℝ A B).comp
        (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)) -
      R.comp
        ((ContinuousLinearMap.fst ℝ A B).comp
          (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  have hQ (y : B) : P (Q y) = (C (0, y)).1 := P.apply_symm_apply _
  have hR (x : A) : R (P x) = (C (x, 0)).2 := by
    change (C (P.symm (P x), 0)).2 = _
    rw [P.symm_apply_apply]
  have hsplit (p : A × B) : C p = C (p.1, 0) + C (0, p.2) := by
    rw [← map_add]
    congr 1
    simp
  have hmodel (p : A × B) : C p = (P (p.1 + Q p.2), S₀ p.2 + R (P (p.1 + Q p.2))) := by
    apply Prod.ext
    · rw [hsplit, Prod.fst_add, map_add, hP, hQ]
    · rw [hsplit, Prod.snd_add, map_add, map_add, hR, hQ]
      change
        (C (p.1, 0)).2 + (C (0, p.2)).2 =
          ((C (0, p.2)).2 - R ((C (0, p.2)).1)) + ((C (p.1, 0)).2 + R ((C (0, p.2)).1))
      abel
  have haxis (y : B) : C (-Q y, y) = (0, S₀ y) := by
    rw [hmodel]
    simp
  have hbij : Function.Bijective S₀ := by
    constructor
    · intro x y hxy
      have he : C (-Q x, x) = C (-Q y, y) := by rw [haxis, haxis, hxy]
      exact congrArg Prod.snd (C.injective he)
    · intro y
      obtain ⟨p, hp⟩ := C.surjective (0, y)
      have hfirst : P (p.1 + Q p.2) = 0 := by
        have hh := congrArg Prod.fst hp
        rwa [hmodel] at hh
      have hsecond : S₀ p.2 + R (P (p.1 + Q p.2)) = y := by
        have hh := congrArg Prod.snd hp
        rwa [hmodel] at hh
      exact ⟨p.2, by simpa only [hfirst, map_zero, add_zero] using hsecond⟩
  let S := (LinearEquiv.ofBijective S₀.toLinearMap hbij).toContinuousLinearEquiv
  refine ⟨Q, R, S, ?_⟩
  apply ContinuousLinearMap.ext
  intro p
  exact hmodel p

/-- A supported lower shear isotopy exists. -/
theorem TransverseGerms.exists_supported_lower_shear_isotopy {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] (R : A →L[ℝ] B) {U : Set (A × B)} (hU : IsOpen U)
    (hzero : (0 : A × B) ∈ U) :
    ∃ (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
            (∀ p, H (0, p) = p) ∧
              (∀ t,
                  ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
                    ∀ p, D p = H (t, p)) ∧
                (∀ t p, p ∉ K → H (t, p) = p) ∧
                  (∀ t p, (H (t, p)).1 = p.1) ∧
                    (∀ t y, H (t, ((0 : A), y)) = (0, y)) ∧
                      (fun p => H (1, p)) =ᶠ[𝓝 (0 : A × B)] (fun p => (p.1, p.2 + R p.1)) := by
  let e := ContinuousLinearEquiv.prodComm ℝ A B
  let U' := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  have hzero' : (0 : B × A) ∈ U' := by simpa only [U', Set.mem_preimage, map_zero] using hzero
  obtain ⟨J, K', hK', hK'U', hJ, hJ0, hdiff, hfix, hsecond, hcore, hgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy R hU' hzero'
  let H : ℝ × (A × B) → A × B := fun p => e.symm (J (p.1, e p.2))
  let K := e.symm '' K'
  have hK : IsCompact K := hK'.image e.symm.continuous
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hK'U' hy
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H :=
    e.symm.contDiff.contMDiff.comp
      (hJ.comp (contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)))
  refine ⟨H, K, hK, hKU, hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change e.symm (J (0, e p)) = p
    rw [hJ0, e.symm_apply_apply]
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    refine ⟨(e.toDiffeomorph.trans D).trans e.symm.toDiffeomorph, ?_⟩
    intro p
    change e.symm (D (e p)) = e.symm (J (t, e p))
    rw [hD]
  · intro t p hp
    have hnot : e p ∉ K' := fun h => hp ⟨e p, h, e.symm_apply_apply p⟩
    change e.symm (J (t, e p)) = p
    rw [hfix t _ hnot, e.symm_apply_apply]
  · intro t p
    exact hsecond t (e p)
  · intro t y
    change e.symm (J (t, (y, (0 : A)))) = (0, y)
    rw [hcore]
    rfl
  · have ht : Filter.Tendsto e (𝓝 (0 : A × B)) (𝓝 0) := by
      simpa only [map_zero] using e.continuous.tendsto (0 : A × B)
    filter_upwards [hgerm.comp_tendsto ht] with p hp
    change J (1, e p) = ((e p).1 + R (e p).2, (e p).2) at hp
    change e.symm (J (1, e p)) = (p.1, p.2 + R p.1)
    rw [hp]
    rfl

/-- A supported transverse block reduction exists. -/
theorem TransverseGerms.exists_supported_transverse_block_reduction {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (S : B ≃L[ℝ] B) (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (Kₛ Kₜ :
      Set (A × B)),
      IsCompact Kₛ ∧
        Kₛ ⊆ Φ.source ∧
          IsCompact Kₜ ∧
            Kₜ ⊆ Φ.target ∧
              Nonempty
                  (SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ
                    {p : A × B | p.2 = 0}) ∧
                Nonempty
                    (SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)}) ∧
                  Set.MapsTo Dₛ Φ.source Φ.source ∧
                    Set.MapsTo Dₜ Φ.target Φ.target ∧
                      (∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
                        (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)] (fun p => (P p.1, S p.2)) := by
  obtain ⟨C, H, K₁, hC, hK₁, hK₁target, hH, hH0, hHdiff, hHfix, hHorigin, hHunique, -, hHgerm⟩ :=
    exists_supported_transverse_germ_linearization Φ hzero hΦzero P hP hunique
  have hCP (x : A) : (C (x, 0)).1 = P x := by
    change (C.toContinuousLinearMap (x, 0)).1 = P x
    rw [hC]
    exact hP x
  obtain ⟨Q, R, S, hfactor⟩ := exists_transverse_block_factorization C P hCP
  obtain ⟨J, K₂, hK₂, hK₂source, hJ, hJ0, hJdiff, hJfix, -, hJcore, hJgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy (-Q) Φ.open_source hzero
  have htzero : (0 : A × B) ∈ Φ.target := by
    have hh := Φ.map_source' hzero
    rwa [hΦzero] at hh
  obtain ⟨L, K₃, hK₃, hK₃target, hL, hL0, hLdiff, hLfix, hLfirst, hLcore, hLgerm⟩ :=
    exists_supported_lower_shear_isotopy (-R) Φ.open_target htzero
  obtain ⟨Dₕ, hDₕ⟩ := hHdiff 1
  obtain ⟨Dₛ, hDₛ⟩ := hJdiff 1
  obtain ⟨Dₗ, hDₗ⟩ := hLdiff 1
  let Dₜ := Dₕ.trans Dₗ
  let Kₜ := K₁ ∪ K₃
  have hKₜ : IsCompact Kₜ := hK₁.union hK₃
  have hKₜtarget : Kₜ ⊆ Φ.target := Set.union_subset hK₁target hK₃target
  have hsrc : SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ K₂ {p : A × B | p.2 = 0} := by
    refine ⟨J, hJ, hJ0, fun p => (hDₛ p).symm, hJdiff, hJfix, ?_⟩
    rintro t ⟨x, y⟩ hy
    change y = 0 at hy
    subst y
    exact hJcore t x
  have htgt : SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)} := by
    let T : ℝ × (A × B) → A × B := fun p => L (p.1, H p)
    have hT : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ T :=
      hL.comp (contMDiff_fst.prodMk hH)
    refine ⟨T, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      change L (0, H (0, p)) = p
      rw [hH0, hL0]
    · intro p
      change L (1, H (1, p)) = Dₗ (Dₕ p)
      rw [hDₗ, hDₕ]
    · intro t
      obtain ⟨Eₕ, hEₕ⟩ := hHdiff t
      obtain ⟨Eₗ, hEₗ⟩ := hLdiff t
      refine ⟨Eₕ.trans Eₗ, ?_⟩
      intro p
      change Eₗ (Eₕ p) = L (t, H (t, p))
      rw [hEₗ, hEₕ]
    · intro t p hp
      change L (t, H (t, p)) = p
      rw [hHfix t p (fun h => hp (Or.inl h)), hLfix t p (fun h => hp (Or.inr h))]
    · intro t p hp
      have hp0 : p = 0 := Set.mem_singleton_iff.mp hp
      subst p
      change L (t, H (t, 0)) = 0
      rw [hHorigin]
      exact hLcore t 0
  have hsrczero : Dₛ (0 : A × B) = 0 := hsrc.endpoint_fixed_on 0 rfl
  have hsrctend : Filter.Tendsto Dₛ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Dₛ.continuous.tendsto (0 : A × B)
    rwa [hsrczero] at hh
  refine
    ⟨S, Dₛ, Dₜ, K₂, Kₜ, hK₂, hK₂source, hKₜ, hKₜtarget, ⟨hsrc⟩, ⟨htgt⟩,
      SupportedDiffeomorph.mapsTo_source Φ Dₛ.toEquiv hK₂source hsrc.endpoint_fixed_outside,
      SupportedDiffeomorph.mapsTo_source Φ.symm Dₜ.toEquiv hKₜtarget
        htgt.endpoint_fixed_outside,
      ?_, ?_⟩
  · intro x hx
    have hfixed : Dₛ (x, (0 : B)) = (x, 0) := hsrc.endpoint_fixed_on (x, 0) rfl
    rw [hfixed]
    change (Dₗ (Dₕ (Φ (x, 0)))).1 = 0 ↔ x = 0
    rw [hDₗ, hLfirst, hDₕ]
    exact hHunique 1 x hx
  · have hCtend : Filter.Tendsto (fun p => C (Dₛ p)) (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh : Filter.Tendsto C (𝓝 (0 : A × B)) (𝓝 0) := by
        simpa only [map_zero] using C.continuous.tendsto (0 : A × B)
      exact hh.comp hsrctend
    filter_upwards [hHgerm.comp_tendsto hsrctend, hLgerm.comp_tendsto hCtend, hJgerm] with p hpH
      hpL hpJ
    change H (1, Φ (Dₛ p)) = C (Dₛ p) at hpH
    change L (1, C (Dₛ p)) = ((C (Dₛ p)).1, (C (Dₛ p)).2 + (-R) (C (Dₛ p)).1) at hpL
    change J (1, p) = (p.1 + (-Q) p.2, p.2) at hpJ
    change Dₗ (Dₕ (Φ (Dₛ p))) = (P p.1, S p.2)
    rw [hDₗ, hDₕ, hpH, hpL, hDₛ, hpJ]
    have hmodel (z : A × B) : C z = (P (z.1 + Q z.2), S z.2 + R (P (z.1 + Q z.2))) := by
      have hh := congrArg (fun T : (A × B) →L[ℝ] (A × B) => T z) hfactor
      exact hh
    rw [hmodel]
    simp only [neg_apply, add_neg_cancel_right, neg_add_cancel_right]

/-- A projected equivalence of native transverse data exists. -/
theorem TransverseGerms.exists_projected_equiv_of_native_transverse {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => Φ (x, 0))
        (fun y : B => (0, y)) 0 0) :
    ∃ P : A ≃L[ℝ] A, ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x := by
  let D : A →L[ℝ] (A × B) := (fderiv ℝ Φ 0).comp (ContinuousLinearMap.inl ℝ A B)
  let N : (A × B) →L[ℝ] A := ContinuousLinearMap.fst ℝ A B
  let J : B →L[ℝ] (A × B) := ContinuousLinearMap.inr ℝ A B
  have hdiff :=
    (Φ.contMDiffOn_toFun.contDiffOn.contDiffAt (Φ.open_source.mem_nhds hzero)).differentiableAt
      (by simp)
  have hι : HasFDerivAt (fun x : A => (x, (0 : B))) (ContinuousLinearMap.inl ℝ A B) (0 : A) :=
    (ContinuousLinearMap.inl ℝ A B).hasFDerivAt
  have hd : HasFDerivAt (fun x : A => Φ (x, 0)) D 0 :=
    hdiff.hasFDerivAt.comp (f := fun x : A => (x, (0 : B))) (0 : A) hι
  have hj : HasFDerivAt (fun y : B => (0, y)) J 0 := (ContinuousLinearMap.inr ℝ A B).hasFDerivAt
  have hcross : (0, (0 : B)) = Φ ((0 : A), 0) := hΦzero.symm
  have ht := htrans hcross
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv, hd.fderiv, hj.fderiv] at ht
  have hNJ : N.comp J = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  have hN : Function.Surjective N := fun x => ⟨(x, 0), rfl⟩
  have hJD : Function.Surjective (J.coprod D) :=
    TransverseCoordinates.surjective_coprod_swap D J ht
  have hbij : Function.Bijective (N.comp D) :=
    TransverseCoordinates.bijective_normal_comp N J D hN hJD hNJ rfl
  let P := (LinearEquiv.ofBijective (N.comp D).toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨P, fun _ => rfl⟩

/-- A block reduction of native transverse data exists. -/
theorem TransverseGerms.exists_block_reduction_of_native_transverse {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => Φ (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ P : A ≃L[ℝ] A,
      (∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x) ∧
        ∃ (S : B ≃L[ℝ] B) (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (Kₛ Kₜ :
          Set (A × B)),
          IsCompact Kₛ ∧
            Kₛ ⊆ Φ.source ∧
              IsCompact Kₜ ∧
                Kₜ ⊆ Φ.target ∧
                  Nonempty
                      (SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ
                        {p : A × B | p.2 = 0}) ∧
                    Nonempty
                        (SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ
                          {(0 : A × B)}) ∧
                      Set.MapsTo Dₛ Φ.source Φ.source ∧
                        Set.MapsTo Dₜ Φ.target Φ.target ∧
                          (∀ x : A,
                              (x, (0 : B)) ∈ Φ.source → ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
                            (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)]
                              (fun p => (P p.1, S p.2)) := by
  obtain ⟨P, hP⟩ := exists_projected_equiv_of_native_transverse Φ hzero hΦzero htrans
  exact ⟨P, hP, exists_supported_transverse_block_reduction Φ hzero hΦzero P hP hunique⟩

/-- Label sheets are transverse in the incoming chart. -/
theorem TransverseGerms.label_sheets_transverse_in_incoming_chart {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞) (hQsrc : (0 : A × B) ∈ Q.source)
    (hPsrc : (0 : A × B) ∈ P.source) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun x : A => Q (x, 0))
        (fun y : B => P (0, y)) 0 0) :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A × B) (fun x : A => P.symm (Q (x, 0))) 0).coprod
        (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun y : B => P.symm (P (0, y))) 0)) := by
  have hcross : P ((0 : A), (0 : B)) = Q (0, 0) := hP0.trans hQ0.symm
  have htarget : Q ((0 : A), (0 : B)) ∈ P.target := by
    change Q (0 : A × B) ∈ P.target
    rw [hQ0, ← hP0]
    exact P.map_source' hPsrc
  have hι : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, A × B) (fun x : A => (x, (0 : B))) 0 :=
    ((contDiff_id : ContDiff ℝ ∞ (fun x : A => x)).prodMk
          contDiff_const).contMDiff.mdifferentiableAt
      (by simp)
  have hκ : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun y : B => ((0 : A), y)) 0 :=
    (contDiff_const.prodMk
          (contDiff_id : ContDiff ℝ ∞ (fun y : B => y))).contMDiff.mdifferentiableAt
      (by simp)
  have hqdiff : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, Z) (fun x : A => Q (x, 0)) 0 :=
    (Q.mdifferentiableAt (by simp) hQsrc).comp (f := fun x : A => (x, (0 : B))) 0 hι
  have hpdiff : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun y : B => P (0, y)) 0 :=
    (P.mdifferentiableAt (by simp) hPsrc).comp (f := fun y : B => ((0 : A), y)) 0 hκ
  exact
    ChartMapPerturbation.transverse_in_chart P.symm hqdiff hpdiff hcross htarget
      (htrans hcross)

/-- Relative label sheet germs. -/
theorem TransverseGerms.relative_label_sheet_germs {A B Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hPsrc : (0 : A × B) ∈ P.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u) :
    ((fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0] (fun x : A => H (x, 0))) ∧
      ((fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0] (fun y : B => (0, y))) := by
  have hnearH : ∀ᶠ x : A in 𝓝 0, (x, (0 : B)) ∈ H.source :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually (H.open_source.mem_nhds h0)
  have heqH : (fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0] (fun x : A => H (x, 0)) := by
    filter_upwards [hnearH] with x hx
    rw [← hdiagram (x, 0) hx]
    exact P.left_inv' (hHt (H.map_source' hx))
  have hnearP : ∀ᶠ y : B in 𝓝 0, ((0 : A), y) ∈ P.source :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (P.open_source.mem_nhds hPsrc)
  have heqP : (fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0] (fun y : B => (0, y)) := by
    filter_upwards [hnearP] with y hy
    exact P.left_inv' hy
  exact ⟨heqH, heqP⟩

/-- Relative transversality from label sheets. -/
theorem TransverseGerms.relative_transverse_of_label_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun x : A => Q (x, 0))
        (fun y : B => P (0, y)) 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
      (fun y : B => (0, y)) 0 0 := by
  have hPsrc : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  have ht := label_sheets_transverse_in_incoming_chart Q P (hHs h0) hPsrc hQ0 hP0 htrans
  obtain ⟨heqH, heqP⟩ := relative_label_sheet_germs Q P H h0 hPsrc hHt hdiagram
  rw [heqH.mfderiv_eq, heqP.mfderiv_eq] at ht
  exact fun _ => ht

/-- The relative intersection of a native unique connection. -/
theorem FlowSuspension.relative_intersection_of_native_unique_connection
    {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) (h0U : (0 : Z) ∈ U) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hHs : H.source ⊆ Q.source)
    (hQU : Q.target ⊆ U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0) := by
  intro x hx
  constructor
  · intro hfirst
    have hzU : Q (x, 0) ∈ U := hQU (Q.map_source' (hHs hx))
    have hbot : Filter.Tendsto (fun t => F t (Φ (Q (x, 0), 0))) Filter.atBot (𝓝 q) :=
      (hleftBasin _ hzU).mpr ⟨x, hx, rfl⟩
    have htop1 : Filter.Tendsto (fun t => F t (Φ (Q (x, 0), 1))) Filter.atTop (𝓝 p) :=
      (hrightBasin _ hzU).mpr ⟨H (x, 0), H.map_source' hx, hfirst, hdiagram _ hx⟩
    rw [hflow _ hzU 1] at htop1
    have htop := (MorseCancellation.flow_time_atTop_limit_iff F 1 (Φ (Q (x, 0), 0)) p).mp htop1
    obtain ⟨t, ht⟩ := hunique _ hbot htop
    have hsrc0 : ((0 : Z), t) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, Set.mem_univ _⟩
    have hsrcx : (Q (x, 0), (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hzU, Set.mem_univ _⟩
    have hpoints : Φ (0, t) = Φ (Q (x, 0), 0) := (hflow 0 h0U t).trans ht
    have hlabel : (0 : Z) = Q (x, 0) :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hsrc0 hsrcx hpoints)
    have hpair : (x, (0 : B)) = (0 : A × B) :=
      Q.toOpenPartialHomeomorph.injOn (hHs hx) (hHs h0) (hlabel.symm.trans hQ0.symm)
    exact congrArg Prod.fst hpair
  · intro hx0
    subst x
    change (H (0 : A × B)).1 = 0
    rw [hH0]
    rfl

attribute [local instance 100] Classical.propDecidable in
/-- A cylinder block correction exists. -/
theorem TransverseGerms.exists_cylinder_block_correction {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧
        K ⊆ Q.target ∩ P.target ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)}) ∧
            D 0 = 0 ∧
              (∀ z ∈ H.source, D (Q z) ∈ P.target) ∧
                (∀ x : A, (x, (0 : B)) ∈ H.source → ((P.symm (D (Q (x, 0)))).1 = 0 ↔ x = 0)) ∧
                  (fun z => D (Q z)) =ᶠ[𝓝 (0 : A × B)] (fun z => P (L₁ z.1, L₂ z.2)) := by
  obtain ⟨L₁, _, L₂, Dₛ, Dₜ, Kₛ, Kₜ, hKₛ, hKs, hKₜ, hKt, ⟨Iₛ⟩, ⟨Iₜ⟩, hDₛ, hDₜ, huniq, hgerm⟩ :=
    exists_block_reduction_of_native_transverse H h0 hH0 htrans hunique
  have hP0 : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  obtain ⟨D, K, hK, _, hKU, hI, hD0, hformula⟩ :=
    exists_transported_transition_correction Q P H (hHs h0) hP0 hQzero hPzero hHs hHt hdiagram Dₛ
      Dₜ hKₛ hKₜ hKs hKt (show (0 : A × B) ∈ {p : A × B | p.2 = 0} from rfl)
      (show (0 : A × B) ∈ ({(0 : A × B)} : Set (A × B)) from rfl) Iₛ Iₜ
  have hPt (z : A × B) (hz : z ∈ H.source) : Dₜ (H (Dₛ z)) ∈ P.source :=
    hHt (hDₜ (H.map_source' (hDₛ hz)))
  have hinverse (z : A × B) (hz : z ∈ H.source) : P.symm (D (Q z)) = Dₜ (H (Dₛ z)) := by
    rw [hformula z hz]
    exact P.left_inv' (hPt z hz)
  refine ⟨L₁, L₂, D, K, hK, hKU, hI, hD0, ?_, ?_, ?_⟩
  · intro z hz
    rw [hformula z hz]
    exact P.map_source' (hPt z hz)
  · intro x hx
    rw [hinverse (x, 0) hx]
    exact huniq x hx
  · filter_upwards [H.open_source.mem_nhds h0, hgerm] with z hz hg
    rw [hformula z hz, hg]

end
