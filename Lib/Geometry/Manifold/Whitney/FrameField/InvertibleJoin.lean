/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.PlanarFrame

/-!
# Smooth joins of invertible germs

Two smooth germs at `0` and `1` of invertible endomorphisms of a real space of dimension one or two,
whose determinants have the same sign, are joined by a smooth path of invertible endomorphisms
(`FrameField.exists_smooth_invertible_join_of_finrank_one`,
`FrameField.exists_smooth_invertible_join_of_finrank_two`), the dimension-two case reducing to the
two path components of `GL₂(ℝ)` in `PlanarFrame`.

Applied to the coefficients in the quotient complement of a frame `G`: if the complement
directions have dimension one or two, a path `L` whose endpoint frames `G ⊞ L` have determinants of
the same sign can be replaced, keeping its germs at `0` and `1`, by a path `H` with `G ⊞ H`
invertible throughout
(`FrameField.exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two`,
`FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6 (extending the framing along the boundary of
the Whitney disc).

## Tags

general linear group, frame, homotopy of frames
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- Version of the join of two germs of invertible endomorphisms of the same determinant sign for an
abstract real vector space of dimension two. -/
theorem FrameField.exists_smooth_invertible_join_of_finrank_two {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 2) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane = Module.finrank ℝ D := by
    simp [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self, hdim]
  let e : PlaneImmersion.Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq hdim'
  let a' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((a t).comp e.toContinuousLinearMap)
  let b' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((b t).comp e.toContinuousLinearMap)
  have ha' : ContDiffOn ℝ ∞ a' U := contDiffOn_const.clm_comp (ha.clm_comp contDiffOn_const)
  have hb' : ContDiffOn ℝ ∞ b' V := contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const)
  have hadet (t : ℝ) : (a' t).toLinearMap.det = (a t).toLinearMap.det :=
    LinearMap.det_conj (a t).toLinearMap e.symm.toLinearEquiv
  have hbdet (t : ℝ) : (b' t).toLinearMap.det = (b t).toLinearMap.det :=
    LinearMap.det_conj (b t).toLinearMap e.symm.toLinearEquiv
  have hsign' : 0 < (a' 0).toLinearMap.det * (b' 1).toLinearMap.det := by
    rw [hadet, hbdet]
    exact hsign
  obtain ⟨L', hL', hi', hdet', hleft, hright⟩ :=
    PlanarFrame.exists_smooth_join_of_same_determinant_sign ha' hb' hU hV h0U h1V hsign'
  let L (t : ℝ) := e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp (hL'.clm_comp contDiff_const)
  have hi (t : ℝ) : Function.Bijective (L t) := e.bijective.comp ((hi' t).comp e.symm.bijective)
  have hdet (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have heq : (L t).toLinearMap.det = (L' t).toLinearMap.det :=
      LinearMap.det_conj (L' t).toLinearMap e.toLinearEquiv
    rw [heq, ← hadet 0]
    exact hdet' t
  refine ⟨L, hL, hi, hdet, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = a t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (a t (e (e.symm v)))) = a t v
    simp only [e.apply_symm_apply]
  · filter_upwards [hright] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = b t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (b t (e (e.symm v)))) = b t v
    simp only [e.apply_symm_apply]


/-- Version of the join of two germs of invertible endomorphisms of the same determinant sign for a
space of dimension one. -/
theorem FrameField.exists_smooth_invertible_join_of_finrank_one {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 1) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S : TopologicalSpace.Opens (D →L[ℝ] D) :=
    ⟨{L | 0 < σ * L.toLinearMap.det},
      isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hpos : 0 < σ * (a 0).toLinearMap.det := mul_self_pos.mpr ha0ne
  have ha0 : a 0 ∈ S := hpos
  have hb1 : b 1 ∈ S := hsign
  let γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S) :=
    { toFun := fun t =>
        ⟨(1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1,
          by
          change 0 < σ * ((1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1).toLinearMap.det
          rw [det_smul_add_of_finrank_one hdim]
          have heq :
            σ * ((1 - (t : ℝ)) * (a 0).toLinearMap.det + (t : ℝ) * (b 1).toLinearMap.det) =
              (1 - (t : ℝ)) * (σ * (a 0).toLinearMap.det) +
                (t : ℝ) * (σ * (b 1).toLinearMap.det) := by ring
          rw [heq]
          by_cases ht : (t : ℝ) = 0
          · simpa only [ht, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero] using hpos
          · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
            exact
              add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hpos.le)
                (mul_pos htpos hsign)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      source' := by
        apply Subtype.ext
        simp
      target' := by
        apply Subtype.ext
        simp }
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩


/-- If the complement directions have dimension one or two, a path `L` whose endpoint coefficients
in the quotient complement have determinants of the same sign can be replaced, keeping its germs
at `0` and `1`, by a path `H` for which `G ⊞ H` is invertible throughout. -/
theorem FrameField.exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (h1U : (1 : ℝ) ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ U, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective (G t) (C t) (hi t ht)
  let K (t : ℝ) := (complementQuotient (G t) (C t)).comp (L t)
  have hK : ContDiffOn ℝ ∞ K U := (contDiffOn_complementQuotient hU hG hC hinv).clm_comp hL
  have hjoin :=
    hdim.elim
      (fun hd => exists_smooth_invertible_join_of_finrank_one hd hK hK hU hU h0U h1U hsign)
      (fun hd => exists_smooth_invertible_join_of_finrank_two hd hK hK hU hU h0U h1U hsign)
  obtain ⟨K', hK', hiK', _, hleft, hright⟩ := hjoin
  let H (t : ℝ) := correctedComplement (G t) (C t) (L t) (K' t)
  have hH : ContDiffOn ℝ ∞ H U := contDiffOn_correctedComplement hU hG hC hL hK'.contDiffOn hinv
  refine
    ⟨H, hH, fun t ht =>
      bijective_coprod_correctedComplement (G t) (C t) (L t) (K' t) (hinv t ht) (hiK' t), ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)
  · filter_upwards [hright] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)

/-- Frame-determinant form of the previous statement: the hypothesis is the sign of the product of
the two endpoint determinants of `G ⊞ L` read through the splitting `j`. -/
theorem FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    (j : (D × Z) ≃L[ℝ] F) {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ ∞ G U)
    (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective _ _ (hi t (hIU ht))
  have hcoeff := (same_sign_frames_iff_coefficients j (hG.mono hIU) (hC.mono hIU) hinv).mp hsign
  exact
    exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two hdim hU (hIU (by simp))
      (hIU (by simp)) hG hC hL hi hcoeff

end
