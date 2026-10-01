/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.FrameField

/-!
# Determinants of block frames

Linear algebra of frames `G ⊞ C : D × Z →L F` in finite dimension:

* an endomorphism of `D × Z` preserving `D × {0}` has determinant the product of the
  determinants of its diagonal blocks (`FrameField.det_of_zero_lower_left`,
  `FrameField.det_of_fixed_first_factor`); replacing the second block `C` of an invertible frame
  by `L` multiplies the determinant by that of `L` read in the quotient complement of the range
  of `G` (`FrameField.det_frame_eq_det_split_mul_det_coefficient`);
* on a line, a linear map is injective iff nonzero, every endomorphism is its determinant times
  the identity, and the determinant is linear (`FrameField.eq_det_smul_id_of_finrank_one`,
  `FrameField.det_smul_add_of_finrank_one`);
* along a continuous path of invertible maps on `[0, 1]` the endpoint determinants have the same
  sign (`FrameField.det_mul_endpoints_pos`), so the sign comparison of two frames `G ⊞ L` reduces
  to that of their quotient coefficients (`FrameField.same_sign_frames_iff_coefficients`); for a
  map `Q` killing the range of `G`,
  `det (G ⊞ L) * det (Q ∘ C) = det (G ⊞ C) * det (Q ∘ L)`
  (`FrameField.det_intersection_mul_normalComplement`), with its endpoint-sign form
  `FrameField.opposite_intersectionDet_iff_normalDet`.

The block-triangular determinant is `Matrix.det_fromBlocks_zero₂₁` read through bases; the rest
is the bookkeeping behind the comparison of intersection signs in the Whitney trick, cf. Milnor,
*Lectures on the h-cobordism theorem*, §6.

## Tags

determinant, frame, block matrix
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- An endomorphism of `D × Z` preserving the first factor `D × {0}` is block triangular, so its
determinant is the product of the determinants of its two diagonal blocks. -/
theorem FrameField.det_of_zero_lower_left {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, (T (u, 0)).2 = 0) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.fst ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inl ℝ D Z))).toLinearMap.det *
        ((ContinuousLinearMap.snd ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let A := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inl ℝ D Z))
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bD bD A.toLinearMap)
        (LinearMap.toMatrix bZ bD B.toLinearMap) 0 (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hT, A, B, K]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- An endomorphism of `D × Z` fixing the first factor `D × {0}` pointwise has the determinant of
its lower right block on `Z`. -/
theorem FrameField.det_of_fixed_first_factor {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, T (u, 0) = (u, 0)) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.snd ℝ D Z).comp
          (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix bZ bD B.toLinearMap) 0
        (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, hT, B, K, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul, LinearMap.det_toMatrix]

/-- Replacing the second block `C` of an invertible frame `G ⊞ C` by a map `L` multiplies the
determinant of the frame by the determinant of `L` read in the quotient complement of the range
of `G`. -/
theorem FrameField.det_frame_eq_det_split_mul_det_coefficient {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).toLinearMap.det *
        ((complementQuotient G C).comp L).toLinearMap.det := by
  let T := G.coprod C
  let R := G.coprod L
  let A := T.inverse.comp R
  have hA : ∀ u : D, A (u, 0) = (u, 0) := by
    intro u
    change T.inverse (G u + L 0) = (u, 0)
    rw [map_zero, add_zero]
    have hi := h.inverse_apply_self (u, 0)
    change T.inverse (G u + C 0) = (u, 0) at hi
    simpa only [map_zero, add_zero] using hi
  have hblock :
    (ContinuousLinearMap.snd ℝ D Z).comp (A.comp (ContinuousLinearMap.inr ℝ D Z)) =
      (complementQuotient G C).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change (T.inverse (G 0 + L v)).2 = (T.inverse (L v)).2
    rw [map_zero, zero_add]
  have hdetA : A.toLinearMap.det = ((complementQuotient G C).comp L).toLinearMap.det := by
    rw [det_of_fixed_first_factor A hA, hblock]
  have hfactor :
    j.symm.toContinuousLinearMap.comp R = (j.symm.toContinuousLinearMap.comp T).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change j.symm (R v) = j.symm (T (T.inverse (R v)))
    rw [h.self_apply_inverse]
  change (j.symm.toContinuousLinearMap.comp R).toLinearMap.det = _
  rw [hfactor]
  have hmul :
    ((j.symm.toContinuousLinearMap.comp T).comp A).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp T).toLinearMap.det * A.toLinearMap.det :=
    map_mul LinearMap.det _ _
  rw [hmul, hdetA]


/-- A linear map out of a line is injective exactly when it is nonzero. -/
theorem FrameField.injective_iff_ne_zero_of_finrank_one {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) (L : A →L[ℝ] F) : Function.Injective L ↔ L ≠ 0 := by
  constructor
  · intro hi hzero
    let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply hi
    rw [hzero]
    rfl
  · intro hne
    have hr : L.range ≠ ⊥ := by
      intro hbot
      have hz : L.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
      apply hne
      ext x
      exact congrArg (fun f : A →ₗ[ℝ] F => f x) hz
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    have hpos : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr hr
    have hk : Module.finrank ℝ L.ker = 0 := by
      rw [hA] at hrank
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The space of linear maps out of a line has the dimension of the target. -/
theorem FrameField.finrank_one_column {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) : Module.finrank ℝ (A →L[ℝ] F) = Module.finrank ℝ F := by
  rw [← (LinearMap.toContinuousLinearMap : (A →ₗ[ℝ] F) ≃ₗ[ℝ] (A →L[ℝ] F)).finrank_eq,
    Module.finrank_linearMap, hA, one_mul]


/-- On a line, every endomorphism is multiplication by its determinant. -/
theorem FrameField.eq_det_smul_id_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A : D →L[ℝ] D) :
    A.toLinearMap = A.toLinearMap.det • LinearMap.id := by
  obtain ⟨a, ha, -⟩ := A.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hdet : A.toLinearMap.det = a := by
    rw [ha, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]
  rw [hdet]
  exact ha

/-- On a line, the determinant is linear: `det (a • A + b • B) = a det A + b det B`. -/
theorem FrameField.det_smul_add_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A B : D →L[ℝ] D) (a b : ℝ) :
    (a • A + b • B).toLinearMap.det = a * A.toLinearMap.det + b * B.toLinearMap.det := by
  have hlin :
    (a • A + b • B).toLinearMap =
      (a * A.toLinearMap.det + b * B.toLinearMap.det) • LinearMap.id := by
    calc
      _ = a • (A.toLinearMap.det • LinearMap.id) + b • (B.toLinearMap.det • LinearMap.id) :=
        congrArg₂ (fun L K : D →ₗ[ℝ] D => a • L + b • K) (eq_det_smul_id_of_finrank_one hdim A)
          (eq_det_smul_id_of_finrank_one hdim B)
      _ = _ := by rw [smul_smul, smul_smul, ← add_smul]
  rw [hlin, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]


/-- A continuous nowhere-zero real function on `[0, 1]` has endpoint values of the same sign, so
their product is positive. -/
theorem FrameField.mul_endpoints_pos_of_continuous_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) :
    0 < f 0 * f 1 := by
  by_contra h
  rcases mul_nonpos_iff.mp (le_of_not_gt h) with h | h
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf ⟨h.2, h.1⟩
    exact hne t ht hft
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf h
    exact hne t ht hft

/-- A continuous path of invertible endomorphisms on `[0, 1]` has endpoint determinants of the same
sign. -/
theorem FrameField.det_mul_endpoints_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {T : ℝ → (E →L[ℝ] E)}
    (hT : ContinuousOn T (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t)) :
    0 < (T 0).toLinearMap.det * (T 1).toLinearMap.det := by
  apply
    mul_endpoints_pos_of_continuous_nonzero
      (ContinuousLinearMap.continuous_det.comp_continuousOn hT)
  intro t ht hz
  have hker : (T t).toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hker (LinearMap.ker_eq_bot.mpr (hi t ht).1)

/-- For a path of frames `G ⊞ C` that stays invertible, the two endpoint determinants of `G ⊞ L`
have the same sign exactly when the two endpoint determinants of `L` read in the quotient
complement of `G` do. -/
theorem FrameField.same_sign_frames_iff_coefficients {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible) :
    (0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) ↔
      (0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  have hs : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hT : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t) := fun t ht =>
    j.symm.bijective.comp (hi t ht).bijective
  have hpositive := det_mul_endpoints_pos hs.continuousOn hT
  have h0 := det_frame_eq_det_split_mul_det_coefficient j (G 0) (C 0) (L 0) (hi 0 (by simp))
  have h1 := det_frame_eq_det_split_mul_det_coefficient j (G 1) (C 1) (L 1) (hi 1 (by simp))
  rw [h0, h1]
  have heq :
    ((T 0).toLinearMap.det * ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det) *
        ((T 1).toLinearMap.det * ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) =
      ((T 0).toLinearMap.det * (T 1).toLinearMap.det) *
        (((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by ring
  change (0 < ((T 0).toLinearMap.det * _) * ((T 1).toLinearMap.det * _)) ↔ _
  rw [heq]
  exact mul_pos_iff_of_pos_left hpositive


/-- A map `Q` killing the range of `G` factors through the quotient complement of `G` in an
invertible frame `G ⊞ C`. -/
theorem FrameField.normalDetector_eq_comp_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    Q = (Q.comp C).comp (complementQuotient G C) := by
  apply ContinuousLinearMap.ext
  intro v
  let w := (G.coprod C).inverse v
  have hv : G w.1 + C w.2 = v := hi.self_apply_inverse v
  have hzero : Q (G w.1) = 0 := congrArg (fun L : D →L[ℝ] Z => L w.1) hQG
  change Q v = Q (C w.2)
  rw [← hv, map_add, hzero, zero_add]

/-- The determinant identity relating the two ways of measuring `L` against an invertible frame `G ⊞
C`: `det (G ⊞ L) * det (Q ∘ C) = det (G ⊞ C) * det (Q ∘ L)` for any `Q` killing `G`. -/
theorem FrameField.det_intersection_mul_normalComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det * (Q.comp C).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det * (Q.comp L).det := by
  have hnormal : Q.comp L = (Q.comp C).comp ((complementQuotient G C).comp L) := by
    have h := normalDetector_eq_comp_quotient G C Q hi hQG
    exact congrArg (fun R : F →L[ℝ] Z => R.comp L) h
  have hdet : (Q.comp L).det = (Q.comp C).det * ((complementQuotient G C).comp L).det := by
    rw [hnormal]
    exact LinearMap.det_comp _ _
  have hframe :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det *
        ((complementQuotient G C).comp L).det :=
    det_frame_eq_det_split_mul_det_coefficient j G C L hi
  rw [hframe, hdet]
  ring

/-- Endpoint form of the previous identity: the two corner determinants of `G ⊞ L` have opposite
signs exactly when the two corner determinants of `Q ∘ L` do. -/
theorem FrameField.opposite_intersectionDet_iff_normalDet {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : ℝ → (D →L[ℝ] F)) (C L : ℝ → (Z →L[ℝ] F)) (Q : ℝ → (F →L[ℝ] Z))
    (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1)) (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible)
    (hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t))
    (hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0) :
    ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det <
        0) ↔
      ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det < 0 := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  let K (t : ℝ) := (Q t).comp (C t)
  have hT : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hK : ContDiffOn ℝ ∞ K (Set.Icc (0 : ℝ) 1) := hQ.clm_comp hC
  have hTpos :=
    det_mul_endpoints_pos hT.continuousOn (fun t ht => j.symm.bijective.comp (hi t ht).bijective)
  have hKpos :=
    det_mul_endpoints_pos hK.continuousOn
      (fun t ht =>
        TransverseCoordinates.bijective_normal_comp (Q t) (G t) (C t) (hQs t ht)
          (hi t ht).surjective (hQG t ht) rfl)
  have h₀ :=
    det_intersection_mul_normalComplement j (G 0) (C 0) (L 0) (Q 0) (hi 0 (by simp))
      (hQG 0 (by simp))
  have h₁ :=
    det_intersection_mul_normalComplement j (G 1) (C 1) (L 1) (Q 1) (hi 1 (by simp))
      (hQG 1 (by simp))
  let a :=
    (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det
  let b := ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det
  have heq : a * ((K 0).det * (K 1).det) = ((T 0).det * (T 1).det) * b := by
    dsimp [a, b, T, K]
    calc
      _ =
          ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
              ((Q 0).comp (C 0)).det) *
            ((j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det *
              ((Q 1).comp (C 1)).det) := by ring
      _ = _ := by rw [h₀, h₁]; ring
  change a < 0 ↔ b < 0
  constructor
  · intro ha
    have hn : ((T 0).det * (T 1).det) * b < 0 := heq ▸ mul_neg_of_neg_of_pos ha hKpos
    rcases mul_neg_iff.mp hn with ⟨_, hb⟩ | ⟨ht, _⟩
    · exact hb
    · exact (not_lt_of_gt hTpos ht).elim
  · intro hb
    have hn : a * ((K 0).det * (K 1).det) < 0 := heq.symm ▸ mul_neg_of_pos_of_neg hTpos hb
    rcases mul_neg_iff.mp hn with ⟨_, hk⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hKpos hk).elim
    · exact ha

end
