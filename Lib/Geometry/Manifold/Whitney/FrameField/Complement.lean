/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Collar.RangeTransport

/-!
# Smooth orthogonal complements of a family of injective maps

In a finite-dimensional inner-product space `F`, the coproduct `L ⊞ B` of two injective maps is
bijective when `range B = (range L)ᗮ` (`FrameField.bijective_coprod_of_orthogonal_range`).
A smooth family `x ↦ L x : D →L F` of injective maps near a compact star-shaped set `K` admits a
smooth family of complements `B x : ℝⁿ →L F`, `dim D + n = dim F`, with `range (B x) = (range L x)ᗮ`
on `K` and `L x ⊞ B x` bijective on a neighbourhood of `K`
(`FrameField.exists_smooth_complement_near_starConvex_on`,
`FrameField.exists_smooth_complement_near_starConvex`).

This is the triviality of the orthogonal-complement bundle over a contractible base, built from the
Gram projection onto the range; cf. Milnor–Stasheff, *Characteristic classes*, Ch. 3 (orthogonal
complements of subbundles).

## Tags

orthogonal complement, frame field, vector bundle
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- In an inner-product space, the coproduct of two injective maps is bijective as soon as the range
of the second is the orthogonal complement of the range of the first. -/
theorem FrameField.bijective_coprod_of_orthogonal_range {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F)
    (B : Z →L[ℝ] F) (hL : Function.Injective L) (hB : Function.Injective B)
    (hr : B.range = L.rangeᗮ) : Function.Bijective (L.coprod B) := by
  have hd : Disjoint L.range B.range := by
    rw [hr]
    exact L.range.orthogonal_disjoint
  constructor
  · change Function.Injective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  · change Function.Surjective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact L.range.isCompl_orthogonal.sup_eq_top

/-- A smooth family of injective maps `L x : D →L F` on a neighbourhood of a compact star-shaped set
`K` admits a smooth family of complements: a family `B` whose range is `(L x)ᗮ` on `K` and for
which `L x ⊞ B x` is bijective on a neighbourhood of `K`. -/
theorem FrameField.exists_smooth_complement_near_starConvex_on {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} {O : Set E} (hO : IsOpen O) (hL : ContDiffOn ℝ ∞ L O) {K : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hKO : K ⊆ O)
    (hi : ∀ x ∈ K, Function.Injective (L x)) (n : ℕ)
    (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)) ≃L[ℝ] D :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let A (x : E) := (L x).comp φ.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A O := hL.clm_comp contDiffOn_const
  have hAr (x : E) : (A x).range = (L x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
  let U : Set E := O ∩ {x | Function.Injective (L x)}
  have hU : IsOpen U :=
    hL.continuousOn.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_injective
  have hKU : K ⊆ U := fun x hx => ⟨hKO hx, hi x hx⟩
  let P (x : E) : F →L[ℝ] F := 1 - gramProjection (A x)
  have hP (x : E) (hx : x ∈ U) : P x = ((L x).rangeᗮ).starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hx.2.comp φ.injective)]
    simp only [hAr]
    exact (Submodule.starProjection_orthogonal' (L x).range).symm
  have hsP : ContDiffOn ℝ ∞ P U := by
    intro x hx
    have hg : ContDiffAt ℝ ∞ (fun y => gramProjection (A y)) x :=
      (contMDiffAt_gramProjection (hA.contDiffAt (hO.mem_nhds hx.1)).contMDiffAt
          (hx.2.comp φ.injective)).contDiffAt
    exact (contDiffAt_const.sub hg).contDiffWithinAt
  have hidem : ∀ x ∈ K, IsIdempotentElem (P x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact ((L x).rangeᗮ).isIdempotentElem_starProjection
  obtain ⟨W, hW, hKW, B₀, hB₀, hB₀i⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU P hidem hsP
  have hr (x : E) (hx : x ∈ K) : (P x).range = (L x).rangeᗮ := by
    rw [hP x (hKU hx), Submodule.range_starProjection]
  have hcenter : Module.finrank ℝ (P 0).range = n := by
    have hrank : Module.finrank ℝ (L 0).range = Module.finrank ℝ D :=
      LinearMap.finrank_range_of_inj (hi 0 h0)
    have hs := (L 0).range.finrank_add_finrank_orthogonal
    rw [hrank] at hs
    rw [hr 0 h0]
    omega
  let ψ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (P 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  let B (x : E) := (B₀ x).comp ψ.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ B (W ∩ O) := (hB₀.clm_comp contDiffOn_const).mono Set.inter_subset_left
  have hBr : ∀ x ∈ K, (B x).range = (L x).rangeᗮ := by
    intro x hx
    calc
      (B x).range = (B₀ x).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ψ.surjective)
      _ = (P x).range := (hB₀i x hx).2
      _ = (L x).rangeᗮ := hr x hx
  have hBi : ∀ x ∈ K, Function.Injective (B x) := fun x hx => (hB₀i x hx).1.comp ψ.injective
  let T (x : E) := (L x).coprod (B x)
  have hT : ContDiffOn ℝ ∞ T (W ∩ O) := by
    have hs :=
      ((hL.mono Set.inter_subset_right).clm_comp
            (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin n))))).add
        (hB.clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin n)))))
    exact hs
  have hTi : ∀ x ∈ K, Function.Bijective (T x) := fun x hx =>
    bijective_coprod_of_orthogonal_range (L x) (B x) (hi x hx) (hBi x hx) (hBr x hx)
  let V : Set E := (W ∩ O) ∩ {x | Function.Injective (T x)}
  have hV : IsOpen V :=
    hT.continuousOn.isOpen_inter_preimage (hW.inter hO) ContinuousLinearMap.isOpen_injective
  refine
    ⟨V, hV, fun x hx => ⟨⟨hKW hx, hKO hx⟩, (hTi x hx).1⟩, B, hB.mono Set.inter_subset_left, hBr,
      ?_⟩
  intro x hx
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hx.2⟩

/-- Version of `FrameField.exists_smooth_complement_near_starConvex_on` for a family that is smooth
on the whole space. -/
theorem FrameField.exists_smooth_complement_near_starConvex {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} (hL : ContDiff ℝ ∞ L) {K : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hi : ∀ x ∈ K, Function.Injective (L x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) :=
  exists_smooth_complement_near_starConvex_on isOpen_univ hL.contDiffOn hK hstar h0
    (Set.subset_univ K) hi n hdim

end
