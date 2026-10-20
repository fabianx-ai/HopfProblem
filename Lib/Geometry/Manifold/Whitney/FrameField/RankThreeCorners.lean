/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame
import Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal

/-!
# Corner signs from a defining map, in normal rank three

For a rank-three tubular bigon, the two corner sheet-pair determinants have opposite signs exactly
when the two corner determinants of a defining map of the second sheet, read in the strip chart of
the first, do (`TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants`): the
intersection signs of the corners can be computed from a defining map of one sheet.

The case of a belt sphere of a Morse surgery: the belt normal coordinates
(`ManifoldMorse.MorseSurgeryData.beltSheetNormal`) are such a defining map, and the corner
intersection signs are opposite exactly when the corner determinants of the belt normal coordinates
are (`ManifoldMorse.MorseSurgeryData.opposite_belt_corners_iff_normal_sheet_determinants`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §§5–6.

## Tags

Whitney trick, intersection sign, belt sphere
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- In the rank-three situation, the two corner sheet-pair determinants have opposite signs exactly
when the two corner determinants of a defining map of the second sheet, read in the strip chart
of the first, do: the intersection signs can be computed from a local defining function. -/
theorem TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 1))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ O)
    (hqs :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.Surjective
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) q
            (e.chart (StripCoordinates.center t)))) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (1, 0)).det <
        0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := IntersectionCoordinates.pairCoordinates FrameField.rankThreePairCoordinates
  let G := e.sheetDifferential tube.chart
  let L := d.sheetDifferential tube.chart
  let C (t : ℝ) := (e.sheetComplement tube.chart t).comp i.toContinuousLinearMap
  let Q := e.normalDetector tube.chart q
  have htarget :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ tube.chart.target :=
    fun _ ht => tube.upper_chart_center_mem_target e ht
  have hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1) :=
    (e.contDiffOn_sheetDifferential tube.chart).mono (fun t ht => ⟨e.line ht, htarget t ht⟩)
  have hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1) :=
    ((e.contDiffOn_sheetComplement tube.chart).mono
          (fun t ht => ⟨e.line ht, htarget t ht⟩)).clm_comp
      contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1) :=
    e.contDiffOn_normalDetector tube.chart q hO hq htarget hcenter
  have hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := by
    intro t ht
    let p :=
      ContinuousLinearEquiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) i
    have heq :
      (G t).coprod (C t) =
        ((e.sheetDifferential tube.chart t).coprod (e.sheetComplement tube.chart t)).comp
          p.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    apply FrameField.isInvertible_coprod_of_bijective
    rw [heq]
    exact
      (e.isInvertible_sheet_coprod_complement tube.chart ht (htarget t ht)).bijective.comp
        p.bijective
  have hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t) := fun t ht =>
    e.surjective_normalDetector tube.chart q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht))) (hqs t ht)
  have hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0 := fun t ht =>
    e.normalDetector_comp_sheet_eq_zero tube.chart q hO hq hzero ht (htarget t ht) (hcenter t ht)
  have hsign :=
    FrameField.opposite_intersectionDet_iff_normalDet j G C L Q hG hC hQ hi hQs hQG
  have hdet (t : ℝ) :
    tube.rankThreeSheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    IntersectionCoordinates.det_jointBlock_eq_tangentSum
      FrameField.rankThreePairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.rankThree_corner_sheet_charts_coincide d e ht
    have hqD :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q
        (d.chart (StripCoordinates.center t)) :=
      hpoint.symm ▸ hq.contMDiffAt (hO.mem_nhds (hcenter t htI))
    have hQeq : Q t = d.normalDetector tube.chart q t := by
      change e.normalDetector tube.chart q t = d.normalDetector tube.chart q t
      unfold StripNormalData.normalDetector
      rw [hpoint]
    rw [hQeq]
    exact
      d.normalDetector_comp_sheet tube.chart q htI (tube.lower_chart_center_mem_target d htI) hqD
  rw [hdet 0, hdet 1]
  exact hsign.trans (by rw [hcoeff 0 (Or.inl rfl), hcoeff 1 (Or.inr rfl)])

/-- The normal coordinates of the belt sphere in the negative directions of a Morse chart, read
through a chosen splitting `j`. -/
def ManifoldMorse.MorseSurgeryData.beltSheetNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) :
    D.UpperLevel → (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  j.symm ∘ D.beltNormal

attribute [local instance 100] Classical.propDecidable in
/-- For a rank-three tubular bigon between a sheet and a belt sphere of a Morse surgery, the two
corner intersection signs are opposite exactly when the two corner determinants of the belt
normal coordinates are. -/
theorem ManifoldMorse.MorseSurgeryData.opposite_belt_corners_iff_normal_sheet_determinants
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) {S : Set D.UpperLevel}
    {a b : ℝ → D.UpperLevel} {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∀
      (tube :
        TubularBigon (E := RegularLevel.Model E) S (Set.range D.surgery.beltSphere) a
          b k l h 3)
      (d :
        StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          RegularLevel.Model E) S k)
      (e :
        StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          RegularLevel.Model E) (Set.range D.surgery.beltSphere) l),
      (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (0, 0)).det *
            (fderiv ℝ
                (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (1, 0)).det <
          0 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro tube d e
  have hq :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞
      (D.beltSheetNormal j) D.beltNormalDomain :=
    j.symm.contDiff.contMDiff.comp_contMDiffOn (D.contMDiffOn_beltNormal hf)
  have hcenter (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ Set.range D.surgery.beltSphere :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ D.beltNormalDomain := by
    obtain ⟨v, hv⟩ := hcenter t ht
    exact hv ▸ D.belt_mem_normalDomain v
  apply
    tube.opposite_rankThree_corners_iff_normal_sheet_determinants d e (D.beltSheetNormal j)
      D.isOpen_beltNormalDomain hq
  · rintro y ⟨⟨v, rfl⟩, _⟩
    change j.symm (D.beltNormal (D.surgery.beltSphere v)) = 0
    rw [D.beltNormal_belt, map_zero]
  · exact hcenterO
  · intro t ht
    obtain ⟨v, hv⟩ := hcenter t ht
    rw [← hv]
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt
        (D.isOpen_beltNormalDomain.mem_nhds (D.belt_mem_normalDomain v))
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (D.surgery.beltSphere v)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hjSmooth :
      ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
      j.symm.contDiff.contMDiff
    rw [beltSheetNormal,
      mfderiv_comp _ (hjSmooth.mdifferentiableAt (by simp)) (hnormal.mdifferentiableAt (by simp)),
      hJ]
    exact j.symm.surjective.comp (D.surjective_beltNormal_derivative hf v)

end
