/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs
import Lib.Geometry.Manifold.Whitney.RankThreeModel.Model

/-!
# Correcting a map along the two sheets

For maps `R G : ℝ × A → F`, the centred correction `SheetCorrection.centeredCorrection R G` is
`R - G` minus its value at the centre `(s, 0)`; it vanishes on the centre line, is smooth where `R`
and `G` are, and has zero derivative at a centre point where `R` and `G` have the same derivative.
In the rank-three model, `RankThreeWhitneyModel.correctedSheetMap G Rlo Rhi h` adds to a map
`G` the centred corrections towards prescribed parametrisations `Rlo` of the lower and `Rhi` of
the upper sheet: the result equals `Rlo` on the lower sheet and `Rhi` on the upper sheet
(`correctedSheetMap_lower`, `correctedSheetMap_upper`), agrees with `G` on the zero section, is
smooth on the correction domain, and has the derivative of `G` along the zero section
(`hasFDerivAt_correctedSheetMap_zero`).

This is the step which makes a tubular chart along a Whitney disc carry the two model sheets onto
the two given sheets; cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, chart, correction
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- The projection of a sheet parameter to its centre: `(s, u) ↦ (s, 0)`. -/
def SheetCorrection.centerProjection {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (ℝ × A) →L[ℝ] (ℝ × A) :=
  (ContinuousLinearMap.fst ℝ ℝ A).prod (0 : (ℝ × A) →L[ℝ] A)

/-- Value of the centre projection. -/
theorem SheetCorrection.centerProjection_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : ℝ × A) : centerProjection p = (p.1, 0) :=
  rfl

/-- The correction of `G` towards `R` along a sheet: the difference `R - G` with its value at the
centre subtracted, so that it vanishes on the centre line. -/
def SheetCorrection.centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (p : ℝ × A) : F :=
  (R p - G p) - (R (centerProjection p) - G (centerProjection p))

/-- The centred correction vanishes on the centre line. -/
theorem SheetCorrection.centeredCorrection_zero {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (s : ℝ) :
    centeredCorrection R G (s, 0) = 0 := by
  simp only [centeredCorrection, centerProjection_apply, sub_self]

/-- Where `R` and `G` agree at the centre, the centred correction is simply `R - G`. -/
theorem SheetCorrection.centeredCorrection_eq_sub {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] {R G : (ℝ × A) → F} {p : ℝ × A}
    (hcenter : R (p.1, 0) = G (p.1, 0)) : centeredCorrection R G p = R p - G p := by
  simp only [centeredCorrection, centerProjection_apply, hcenter, sub_self, sub_zero]

/-- The centred correction is smooth where `R` and `G` are. -/
theorem SheetCorrection.contDiffOn_centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F] {R G : (ℝ × A) → F}
    {D : Set (ℝ × A)} (hR : ContDiffOn ℝ ∞ R D) (hG : ContDiffOn ℝ ∞ G D) :
    ContDiffOn ℝ ∞ (centeredCorrection R G) (D ∩ centerProjection ⁻¹' D) :=
  ((hR.sub hG).mono Set.inter_subset_left).sub
    ((hR.sub hG).comp (centerProjection (A := A)).contDiff.contDiffOn (fun _ hp => hp.2))

/-- If `R` and `G` have the same derivative at a centre point, the centred correction has vanishing
derivative there. -/
theorem SheetCorrection.hasFDerivAt_centeredCorrection_zero {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R G : (ℝ × A) → F} {L : (ℝ × A) →L[ℝ] F} {s : ℝ} (hR : HasFDerivAt R L (s, 0))
    (hG : HasFDerivAt G L (s, 0)) :
    HasFDerivAt (centeredCorrection R G) (0 : (ℝ × A) →L[ℝ] F) (s, 0) := by
  have hdiff : HasFDerivAt (fun p => R p - G p) (0 : (ℝ × A) →L[ℝ] F) (s, (0 : A)) := by
    convert hR.sub hG using 1 <;>
      first
      | rfl
      | simp only [sub_self]
  have hcenter := hdiff.comp (s, (0 : A)) (centerProjection (A := A)).hasFDerivAt
  convert hdiff.sub hcenter using 1 <;>
    first
    | rfl
    | simp only [ContinuousLinearMap.zero_comp, sub_self]

/-- The lower sheet coordinates of a point of the rank-three model: its time coordinate and its
lower normal coordinate. -/
def RankThreeWhitneyModel.lowerSheetCoordinates : Space →L[ℝ] LowerSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.fst ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

/-- The upper sheet coordinates of a point of the rank-three model: its time coordinate and its
upper normal coordinate. -/
def RankThreeWhitneyModel.upperSheetCoordinates : Space →L[ℝ] UpperSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.snd ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

/-- The map `G` corrected along both sheets so as to agree with the prescribed parametrisations
`Rlo` and `Rhi` there, without changing it on the zero section. -/
def RankThreeWhitneyModel.correctedSheetMap {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : Space) : F :=
  G p + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (lowerSheetCoordinates p) +
    SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (upperSheetCoordinates p)

/-- The corrected map agrees with `G` on the zero section of the model. -/
theorem RankThreeWhitneyModel.correctedSheetMap_zero {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : ℝ × ℝ) :
    correctedSheetMap G Rlo Rhi h (p, 0) = G (p, 0) := by
  change
    G (p, 0) + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (p.1, 0) +
        SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (p.1, 0) =
      G (p, 0)
  rw [SheetCorrection.centeredCorrection_zero,
    SheetCorrection.centeredCorrection_zero, add_zero, add_zero]

/-- On the lower sheet the corrected map is the prescribed lower parametrisation. -/
theorem RankThreeWhitneyModel.correctedSheetMap_lower {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : LowerSheet)
    (hcenter : Rlo (q.1, 0) = G (firstSheet (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (firstSheet q) = Rlo q := by
  have hlo : lowerSheetCoordinates (firstSheet q) = q := rfl
  have hhi : upperSheetCoordinates (firstSheet q) = (q.1, 0) := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

/-- On the upper sheet the corrected map is the prescribed upper parametrisation. -/
theorem RankThreeWhitneyModel.correctedSheetMap_upper {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : UpperSheet)
    (hcenter : Rhi (q.1, 0) = G (secondSheet h (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (secondSheet h q) = Rhi q := by
  have hlo : lowerSheetCoordinates (secondSheet h q) = (q.1, 0) := rfl
  have hhi : upperSheetCoordinates (secondSheet h q) = q := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

/-- The domain of the correction: the points whose sheet coordinates and their centres lie in the
two sheet domains. -/
def RankThreeWhitneyModel.correctionDomain (U : Set Space) (Dlo : Set LowerSheet)
    (Dhi : Set UpperSheet) : Set Space :=
  U ∩
    (lowerSheetCoordinates ⁻¹' (Dlo ∩ SheetCorrection.centerProjection ⁻¹' Dlo) ∩
      upperSheetCoordinates ⁻¹' (Dhi ∩ SheetCorrection.centerProjection ⁻¹' Dhi))

/-- The correction domain is open. -/
theorem RankThreeWhitneyModel.isOpen_correctionDomain {U : Set Space} {Dlo : Set LowerSheet}
    {Dhi : Set UpperSheet} (hU : IsOpen U) (hDlo : IsOpen Dlo) (hDhi : IsOpen Dhi) :
    IsOpen (correctionDomain U Dlo Dhi) :=
  hU.inter
    (((hDlo.inter (hDlo.preimage SheetCorrection.centerProjection.continuous)).preimage
          lowerSheetCoordinates.continuous).inter
      ((hDhi.inter (hDhi.preimage SheetCorrection.centerProjection.continuous)).preimage
        upperSheetCoordinates.continuous))

/-- The corrected map is smooth on the correction domain. -/
theorem RankThreeWhitneyModel.contDiffOn_correctedSheetMap {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {U : Set Space} {Dlo : Set LowerSheet} {Dhi : Set UpperSheet}
    (hG : ContDiffOn ℝ ∞ G U) (hRlo : ContDiffOn ℝ ∞ Rlo Dlo)
    (hGlo : ContDiffOn ℝ ∞ (G ∘ firstSheet) Dlo) (hRhi : ContDiffOn ℝ ∞ Rhi Dhi)
    (hGhi : ContDiffOn ℝ ∞ (G ∘ secondSheet h) Dhi) :
    ContDiffOn ℝ ∞ (correctedSheetMap G Rlo Rhi h) (correctionDomain U Dlo Dhi) :=
  ((hG.mono Set.inter_subset_left).add
        ((SheetCorrection.contDiffOn_centeredCorrection hRlo hGlo).comp
          lowerSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.1))).add
    ((SheetCorrection.contDiffOn_centeredCorrection hRhi hGhi).comp
      upperSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.2))

/-- At a point of the zero section the corrected map has the same derivative as the uncorrected one,
the two corrections having vanishing derivative there. -/
theorem RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {p : ℝ × ℝ} {L : Space →L[ℝ] F} {Llo : LowerSheet →L[ℝ] F}
    {Lhi : UpperSheet →L[ℝ] F} (hG : HasFDerivAt G L (p, 0)) (hRlo : HasFDerivAt Rlo Llo (p.1, 0))
    (hGlo : HasFDerivAt (G ∘ firstSheet) Llo (p.1, 0)) (hRhi : HasFDerivAt Rhi Lhi (p.1, 0))
    (hGhi : HasFDerivAt (G ∘ secondSheet h) Lhi (p.1, 0)) :
    HasFDerivAt (correctedSheetMap G Rlo Rhi h) L (p, 0) := by
  have hlo :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) ∘ lowerSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRlo hGlo).comp
        (p, (0 : Lower × Upper)) lowerSheetCoordinates.hasFDerivAt
  have hhi :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) ∘ upperSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRhi hGhi).comp
        (p, (0 : Lower × Upper)) upperSheetCoordinates.hasFDerivAt
  convert (hG.add hlo).add hhi using 1 <;>
    first
    | rfl
    | simp only [add_zero]


end
