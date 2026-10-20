/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.BoundaryArcs
import Lib.Geometry.Manifold.Whitney.FrameField.IntersectionCoordinates
import Lib.Geometry.Manifold.Whitney.FrameField.InvertibleJoin
import Lib.Geometry.Manifold.Whitney.FrameField.BoundaryField

/-!
# The adapted frame over a bigon in normal rank three

The rank-three case of the framing of the Whitney disc: the normal space of the bigon is
`ℝ² × ℝ¹ ≃ ℝ³` (`FrameField.rankThreePairCoordinates`), split into the normal directions of the two
sheets. If the corner determinants of the two normal frames have the same sign, the lower normal
frame extends to a globally smooth field on the plane, completed over a neighbourhood of the bigon
by a smooth two-column field and restricting to the normal frames of the sheets along the two arcs
(`TubularBigon.exists_rankThree_adapted_frame_of_normal_sign`).

The sheet-pair determinant at a parameter is `8 h (2t - 1)` times the normal-frame determinant
(`TubularBigon.rankThreeSheetPairDet_eq`); the factor changes sign between the corners, so the
condition is equivalent to opposite intersection signs at the two corners
(`TubularBigon.opposite_rankThree_corner_determinants_iff_normal_sign`), giving
`TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs`.

Milnor, *Lectures on the h-cobordism theorem*, §6, treats the general case `k + l = n`; this file
is the case of normal rank three used by the Whitney model of this library.

## Tags

Whitney trick, framing, intersection sign
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- A fixed linear identification `ℝ² × ℝ¹ ≃ ℝ³` of the split rank-three normal space with
`EuclideanSpace ℝ (Fin 3)`. -/
def FrameField.rankThreePairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

/-- The determinant of a pair of frames `A : ℝ² →L ℝ³` and `B : ℝ¹ →L ℝ³`, read through the
identification `ℝ² × ℝ¹ ≃ ℝ³`. -/
def FrameField.rankThreePairDet
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (rankThreePairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

/-- In the rank-three situation, if the two corner frame determinants have the same sign, the normal
frame along the lower sheet can be replaced by a smooth complement `H` of the upper normal frame
on a neighbourhood of `[0, 1]`, with the same germs at both corners. -/
theorem TubularBigon.exists_rankThree_boundary_complement_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        Set.Icc (0 : ℝ) 1 ⊆ U ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
            ∃ H : ℝ → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
              ContDiffOn ℝ ∞ H U ∧
                (∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
                  (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
                    (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, -⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, -, hRC⟩ :=
    tube.upper_sheetFrame_complement_of_finrank e 1 (by simp only [finrank_euclideanSpace_fin])
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Set.Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from Set.inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from Set.inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from Set.inter_subset_right)
  have hsplit : ∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
      (Or.inl finrank_euclideanSpace_fin) FrameField.rankThreePairCoordinates hU hIU hRU hCU
      hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

/-- The complement of the previous statement, transported to a field on a neighbourhood of the
boundary of the bigon: it has the germ of the lower normal frame along the lower arc, completes
the upper normal frame along the upper arc, and is injective on the boundary. -/
theorem TubularBigon.exists_rankThree_planar_boundary_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (WhitneyPairModel.bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                  W =ᶠ[𝓝 (2 * t - 1, 0)]
                    (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    Function.Bijective
                      ((e.normalFrame tube.chart t).coprod
                        (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
                  ∀ p ∈ frontier (WhitneyPairModel.bigon h), Function.Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_rankThree_boundary_complement_of_normal_sign d e hsign
  have hHi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t) := by
    intro t ht u v huv
    have heq :
      ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  obtain ⟨O, hO, hfront, W, hW, hlo, hhi, hinj⟩ :=
    WhitneyPairModel.exists_injective_bigon_boundary_field tube.height_pos hD hID hL hH h0
      h1 (tube.lower_sheetFrame d).2 hHi
  refine ⟨O, hO, hfront, W, hW, hlo, ?_, hinj⟩
  intro t ht
  rw [(hhi t ht).eq_of_nhds]
  have htime : WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = t := by
    dsimp [WhitneyPairModel.arcTime]
    ring
  change
    Function.Bijective
      ((e.normalFrame tube.chart t).coprod
        (H (WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))))
  rw [htime]
  exact hcomp t (hID ht)

/-- The boundary field of the previous statement extends to a globally smooth field on the plane
which, on a neighbourhood of the bigon, is completed by a smooth two-column field spanning its
orthogonal complement. -/
theorem TubularBigon.exists_rankThree_planar_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
              Function.Bijective
                ((e.normalFrame tube.chart t).coprod
                  (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
            ∃ V : Set (ℝ × ℝ),
              IsOpen V ∧
                WhitneyPairModel.bigon h ⊆ V ∧
                  ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                    ContDiffOn ℝ ∞ B V ∧
                      (∀ p ∈ WhitneyPairModel.bigon h, (B p).range = (W p).rangeᗮ) ∧
                        ∀ p ∈ V, Function.Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_rankThree_planar_boundary_frame_of_normal_sign d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    FrameField.exists_completed_one_column_frame finrank_euclideanSpace_fin hO hW₀
      isClosed_frontier hfront (WhitneyPairModel.isCompact_bigon tube.height_pos)
      (WhitneyPairModel.starConvex_bigon tube.height_pos.le)
      (WhitneyPairModel.zero_mem_bigon tube.height_pos.le) (fun p hp => hinj p hp.2)
      finrank_euclideanSpace_fin
  refine ⟨W, hW, ?_, ?_, V, hV, hKV, B, hB, hr, hb⟩
  · intro t ht
    have hp : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact (heq.filter_mono (nhds_le_nhdsSet hp)).trans (hlo t ht)
  · intro t ht
    have hp :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    rw [heq.self_of_nhdsSet hp]
    exact hhi t ht


/-- In the rank-three situation with corner frame determinants of the same sign, there is a globally
smooth field `W` with the germs of the lower normal frame along the lower arc, completed on a
neighbourhood of the bigon by a smooth field `C` that restricts to the upper normal frame along
the upper arc. -/
theorem TubularBigon.exists_rankThree_adapted_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) := by
  obtain ⟨W, hW, hlo, hhi, V, hV, hKV, B, hB, -, hb⟩ :=
    tube.exists_rankThree_planar_frame_of_normal_sign d e hsign
  obtain ⟨⟨D, hD, hID, hG⟩, -⟩ := tube.upper_sheetFrame e
  let r : (ℝ × ℝ) → (ℝ × ℝ) :=
    WhitneyPairModel.upperBoundaryArc h ∘ WhitneyPairModel.arcTime
  have hq : ContDiff ℝ ∞ (WhitneyPairModel.upperBoundaryArc h) := by
    unfold WhitneyPairModel.upperBoundaryArc; fun_prop
  have hr : ContDiff ℝ ∞ r := hq.comp WhitneyPairModel.contDiff_arcTime
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have hrq (t : ℝ) :
    r (WhitneyPairModel.upperBoundaryArc h t) =
      WhitneyPairModel.upperBoundaryArc h t := by
    dsimp only [r, Function.comp_apply]
    rw [htq]
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have hrK : Set.MapsTo r (WhitneyPairModel.bigon h) (WhitneyPairModel.bigon h) :=
    fun _ hp => tube.upperBoundaryArc_mem_bigon (htimeK hp)
  let O₀ := V ∩ (r ⁻¹' V ∩ WhitneyPairModel.arcTime ⁻¹' D)
  have hO₀ : IsOpen O₀ :=
    hV.inter
      ((hV.preimage hr.continuous).inter
        (hD.preimage WhitneyPairModel.contDiff_arcTime.continuous))
  have hKO₀ : WhitneyPairModel.bigon h ⊆ O₀ := fun p hp =>
    ⟨hKV hp, hKV (hrK hp), hID (htimeK hp)⟩
  let C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := fun p =>
    FrameField.transportComplement (W p) (B p) (W (r p)) (B (r p))
      (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))
  have hC : ContDiffOn ℝ ∞ C O₀ := by
    apply
      FrameField.contDiffOn_transportComplement hO₀ hW.contDiffOn
        (hB.mono Set.inter_subset_left) (hW.comp hr).contDiffOn
        (hB.comp hr.contDiffOn (fun _ hp => hp.2.1))
        (hG.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
    intro p hp
    exact FrameField.isInvertible_coprod_of_bijective (W (r p)) (B (r p)) (hb _ hp.2.1)
  have hcompK : ∀ p ∈ WhitneyPairModel.bigon h, Function.Bijective ((W p).coprod (C p)) := by
    intro p hp
    have ht := htimeK hp
    have hupper :
      Function.Bijective
        ((W (r p)).coprod (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))) :=
      FrameField.bijective_coprod_comm _ _ (hhi (WhitneyPairModel.arcTime p) ht)
    exact
      FrameField.bijective_transportComplement (W p) (B p) (W (r p)) (B (r p)) _
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb p (hKV hp)))
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb _ (hKV (hrK hp)))) hupper
  have hTC : ContDiffOn ℝ ∞ (fun p => (W p).coprod (C p)) O₀ :=
    FrameField.contDiffOn_coprod hW.contDiffOn hC
  let O := O₀ ∩ {p | Function.Injective ((W p).coprod (C p))}
  have hO : IsOpen O :=
    hTC.continuousOn.isOpen_inter_preimage hO₀ ContinuousLinearMap.isOpen_injective
  have hKO : WhitneyPairModel.bigon h ⊆ O := fun p hp => ⟨hKO₀ hp, (hcompK p hp).1⟩
  refine ⟨W, hW, hlo, O, hO, hKO, C, hC.mono Set.inter_subset_left, ?_, ?_⟩
  · intro t ht
    dsimp only [C]
    rw [hrq, htq]
    exact
      FrameField.transportComplement_self _ _ _
        (FrameField.isInvertible_coprod_of_bijective _ _
          (hb _ (hKV (tube.upperBoundaryArc_mem_bigon ht))))
  · intro p hp
    have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact ⟨hp.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp.2⟩

/-- The joint block of the two sheet differentials of a rank-three tubular bigon at the parameter
`t`, read in the coordinates `ℝ² × ℝ¹ ≃ ℝ³`. -/
def TubularBigon.rankThreeSheetPairJacobian {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) :
    ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) →L[ℝ]
      ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :=
  IntersectionCoordinates.jointBlock FrameField.rankThreePairCoordinates
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)

/-- The determinant of the joint block of the two sheet differentials: the intersection sign of the
two sheets at the parameter `t`. -/
def TubularBigon.rankThreeSheetPairDet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) : ℝ :=
  (tube.rankThreeSheetPairJacobian d e t).toLinearMap.det

/-- At the two corners of the bigon the strip charts of the two sheets have the same centre
point. -/
theorem TubularBigon.rankThree_corner_sheet_charts_coincide {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t = 0 ∨ t = 1) :
    d.chart (StripCoordinates.center t) = e.chart (StripCoordinates.center t) := by
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hd := (tube.lower_germ t htI).eq_of_nhds
  have he := (tube.upper_germ t htI).eq_of_nhds
  dsimp only [Function.comp_apply] at hd he
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hd
  rw [WhitneyPairModel.upperStripCoordinates_upper, e.center t, hheight] at he
  exact hd.symm.trans he

/-- At each parameter, the sheet pair determinant is `8 h (2 t - 1)` times the determinant of the
pair of normal frames: the two differ by the velocity factor of the boundary arcs. -/
theorem TubularBigon.rankThreeSheetPairDet_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tube.rankThreeSheetPairDet d e t =
      (8 * h * (2 * t - 1)) *
        FrameField.rankThreePairDet (e.normalFrame tube.chart t)
          (d.normalFrame tube.chart t) := by
  rw [rankThreeSheetPairDet, rankThreeSheetPairJacobian,
    IntersectionCoordinates.det_jointBlock FrameField.rankThreePairCoordinates
      (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
      (tube.upper_sheetDifferential_arc e ht) (tube.lower_sheetDifferential_arc d ht),
    e.normal_sheetDifferential tube.chart ht (tube.upper_chart_center_mem_target e ht),
    d.normal_sheetDifferential tube.chart ht (tube.lower_chart_center_mem_target d ht)]
  have hplane :
    (PlaneImmersion.linearMap ((2, -4 * h * (2 * t - 1)), (2, 0))).toLinearMap.det =
      8 * h * (2 * t - 1) := by
    rw [← PlanarFrame.determinant_eq_det, PlanarFrame.determinant_linearMap]
    dsimp [PlanarFrame.area]
    ring
  rw [hplane]
  rfl

/-- The two corner sheet-pair determinants have opposite signs exactly when the two corner
normal-frame determinants have the same sign: the factor `8 h (2 t - 1)` changes sign between
the corners. -/
theorem TubularBigon.opposite_rankThree_corner_determinants_iff_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) := by
  let n :=
    FrameField.rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      FrameField.rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)
  have hprod :
    tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 = -((8 * h) ^ 2 * n) := by
    rw [tube.rankThreeSheetPairDet_eq d e (t := 0) (by simp),
      tube.rankThreeSheetPairDet_eq d e (t := 1) (by simp)]
    dsimp only [n]
    ring
  have hscale : 0 < (8 * h) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) tube.height_pos)
  change (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔ 0 < n
  rw [hprod]
  constructor
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := by linarith
    exact (mul_pos_iff_of_pos_left hscale).mp hp
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := mul_pos hscale hn
    linarith

/-- The adapted frame over the bigon exists as soon as the two corner intersection signs are
opposite, which is the Whitney condition on the two intersection points. -/
theorem TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) :=
  tube.exists_rankThree_adapted_frame_of_normal_sign d e
    ((tube.opposite_rankThree_corner_determinants_iff_normal_sign d e).mp hsign)

end
