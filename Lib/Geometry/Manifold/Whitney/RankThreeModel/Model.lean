/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs
import Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion

/-!
# The rank-three Whitney model

The rank-three model `RankThreeWhitneyModel.Space = (ℝ × ℝ) × (ℝ¹ × ℝ²)`: the bigon plane times a
lower normal line and an upper normal plane. The lower sheet `firstSheet (s, u) = ((s, 0), (u, 0))`
and the upper sheet `secondSheet h (s, v) = ((s, h (1 - s²)), (0, v))` are smooth with explicit
derivatives, meet the zero section exactly in the two boundary arcs of the bigon
(`zero_mem_firstSheet_iff`, `zero_mem_secondSheet_iff`), and meet each other exactly at the two
corners `s = ±1` (`firstSheet_eq_secondSheet_iff`). The model embeds linearly in the Whitney pair
model (`expand`) with a linear left inverse (`collapse`), and `nativeFirstSheet`,
`nativeSecondSheet` are the images of the two model sheets under a chart.

This is the standard local model of two transverse submanifolds of complementary dimensions
`2` and `3` in a manifold of dimension five, meeting in the two corners of a Whitney disc:
Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, local model
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- The sheet direction of the lower sheet in the rank-three model: a line. -/
abbrev RankThreeWhitneyModel.Lower :=
  EuclideanSpace ℝ (Fin 1)

/-- The sheet direction of the upper sheet in the rank-three model: a plane. -/
abbrev RankThreeWhitneyModel.Upper :=
  EuclideanSpace ℝ (Fin 2)

/-- The ambient model of the rank-three Whitney situation: the bigon plane times the lower and upper
normal directions. -/
abbrev RankThreeWhitneyModel.Space :=
  (ℝ × ℝ) × (Lower × Upper)

/-- The parameter space of the lower sheet: a time coordinate and the lower sheet direction. -/
abbrev RankThreeWhitneyModel.LowerSheet :=
  ℝ × Lower

/-- The parameter space of the upper sheet: a time coordinate and the upper sheet direction. -/
abbrev RankThreeWhitneyModel.UpperSheet :=
  ℝ × Upper

/-- The lower sheet of the rank-three model: the sheet through the lower boundary arc, spread in the
lower direction. -/
def RankThreeWhitneyModel.firstSheet (p : LowerSheet) : Space :=
  ((p.1, 0), (p.2, 0))

/-- The upper sheet of the rank-three model: the sheet through the parabolic boundary arc, spread in
the upper direction. -/
def RankThreeWhitneyModel.secondSheet (h : ℝ) (p : UpperSheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

/-- The lower sheet is smooth. -/
theorem RankThreeWhitneyModel.contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

/-- The upper sheet is smooth. -/
theorem RankThreeWhitneyModel.contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) :=
  by
  unfold secondSheet
  fun_prop

/-- The derivative of the lower sheet parametrisation. -/
def RankThreeWhitneyModel.firstSheetDerivative : LowerSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Lower).prod 0).prod ((ContinuousLinearMap.snd ℝ ℝ Lower).prod 0)

/-- The derivative of the upper sheet parametrisation at the time `s`, whose vertical component is
the slope `-2 h s` of the parabola. -/
def RankThreeWhitneyModel.secondSheetDerivative (h s : ℝ) : UpperSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Upper).prod
        ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Upper)).prod
    ((0 : UpperSheet →L[ℝ] Lower).prod (ContinuousLinearMap.snd ℝ ℝ Upper))

/-- Value of the derivative of the lower sheet parametrisation. -/
theorem RankThreeWhitneyModel.firstSheetDerivative_apply (p : LowerSheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) :=
  rfl

/-- Value of the derivative of the upper sheet parametrisation. -/
theorem RankThreeWhitneyModel.secondSheetDerivative_apply (h s : ℝ) (p : UpperSheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) :=
  rfl

/-- The lower sheet parametrisation has the stated derivative. -/
theorem RankThreeWhitneyModel.hasFDerivAt_firstSheet (p : LowerSheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

/-- The upper sheet parametrisation has the stated derivative. -/
theorem RankThreeWhitneyModel.hasFDerivAt_secondSheet (h : ℝ) (p : UpperSheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Upper).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Upper).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Lower) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

/-- A linear identification of the lower direction plus a line with the plane. -/
def RankThreeWhitneyModel.lowerSplit : (Lower × ℝ) ≃L[ℝ] WhitneyPairModel.Plane :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp [Lower, WhitneyPairModel.Plane, Module.finrank_prod])

/-- The inclusion of the lower direction into the plane. -/
def RankThreeWhitneyModel.lowerInclude : Lower →L[ℝ] WhitneyPairModel.Plane :=
  lowerSplit.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Lower ℝ)

/-- The projection of the plane onto the lower direction. -/
def RankThreeWhitneyModel.lowerProject : WhitneyPairModel.Plane →L[ℝ] Lower :=
  (ContinuousLinearMap.fst ℝ Lower ℝ).comp lowerSplit.symm.toContinuousLinearMap

/-- The projection is a left inverse of the inclusion of the lower direction. -/
theorem RankThreeWhitneyModel.lowerProject_include (u : Lower) :
    lowerProject (lowerInclude u) = u := by
  change (lowerSplit.symm (lowerSplit (u, 0))).1 = u
  rw [lowerSplit.symm_apply_apply]

/-- The inclusion of the pair of normal directions into the pair of planes of the planar model. -/
def RankThreeWhitneyModel.normalInclude :
    (Lower × Upper) →L[ℝ] (WhitneyPairModel.Plane × WhitneyPairModel.Plane) :=
  lowerInclude.prodMap (ContinuousLinearMap.id ℝ Upper)

/-- The projection of the pair of planes onto the pair of normal directions. -/
def RankThreeWhitneyModel.normalProject :
    (WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (Lower × Upper) :=
  lowerProject.prodMap (ContinuousLinearMap.id ℝ Upper)

/-- The normal projection is a left inverse of the normal inclusion. -/
theorem RankThreeWhitneyModel.normalProject_include :
    Function.LeftInverse normalProject normalInclude := fun z =>
  Prod.ext (lowerProject_include z.1) rfl

/-- The inclusion of the rank-three model into the planar model. -/
def RankThreeWhitneyModel.expand : Space →L[ℝ] WhitneyPairModel.Space :=
  FiberRestriction.embed normalInclude

/-- The projection of the planar model onto the rank-three model. -/
def RankThreeWhitneyModel.collapse : WhitneyPairModel.Space →L[ℝ] Space :=
  FiberRestriction.project normalProject

/-- The projection is a left inverse of the inclusion. -/
theorem RankThreeWhitneyModel.collapse_expand (z : Space) : collapse (expand z) = z :=
  FiberRestriction.project_embed normalInclude normalProject normalProject_include z

/-- The inclusion is the identity on the zero section. -/
theorem RankThreeWhitneyModel.expand_zero (p : ℝ × ℝ) : expand (p, 0) = (p, 0) :=
  Prod.ext rfl normalInclude.map_zero

/-- The projection is the identity on the zero section. -/
theorem RankThreeWhitneyModel.collapse_zero (p : ℝ × ℝ) : collapse (p, 0) = (p, 0) :=
  Prod.ext rfl normalProject.map_zero

/-- The vertical graph of the height function, read in the rank-three model. -/
def RankThreeWhitneyModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

/-- The projection carries the planar vertical graph to the rank-three one. -/
theorem RankThreeWhitneyModel.collapse_verticalGraph (B : ℝ → ℝ) (t s : ℝ) :
    collapse (WhitneyPairModel.verticalGraph B t s) = verticalGraph B t s :=
  collapse_zero _


/-- On the zero section, the rank-three model lower sheet is the lower boundary arc `{y = 0}`. -/
theorem RankThreeWhitneyModel.zero_mem_firstSheet_iff (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

/-- On the zero section, the rank-three model upper sheet is the parabolic boundary arc. -/
theorem RankThreeWhitneyModel.zero_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl


/-- The image in the manifold of the model lower sheet under a chart. -/
def RankThreeWhitneyModel.nativeFirstSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) : Set M :=
  Φ '' (Set.range firstSheet ∩ Φ.source)

/-- The image in the manifold of the model upper sheet under a chart. -/
def RankThreeWhitneyModel.nativeSecondSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) (h : ℝ) : Set M :=
  Φ '' (Set.range (secondSheet h) ∩ Φ.source)


/-- In the rank-three model the two sheets meet exactly at the two corners of the bigon, at the
parameters `±1`. -/
theorem RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff {h : ℝ} (hh : 0 < h)
    (p : LowerSheet) (q : UpperSheet) :
    firstSheet p = secondSheet h q ↔ p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  rcases p with ⟨s, u⟩
  rcases q with ⟨t, v⟩
  constructor
  · intro heq
    have hst : s = t := congrArg (fun z : Space => z.1.1) heq
    have ht : 0 = h * (1 - t ^ 2) := congrArg (fun z : Space => z.1.2) heq
    have hu : u = 0 := congrArg (fun z : Space => z.2.1) heq
    have hv : v = 0 := (congrArg (fun z : Space => z.2.2) heq).symm
    have hsq : t ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp ht.symm).resolve_left hh.ne'
      linarith
    have hprod : (t + 1) * (t - 1) = 0 := by nlinarith
    refine ⟨hst, hu, hv, ?_⟩
    rcases mul_eq_zero.mp hprod with hm | hp
    · left
      linarith
    · right
      linarith
  · rintro ⟨hst, hu, hv, ht⟩
    change s = t at hst
    change u = 0 at hu
    change v = 0 at hv
    subst s
    subst u
    subst v
    rcases ht with ht | ht
    · change t = -1 at ht
      subst t
      simp [firstSheet, secondSheet]
    · change t = 1 at ht
      subst t
      simp [firstSheet, secondSheet]


end
