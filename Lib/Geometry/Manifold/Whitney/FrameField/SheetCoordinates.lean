/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Charts induced on a sheet by a clean ambient chart

For a chart `Φ` of the ambient manifold in which the image of an injective immersion `F` is the zero
set of the second coordinate (a clean chart), the sheet projection
`NativeSheetCoordinates.projection` (the first component of `Φ⁻¹ ∘ F`) is smooth with injective
differential where `dF` is injective, is a local diffeomorphism when the source and the sheet
directions have the same dimension, and induces a chart of the source
(`NativeSheetCoordinates.exists_induced_sheet_chart`): a partial diffeomorphism onto the slice
`{u | (u, 0) ∈ Φ.source}` carried by `F` to `u ↦ Φ (u, 0)`.

This is the slice-chart description of an embedded submanifold, cf. Lee, *Introduction to Smooth
Manifolds*, Thm 5.8 (slice charts) for the statement in the textbook setting.

## Tags

slice chart, immersion, submanifold
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The sheet coordinate of a point: the first component of its image under the inverse of a chart
in which the sheet is the zero set of the second coordinate. -/
def NativeSheetCoordinates.projection {D B E M N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) (x : N) : D :=
  (Φ.symm (F x)).1

/-- The sheet projection is smooth on the preimage of the chart target. -/
theorem NativeSheetCoordinates.contMDiffOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) : ContMDiffOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hcoord : ContMDiffOn I 𝓘(ℝ, D × B) ∞ (Φ.symm ∘ F) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoord

/-- Where the chart is clean for the image of `F` (the image meets the chart exactly in the zero set
of the second coordinate), the differential of the sheet projection is injective wherever that
of `F` is. -/
theorem NativeSheetCoordinates.injective_mfderiv_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) (hiF : Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, D) (projection Φ F) x) := by
  let C : N → (D × B) := Φ.symm ∘ F
  let T : G →L[ℝ] (D × B) := mfderiv I 𝓘(ℝ, D × B) C x
  have hC : ContMDiffAt I 𝓘(ℝ, D × B) ∞ C x :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hTi : Function.Injective T := by
    change Function.Injective (mfderiv I 𝓘(ℝ, D × B) (Φ.symm ∘ F) x)
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx) (hF.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ.symm hx).injective.comp hiF
  have hfst :
    (mfderiv I 𝓘(ℝ, D) (projection Φ F) x : G →L[ℝ] D) = (ContinuousLinearMap.fst ℝ D B).comp T :=
    by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) := contDiff_fst.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (C x) = ContinuousLinearMap.fst ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.fst ℝ D B).fderiv
    change mfderiv I 𝓘(ℝ, D) (Prod.fst ∘ C) x = _
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)), hd]
    rfl
  have hzero : (Prod.snd ∘ C) =ᶠ[𝓝 x] (fun _ => (0 : B)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with
      y hy
    exact (hclean _ (Φ.map_target' hy)).mp ⟨y, (Φ.right_inv' hy).symm⟩
  have hsnd : (ContinuousLinearMap.snd ℝ D B).comp T = 0 := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (C x) = ContinuousLinearMap.snd ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.snd ℝ D B).fderiv
    have hz : (mfderiv I 𝓘(ℝ, B) (Prod.snd ∘ C) x : G →L[ℝ] B) = 0 := by
      rw [hzero.mfderiv_eq, mfderiv_const]
      rfl
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)),
      hd] at hz
    exact hz
  intro u v huv
  apply hTi
  apply Prod.ext
  · exact
      (congrArg (fun L : G →L[ℝ] D => L u) hfst).symm.trans
        (huv.trans (congrArg (fun L : G →L[ℝ] D => L v) hfst))
  · have hz (w : G) : (T w).2 = 0 := congrArg (fun L : G →L[ℝ] B => L w) hsnd
    rw [hz u, hz v]

/-- Under the same cleanness hypothesis, and when source and sheet directions have the same
dimension, the sheet projection is a local diffeomorphism on the preimage of the chart target. -/
theorem NativeSheetCoordinates.isLocalDiffeomorphOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ G] [I.Boundaryless] [IsManifold I ∞ N] (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    IsLocalDiffeomorphOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hU : IsOpen (F ⁻¹' Φ.target) := Φ.open_target.preimage hF.continuous
  intro x
  let A : G →L[ℝ] D := mfderiv I 𝓘(ℝ, D) (projection Φ F) x.1
  have hi : Function.Injective A := injective_mfderiv_projection Φ F hF hclean x.2 (hiF x.1)
  have hb : Function.Bijective A :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hA : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact isLocalDiffeomorphAt_boundaryless hU x.2 (contMDiffOn_projection Φ F hF) hA

/-- A clean chart for an injective immersion `F` induces a chart of the source: a partial
diffeomorphism onto the slice `{u | (u, 0) ∈ Φ.source}` whose inverse is the sheet projection
and which is carried by `F` to `u ↦ Φ (u, 0)`. -/
theorem NativeSheetCoordinates.exists_induced_sheet_chart {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [Nonempty N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hinjF : Function.Injective F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, D) I D N ∞,
      c.source = {u | (u, (0 : B)) ∈ Φ.source} ∧
        c.target = F ⁻¹' Φ.target ∧
          (∀ u ∈ c.source, F (c u) = Φ (u, 0)) ∧ ∀ x, c.symm x = projection Φ F x := by
  let U := F ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hF.continuous
  have hzero (x : N) (hx : x ∈ U) : (Φ.symm (F x)).2 = 0 :=
    (hclean _ (Φ.map_target' hx)).mp ⟨x, (Φ.right_inv' hx).symm⟩
  have hinj : Set.InjOn (projection Φ F) U := by
    intro x hx y hy heq
    have hc : Φ.symm (F x) = Φ.symm (F y) := Prod.ext heq ((hzero x hx).trans (hzero y hy).symm)
    apply hinjF
    exact (Φ.right_inv' hx).symm.trans ((congrArg Φ hc).trans (Φ.right_inv' hy))
  let p :=
    partialDiffeomorphOfInjectiveLocal hU hinj
      (isLocalDiffeomorphOn_projection Φ F hF hclean hdim hiF)
  have htarget : p.target = {u | (u, (0 : B)) ∈ Φ.source} := by
    change projection Φ F '' U = _
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have heq : (projection Φ F x, (0 : B)) = Φ.symm (F x) := Prod.ext rfl (hzero x hx).symm
      change (projection Φ F x, (0 : B)) ∈ Φ.source
      rw [heq]
      exact Φ.map_target' hx
    · intro hu
      obtain ⟨x, hx⟩ := (hclean (u, 0) hu).mpr rfl
      have hxU : x ∈ U := by
        change F x ∈ Φ.target
        rw [hx]
        exact Φ.map_source' hu
      refine ⟨x, hxU, ?_⟩
      change (Φ.symm (F x)).1 = u
      rw [hx]
      exact congrArg Prod.fst (Φ.left_inv' hu)
  refine ⟨p.symm, htarget, rfl, ?_, fun _ => rfl⟩
  intro u hu
  have hx : p.symm u ∈ U := p.map_target' hu
  have hp : projection Φ F (p.symm u) = u := p.right_inv' hu
  have heq : Φ.symm (F (p.symm u)) = (u, (0 : B)) := Prod.ext hp (hzero (p.symm u) hx)
  exact (Φ.right_inv' hx).symm.trans (congrArg Φ heq)

end
