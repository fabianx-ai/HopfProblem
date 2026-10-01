/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips

/-!
# The normal derivative at a transverse intersection

At a transverse intersection of two sheets of complementary dimensions, the differential of the
normal coordinate of the first sheet restricted to the second is bijective
(`TransverseCoordinates.bijective_normalDerivative_transverse_sheet`, and its version for a
parametrised second sheet). At a clean corner whose vertical axis is a transverse parametrised arc,
the vertical derivative of the normal coordinate is nonzero at the corner and nearby
(`TransverseCoordinates.corner_normalDerivative_ne_zero`), computed from the axis germ
(`TransverseCoordinates.vertical_derivative_of_axis_germ`); `NativeParametrization.line u` is the
line `t ↦ t • u`.

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

transversality, normal derivative
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- At a transverse intersection, the differential of the normal coordinate of the sheet restricted
to the second sheet is bijective when the two sheets have complementary dimensions. -/
theorem TransverseCoordinates.bijective_normalDerivative_transverse_sheet
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N} {y : P} (hx : F x ∈ Φ.target)
    (hxy : G y = F x)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y) := by
  let Q : E →L[ℝ] B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)
  let DF : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x
  let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y
  have hQ : Function.Surjective Q := surjective_mfderiv_normalCoordinate Φ hx
  have hQA : Q.comp DF = 0 := normalDerivative_comp_sheet_eq_zero Φ hF hclean hx
  have hb : Function.Bijective (Q.comp DG) := bijective_normal_comp Q DF DG hQ ht hQA hdim
  have hy : G y ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hderiv : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y = Q.comp DG := by
    rw [mfderiv_comp y (hnormal.mdifferentiableAt (by simp)) (hG.mdifferentiableAt (by simp)),
      hxy]
    rfl
  rw [hderiv]
  exact hb

/-- Version of the previous statement for the second sheet read through a parametrisation. -/
theorem TransverseCoordinates.bijective_normalDerivative_transverse_parametrization
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {Z' : Type*} [NormedAddCommGroup Z']
    [NormedSpace ℝ Z'] {F : N → M} {G : P → M} (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) {z : Z'} (hz : z ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c z) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c z))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (fderiv ℝ ((normalCoordinate Φ ∘ G) ∘ c) z) := by
  have hb := bijective_normalDerivative_transverse_sheet Φ hF hG hclean hx hxy ht hdim
  have hy : G (c z) ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, B) ∞ (normalCoordinate Φ ∘ G) (c z) :=
    hnormal.comp (c z) hG.contMDiffAt
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp z (hg.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hz)]
  exact hb.comp (PartialChart.bijective_mfderiv c hz)

/-- The line through `u`: the linear map `t ↦ t • u`. -/
def NativeParametrization.line {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (u : D) : ℝ →L[ℝ] D :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight u

/-- The line through `u` takes the value `t • u` at `t`. -/
theorem NativeParametrization.line_apply {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (u : D) (t : ℝ) : line u t = t • u :=
  rfl

/-- If a two-parameter map agrees near the origin along the vertical axis with a curve in the
direction `v`, then its vertical derivative at the origin is the derivative of that curve in the
direction `v`. -/
theorem TransverseCoordinates.vertical_derivative_of_axis_germ {Z B : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {H : (ℝ × ℝ) → B} {a : Z → B} (v : Z) (hH : DifferentiableAt ℝ H 0)
    (ha : DifferentiableAt ℝ a 0) (heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v))) :
    fderiv ℝ H (0, 0) (0, 1) = fderiv ℝ a 0 v := by
  let S : ℝ →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.inr ℝ ℝ ℝ
  let L : ℝ →L[ℝ] Z := NativeParametrization.line v
  have hHS : fderiv ℝ (H ∘ S) 0 = (fderiv ℝ H 0).comp S := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using hH) S.differentiableAt, map_zero, S.fderiv]
  have haL : fderiv ℝ (a ∘ L) 0 = (fderiv ℝ a 0).comp L := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using ha) L.differentiableAt, map_zero, L.fderiv]
  have heq' : (H ∘ S) =ᶠ[𝓝 (0 : ℝ)] (a ∘ L) := heq
  have hd : fderiv ℝ (H ∘ S) 0 = fderiv ℝ (a ∘ L) 0 := heq'.fderiv_eq
  rw [hHS, haL] at hd
  have hval := congrArg (fun T : ℝ →L[ℝ] B => T 1) hd
  change fderiv ℝ H (0 : ℝ × ℝ) (0, 1) = fderiv ℝ a 0 v
  simpa only [ContinuousLinearMap.comp_apply, S, L, NativeParametrization.line_apply,
    one_smul, ContinuousLinearMap.inr_apply] using hval

/-- A nonvanishing vertical derivative at a point persists on a neighbourhood. -/
theorem TransverseCoordinates.eventually_vertical_derivative_ne_zero {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} {p : ℝ × ℝ}
    (hH : ContDiffAt ℝ ∞ H p) (hn : fderiv ℝ H p (0, 1) ≠ 0) :
    ∀ᶠ q in 𝓝 p, fderiv ℝ H q (0, 1) ≠ 0 := by
  have hd : ContinuousAt (fderiv ℝ H) p := hH.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun q => fderiv ℝ H q (0, 1)) p := hd.clm_apply continuousAt_const
  exact hv.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hn)

/-- At a clean corner whose vertical axis is a transverse parametrised arc, the vertical derivative
of the normal coordinate of the sheet is nonzero at the corner and stays nonzero nearby. -/
theorem TransverseCoordinates.corner_normalDerivative_ne_zero {D B E M A Z Z' N P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
    [TopologicalSpace N] [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) (hc : (0 : Z') ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c 0) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c 0))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W) (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W) {v : Z'}
    (hv : v ≠ 0) (haxis : ∀ t, (0, t) ∈ W → k (0, t) = G (c (t • v))) :
    fderiv ℝ (normalCoordinate Φ ∘ k) (0, 0) (0, 1) ≠ 0 ∧
      ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), fderiv ℝ (normalCoordinate Φ ∘ k) q (0, 1) ≠ 0 := by
  let H := normalCoordinate Φ ∘ k
  let a := (normalCoordinate Φ ∘ G) ∘ c
  have hk0 : k (0 : ℝ × ℝ) = F x := by
    have h := haxis 0 h0W
    rw [zero_smul] at h
    exact h.trans hxy
  have hkΦ : k (0 : ℝ × ℝ) ∈ Φ.target := hk0.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hkΦ)
  have hH : ContDiffAt ℝ ∞ H 0 := (hnormal.comp 0 (hk.contMDiffAt (hW.mem_nhds h0W))).contDiffAt
  have hy : G (c 0) ∈ Φ.target := hxy.symm ▸ hx
  have hnormalG := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have ha : ContDiffAt ℝ ∞ a 0 :=
    ((hnormalG.comp (c 0) hG.contMDiffAt).comp 0
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc))).contDiffAt
  have haxisW : ∀ᶠ t : ℝ in 𝓝 0, (0, t) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds h0W)
  have heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v)) := by
    filter_upwards [haxisW] with t htW
    exact congrArg (normalCoordinate Φ) (haxis t htW)
  have hderiv :=
    vertical_derivative_of_axis_germ v (hH.differentiableAt (by simp))
      (ha.differentiableAt (by simp)) heq
  have hbij : Function.Bijective (fderiv ℝ a 0) :=
    bijective_normalDerivative_transverse_parametrization Φ hF hG hclean c hc hx hxy ht hdim
  have hn : fderiv ℝ H (0, 0) (0, 1) ≠ 0 := by
    rw [hderiv]
    intro hz
    exact hv (hbij.1 (hz.trans (map_zero (fderiv ℝ a 0)).symm))
  exact ⟨hn, eventually_vertical_derivative_ne_zero hH hn⟩

end
