/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips
import Lib.Geometry.Manifold.Whitney.FrameField.BlockDeterminant
import Lib.Geometry.Manifold.Whitney.FrameField.SheetCoordinates

/-!
# Radial frames and normal Jacobians along an embedded sphere

For a point `x` of the unit sphere and a chart coefficient `C`, the radial frame
`SphereNormalCoordinates.radialFrame` sends `(s, w)` to `s x` plus the image of `w` in the tangent
space at `x`; it is bijective when `C` is (`SphereNormalCoordinates.bijective_radialFrame`). Read
through a chart of the sphere (`SphereNormalCoordinates.chartRadialFrame`) it is smooth and
bijective on the chart source, so along a path inside one chart its endpoint determinants have the
same sign.

Consequently the two endpoint normal Jacobians of an embedded sphere have opposite signs exactly when
the endpoint determinants of the chart coefficients do
(`SphereNormalCoordinates.opposite_normalJacobians_iff_chartDet`), and, for a sphere meeting a sheet
cleanly in a chart, exactly when the endpoint determinants of a defining map of the sheet do
(`SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6 (intersection signs).

## Tags

sphere, normal frame, intersection sign
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- The radial frame of the unit sphere at `x`: the map sending `(s, w)` to `s x` plus the image of
`w` in the tangent space of the sphere at `x`, for a chosen chart coefficient `C`. -/
def SphereNormalCoordinates.radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp C)

/-- Composing the normal frame with an invertible change of chart coefficients gives the radial
frame. -/
theorem SphereNormalCoordinates.normalFrame_comp_normalDerivative {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (normalFrame x A).comp ((ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)) = radialFrame x C := by
  apply ContinuousLinearMap.ext
  intro z
  change
    z.1 • (x : V) + inclusionDerivative x (A.inverse (A (C z.2))) =
      z.1 • (x : V) + inclusionDerivative x (C z.2)
  rw [hA.inverse_apply_self]

/-- The radial frame is bijective when its chart coefficient is invertible: the radial direction and
the tangent space span the ambient space. -/
theorem SphereNormalCoordinates.bijective_radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) (hC : C.IsInvertible) :
    Function.Bijective (radialFrame x C) := by
  have heq : radialFrame x C = normalFrame x C.inverse := by
    apply ContinuousLinearMap.ext
    intro z
    change
      z.1 • (x : V) + inclusionDerivative x (C z.2) =
        z.1 • (x : V) + inclusionDerivative x (C.inverse.inverse z.2)
    rw [hC.inverse_inverse]
  rw [heq]
  exact bijective_normalFrame x C.inverse hC.inverse

/-- The normal Jacobian and the determinant of the chart coefficient multiply to the determinant of
the radial frame read in the coordinates `j`. -/
theorem SphereNormalCoordinates.normalJacobian_mul_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    normalJacobian j x A * (A.comp C).det =
      ((radialFrame x C).comp j.symm.toContinuousLinearMap).det := by
  let R : (ℝ × N) →L[ℝ] (ℝ × N) := (ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (R.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = (A.comp C).det := by
    have hconj : T.det = R.det := LinearMap.det_conj R.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (A.comp C).toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T =
      (radialFrame x C).comp j.symm.toContinuousLinearMap := by
    have h := normalFrame_comp_normalDerivative x A hA C
    ext v
    change normalFrame x A (j.symm (j (R (j.symm v)))) = radialFrame x C (j.symm v)
    rw [j.symm_apply_apply]
    exact congrArg (fun L : (ℝ × N) →L[ℝ] V => L (j.symm v)) h
  calc
    normalJacobian j x A * (A.comp C).det =
        (((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T).det := by
      rw [← hdetT]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := congrArg ContinuousLinearMap.det hfactor

/-- The radial frame at a chart point, assembled from the radial direction `c z` and the derivative
of the chart inverse at `z`. -/
def SphereNormalCoordinates.chartRadialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) (z : N) :
    (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (c z : V)).coprod (fderiv ℝ (fun w => (c w : V)) z)

/-- On the source of the chart, the chart radial frame is the radial frame with chart coefficient
the differential of the chart. -/
theorem SphereNormalCoordinates.chartRadialFrame_eq {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) {z : N}
    (hz : z ∈ c.source) :
    chartRadialFrame c z =
      radialFrame (N := N) (c z) (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  by
  have hchain :
    fderiv ℝ (fun w => (c w : V)) z =
      (inclusionDerivative (c z)).comp
        (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    have h :=
      mfderiv_comp z ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  unfold chartRadialFrame radialFrame
  rw [hchain]
  rfl

/-- The chart radial frame depends smoothly on the chart parameter. -/
theorem SphereNormalCoordinates.contDiffOn_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) :
    ContDiffOn ℝ ∞ (chartRadialFrame c) c.source := by
  have hc : ContDiffOn ℝ ∞ (fun w => (c w : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact
    FrameField.contDiffOn_coprod (contDiffOn_const.smulRight hc)
      (hc.fderiv_of_isOpen c.open_source (m := ∞) (by simp))

/-- The chart radial frame is bijective at every point of the source of the chart. -/
theorem SphereNormalCoordinates.bijective_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    {z : N} (hz : z ∈ c.source) : Function.Bijective (chartRadialFrame c z) := by
  rw [chartRadialFrame_eq c hz]
  let C : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c z
  have hC : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (PartialChart.bijective_mfderiv c hz)).toContinuousLinearEquiv,
      rfl⟩
  exact bijective_radialFrame (c z) C hC

/-- Along a continuous path inside a chart, the determinants of the chart radial frame at the two
endpoints have the same sign, so their product is positive. -/
theorem SphereNormalCoordinates.chartRadialFrame_det_mul_endpoints_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source) :
    0 <
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det *
        ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
  have hF := (contDiffOn_chartRadialFrame c).continuousOn.comp ha haS
  exact
    FrameField.det_mul_endpoints_pos (hF.clm_comp continuousOn_const)
      (fun t ht => (bijective_chartRadialFrame c (haS ht)).comp j.symm.bijective)

/-- For a path inside one chart, the two endpoint normal Jacobians have opposite signs exactly when
the two endpoint determinants of the chart coefficients do: the chart radial frame contributes a
factor of constant sign. -/
theorem SphereNormalCoordinates.opposite_normalJacobians_iff_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B < 0 ↔
      (A.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det *
          (B.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det <
        0 := by
  let C₀ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0)
  let C₁ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1)
  have h₀ :
    normalJacobian j (c (a 0)) A * (A.comp C₀).det =
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 0)) A hA C₀
  have h₁ :
    normalJacobian j (c (a 1)) B * (B.comp C₁).det =
      ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 1)) B hB C₁
  have hp :
    0 <
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
        ((A.comp C₀).det * (B.comp C₁).det) := by
    have heq :
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
          ((A.comp C₀).det * (B.comp C₁).det) =
        (normalJacobian j (c (a 0)) A * (A.comp C₀).det) *
          (normalJacobian j (c (a 1)) B * (B.comp C₁).det) := by ring
    rw [heq, h₀, h₁]
    exact chartRadialFrame_det_mul_endpoints_pos c j a ha haS
  change _ ↔ (A.comp C₀).det * (B.comp C₁).det < 0
  rcases mul_pos_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact iff_of_false (not_lt_of_gt hp) (not_lt_of_gt hq)
  · exact iff_of_true hp hq

/-- For an embedded sphere meeting a sheet cleanly in a chart, the two endpoint normal Jacobians of
the sphere have opposite signs exactly when the two endpoint determinants of a defining map of
the sheet, read along the centre line of the chart, do. -/
theorem SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet
    {V A B E M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) 𝓘(ℝ, E) ((ℝ × A) × B) M ∞)
    (F : Metric.sphere (0 : V) 1 → M) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ F)
    (hinjF : Function.Injective F) (hiF : ∀ x, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) F x))
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hline : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t, (0 : A)), (0 : B)) ∈ Φ.source)
    (hdim : Module.finrank ℝ (ℝ × A) = n) (q : M → (ℝ × A)) (r : (ℝ × (ℝ × A)) ≃L[ℝ] V)
    (x₀ x₁ : Metric.sphere (0 : V) 1) (hx₀ : F x₀ = Φ ((0, 0), 0)) (hx₁ : F x₁ = Φ ((1, 0), 0))
    (hq₀ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₀))
    (hq₁ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₁))
    (hi₀ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀).IsInvertible)
    (hi₁ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁).IsInvertible) :
    normalJacobian r x₀ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀) *
          normalJacobian r x₁ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁) <
        0 ↔
      (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0)).det <
        0 := by
  let _ : Nonempty (Metric.sphere (0 : V) 1) := ⟨x₀⟩
  obtain ⟨c, hcS, _, hFc, _⟩ :=
    NativeSheetCoordinates.exists_induced_sheet_chart Φ F hF hinjF hclean
      (by simpa only [finrank_euclideanSpace_fin] using hdim.symm) hiF
  let a : ℝ → (ℝ × A) := fun t => (t, 0)
  have ha : ContinuousOn a (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source := by
    intro t ht
    rw [hcS]
    exact hline t ht
  have h₀ : c (a 0) = x₀ := hinjF ((hFc _ (haS (by simp))).trans hx₀.symm)
  have h₁ : c (a 1) = x₁ := hinjF ((hFc _ (haS (by simp))).trans hx₁.symm)
  let A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀
  let A₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁
  have hsign := opposite_normalJacobians_iff_chartDet c r a ha haS A₀ A₁ hi₀ hi₁
  have hcoeff (t : ℝ) (x : Metric.sphere (0 : V) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : c (a t) = x) (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x)) :
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)).comp
        (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (t, 0) := by
    have hqF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ × A) ∞ (q ∘ F) (c (a t)) := by
      rw [hx]
      exact hq.comp x hF.contMDiffAt
    have hchain :=
      mfderiv_comp (a t) (hqF.mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) (haS ht))
    have heq : ((q ∘ F) ∘ c) =ᶠ[𝓝 (a t)] (fun w => q (Φ (w, 0))) := by
      filter_upwards [c.open_source.mem_nhds (haS ht)] with w hw
      exact congrArg q (hFc w hw)
    have hpoint :
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) (c (a t)) : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)) =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x := by rw [hx]
    rw [mfderiv_eq_fderiv] at hchain
    have h := hchain.symm.trans heq.fderiv_eq
    exact
      (congrArg
            (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) =>
              L.comp (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)))
            hpoint).symm.trans
        h
  rw [h₀, h₁] at hsign
  let C₀ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 0)
  let C₁ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 1)
  have hc₀ : A₀.comp C₀ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0) :=
    hcoeff 0 x₀ (by simp) h₀ hq₀
  have hc₁ : A₁.comp C₁ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0) :=
    hcoeff 1 x₁ (by simp) h₁ hq₁
  change
    normalJacobian r x₀ A₀ * normalJacobian r x₁ A₁ < 0 ↔
      (A₀.comp C₀).det * (A₁.comp C₁).det < 0 at hsign
  rw [hc₀, hc₁] at hsign
  exact hsign

end
