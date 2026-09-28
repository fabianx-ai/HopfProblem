/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.SpherePointTransport
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Whitney.CleanStrips
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover

/-!
# Orientation of the point connecting map on a sphere

The connecting homomorphism `H_{k+2}(Sⁿ⁺¹) → H_{k+1}(Sⁿ)` at a point `x` of the sphere
(`Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting`) depends on the chart at
`x` only through a sign, the sign of the *chart Jacobian*
`SphereNormalCoordinates.chartJacobian` (the determinant of the radial frame of the chart against
a fixed splitting `ℝ × F ≃ V`).  Transporting `x` to `y` by a rotation of determinant `1`
transports the Jacobian sign (`SpherePoint.chartJacobian_transport_sign`), so the sign-corrected
map `SpherePoint.outwardPointClass` is independent of the point and the chart
(`outwardPointClass_eq`, `outwardPointClass_eq_global`) and defines a canonical isomorphism
`SpherePoint.outwardClassEquiv : H_{k+2}(Sⁿ⁺²) ≃ H_{k+1}(Sⁿ⁺¹)`.  The *count marks*
(`sourceCountMark`, `overlapCountMark`, `targetCountMark`) identify the top homology groups of
the sphere, of `S(N)` and of `OnePoint N` with `ℤ` compatibly with the connecting maps
(`countMark_of_connecting`).  Cf. Hatcher, *Algebraic Topology*, §2.2 (local degree and
orientation).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- `normalJacobian j x (c • A) * c ^ dim N = normalJacobian j x A` for invertible `A` and `c ≠ 0`.
`normalJacobian j x (c • A) * c ^ dim N = normalJacobian j x A` for invertible `A` and `c ≠ 0`. -/
theorem SphereNormalCoordinates.normalJacobian_smul_mul_pow {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) :
    normalJacobian j x (c • A) * c ^ Module.finrank ℝ N = normalJacobian j x A := by
  have hB := normalDerivative_smul_isInvertible A hA c hc
  have hcomp : A.comp A.inverse = ContinuousLinearMap.id ℝ N := by
    ext y
    exact hA.self_apply_inverse y
  have hdet : ((c • A).comp A.inverse).det = c ^ Module.finrank ℝ N := by
    rw [ContinuousLinearMap.smul_comp, hcomp]
    change (c • (LinearMap.id : N →ₗ[ℝ] N)).det = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hid : (A.comp A.inverse).det = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  have h :=
    (normalJacobian_mul_chartDet j x (c • A) hB A.inverse).trans
      (normalJacobian_mul_chartDet j x A hA A.inverse).symm
  simpa only [hdet, hid, mul_one] using h

/-- Scaling an invertible `A` by `c > 0` does not change the sign of `normalJacobian j x A`. -/
theorem SphereNormalCoordinates.sign_normalJacobian_smul_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : 0 < c) :
    SignType.sign (normalJacobian j x (c • A)) = SignType.sign (normalJacobian j x A) := by
  have h := congrArg SignType.sign (normalJacobian_smul_mul_pow j x A hA c hc.ne')
  have hp : SignType.sign (c ^ Module.finrank ℝ N) = 1 := sign_eq_one_iff.mpr (pow_pos hc _)
  simpa only [sign_mul, hp, mul_one] using h

/-- For a linear isometry `R` with `R x = y`, the radial frame of the centred chart at `y`
composed with `id × (linear chart transition)` is `R` composed with the radial frame at `x`. -/
theorem SpherePoint.chart_radial_frame_comp {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
            0).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toContinuousLinearMap) =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
          0) := by
  apply ContinuousLinearMap.ext
  intro z
  have hD :=
    congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] V => A z.2)
      (chart_transition_ambient_derivative x y R he)
  have hcenter :
    R (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) =
      (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) := by
    rw [NativeParametrization.centered_zero, NativeParametrization.centered_zero]
    exact congrArg Subtype.val he
  change
    z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) +
        (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0)
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he z.2) =
      R
        (z.1 • (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) +
          (fderiv ℝ (fun u => (NativeParametrization.centered x u : V)) 0) z.2)
  rw [map_add, map_smul, hcenter]
  exact
    congrArg
      (fun v : V =>
        z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) + v)
      hD

/-- The chart Jacobian of a chart `c` of the sphere `S(V)` at `z`: the determinant of the radial
frame of `c` at `z` against the splitting `ℝ × F ≃ V` given by `j` and `B : ℝᵐ ≃ F`. -/
def SphereNormalCoordinates.chartJacobian {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) (z : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  ((chartRadialFrame c z).comp j'.symm.toContinuousLinearMap).det

/-- The chart Jacobian is nonzero on the source of the chart. -/
theorem SphereNormalCoordinates.chartJacobian_ne_zero {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) : chartJacobian c j B z ≠ 0 :=
  (RegularValues.bijective_iff_det_ne_zero _).mp
    ((bijective_chartRadialFrame c hz).comp
      ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans
          j).symm.bijective)

/-- For `f : S(V) → F` with invertible differential at `c z`:
`normalJacobian j (c z) (mfderiv f (c z)) * det (B⁻¹ ∘ fderiv (f ∘ c) z) = chartJacobian c j B z`. -/
theorem SphereNormalCoordinates.chartJacobian_factor {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)) *
        (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      chartJacobian c j B z := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] F := mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)
  let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) c z
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  have hd : fderiv ℝ (f ∘ c) z = A.comp C := by
    have h := mfderiv_comp z hf (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hB : (B.symm.toContinuousLinearMap.comp A).IsInvertible :=
    (show B.symm.toContinuousLinearMap.IsInvertible from ⟨B.symm, rfl⟩).comp hA
  have h := normalJacobian_mul_chartDet j' (c z) (B.symm.toContinuousLinearMap.comp A) hB C
  rw [normalJacobian_change_normal_model j B (c z) A hA] at h
  change normalJacobian j (c z) A * _ = _
  rw [hd]
  rw [← ContinuousLinearMap.comp_assoc]
  apply h.trans
  unfold chartJacobian
  rw [chartRadialFrame_eq c hz]

/-- Sign form of `chartJacobian_factor`: `sign (chartJacobian c j B z) * sign det (B⁻¹ ∘ fderiv (f ∘ c) z)`
is the sign of the normal Jacobian of `f` at `c z`. -/
theorem SphereNormalCoordinates.chartJacobian_sign_factor {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    SignType.sign (chartJacobian c j B z) *
        SignType.sign (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      SignType.sign (normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z))) := by
  have h := chartJacobian_factor c j B hz f hf hA
  apply sign_factor _ h
  intro hd
  rw [hd, MulZeroClass.mul_zero] at h
  exact chartJacobian_ne_zero c j B hz h.symm

/-- For a linear isometry `R` with `R x = y`: `det (frame_y ∘ j⁻¹) * det (transition x y R)`
equals `det R * det (frame_x ∘ j⁻¹)`. -/
theorem SpherePoint.chart_radial_frame_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)
    (j : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] V) :
    ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).det *
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
                0).comp
            j.symm.toContinuousLinearMap).det := by
  let L := NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he
  let Q := (ContinuousLinearMap.id ℝ ℝ).prodMap L.toContinuousLinearMap
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (Q.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = L.toLinearEquiv.toLinearMap.det := by
    have hconj : T.det = Q.det := LinearMap.det_conj Q.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) L.toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).comp
        T =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
              0).comp
          j.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change
      SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y) 0
          (j.symm (j (Q (j.symm v)))) =
        R
          (SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered x)
            0 (j.symm v))
    rw [j.symm_apply_apply]
    exact
      congrArg (fun A : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] V => A (j.symm v))
        (chart_radial_frame_comp x y R he)
  calc
    _ =
        (((SphereNormalCoordinates.chartRadialFrame (NativeParametrization.centered y)
                    0).comp
                j.symm.toContinuousLinearMap).comp
            T).det := by
      rw [hdetT.symm]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := (congrArg ContinuousLinearMap.det hfactor).trans (LinearMap.det_comp _ _)

/-- `chartJacobian (centered y) j B 0 * det (transition x y R) = det R * chartJacobian (centered x) j B 0`
for a linear isometry `R` with `R x = y`. -/
theorem SpherePoint.chartJacobian_transport {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (ℝ × F) ≃L[ℝ] V)
    (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j B 0 *
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0 :=
  chart_radial_frame_det x y R he
    ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j)

/-- If `det R = 1`, the sign of the chart Jacobian at `y` times the sign of the chart transition
determinant is the sign of the chart Jacobian at `x`. -/
theorem SpherePoint.chartJacobian_transport_sign {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hR : R.toLinearEquiv.toLinearMap.det = 1)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j
            B 0) *
        SignType.sign
          (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) := by
  have h := chartJacobian_transport x y R he j B
  rw [hR, one_mul] at h
  rw [← sign_mul, h]

/-- `Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1)`, used as a local instance. -/
theorem SpherePoint.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] SpherePoint.instLocal1 in
/-- The diffeomorphism of `Sⁿ⁺²` moving `x` to `y`, induced by the positive transport rotation. -/
def SpherePoint.pointDiffeomorph (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2))
      (SphereHomology.UnitSphere (n + 2)) ∞ :=
  sphereDiffeomorph (positiveTransport (n + 1) x y)

attribute [local instance] SpherePoint.instLocal1 in
/-- `pointDiffeomorph n x y x = y`. -/
theorem SpherePoint.pointDiffeomorph_apply (n : ℕ)
    (x y : SphereHomology.UnitSphere (n + 2)) : pointDiffeomorph n x y x = y :=
  positiveTransport_moves (n + 1) x y

attribute [local instance] SpherePoint.instLocal1 in
/-- The linear chart transition `ℝⁿ⁺² ≃L ℝⁿ⁺²` of `pointDiffeomorph n x y` at `x`. -/
def SpherePoint.pointChartLinear (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  NativeChartTransition.linear x y (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y)

attribute [local instance] SpherePoint.instLocal1 in
/-- The point connecting maps at `x` and `y` on `H_{k+2}(Sⁿ⁺²)` differ by the sign of the
determinant of `pointChartLinear n x y`. -/
theorem SpherePoint.pointClass_sign_compare (n : ℕ) {F G : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (x y : SphereHomology.UnitSphere (n + 2)) {fx : SphereHomology.UnitSphere (n + 2) → F}
    {fy : SphereHomology.UnitSphere (n + 2) → G} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
        ((NativeParametrization.centered y).source ∩
          NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      (SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det : ℤ) •
        LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a := by
  have h :=
    LocalDegree.pointConnecting_diffeomorph x y dx dy (pointDiffeomorph n x y)
      (pointDiffeomorph_apply n x y) (k + 1) a
  have hid :
    SingularMayerVietoris.singularHomologyMap
        (pointDiffeomorph n x y).toHomeomorph.toHomotopyEquiv.toFun (k + 2) a =
      a :=
    positiveTransport_homology (n + 1) x y (k + 2) a
  rw [hid] at h
  apply h.trans
  exact LinearSphereAction.homology_eq_sign_smul n (pointChartLinear n x y) k _

/-- Stereographic projection: the complement of a point `x` of the unit sphere of `V`,
`dim V = n + 1`, is homeomorphic to `EuclideanSpace ℝ (Fin n)`. -/
def SpherePoint.punctureHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1) :
    ↥({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    ((stereographic' n x).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target x)).trans (Homeomorph.Set.univ _)))

/-- The complement of a point in the unit sphere of `V`, `dim V = n + 1`, is contractible. -/
theorem SpherePoint.puncture_contractible {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
  (punctureHomeomorph (n := n) x).contractibleSpace

/-- The point connecting isomorphism `H_{k+2}(S(V)) ≃ H_{k+1}(S(ℝⁿ))` at `x ∈ S(V)`, `dim V = n + 1`.
The point connecting isomorphism `H_{k+2}(S(V)) ≃ H_{k+1}(S(ℝⁿ))` at `x ∈ S(V)`, `dim V = n + 1`. -/
def SpherePoint.connectingHomologyEquiv {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : Metric.sphere (0 : V) 1)
    {f : Metric.sphere (0 : V) 1 → F} {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F}
    {W : Set (Metric.sphere (0 : V) 1)}
    (d :
      LocalDegree.NeighborhoodData
        (f ∘ NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x) L
        ((NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x).source ∩
          NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x ⁻¹' W))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : V) 1) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
        (k + 1) := by
  let : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
    puncture_contractible (n := n) x
  exact LocalDegree.NativeNeighborhood.sphereHomologyEquiv x d k

attribute [local instance] SpherePoint.instLocal2 in
/-- The point connecting map at `x` corrected by the sign of the chart Jacobian of the centred
chart at `x`: `sign (chartJacobian (centered x) j B 0) • sphereConnecting x dx (k + 1)`. -/
def SpherePoint.outwardPointClass (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  (SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) :
      ℤ) •
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1)

attribute [local instance] SpherePoint.instLocal2 in
/-- `outwardPointClass` does not depend on the point nor on the neighbourhood datum. -/
theorem SpherePoint.outwardPointClass_eq (n : ℕ) {F G H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x y : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {fy : SphereHomology.UnitSphere (n + 2) → G}
    {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
        ((NativeParametrization.centered y).source ∩
          NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ) : outwardPointClass n j B y dy k = outwardPointClass n j B x dx k := by
  have hs :=
    chartJacobian_transport_sign x y (positiveTransport (n + 1) x y)
      (positiveTransport_moves (n + 1) x y) (positiveTransport_det (n + 1) x y) j B
  have hs' :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y) j
            B 0) *
        SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B
          0) :=
    hs
  apply LinearMap.ext
  intro a
  change
    (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered y)
              j B 0) :
          ℤ) •
        LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      _
  rw [pointClass_sign_compare n x y dx dy k a, smul_smul, ← SignType.coe_mul, hs']
  rfl

attribute [local instance] SpherePoint.instLocal2 in
/-- The sign of the chart Jacobian squares to `1` (it is nonzero). -/
theorem SpherePoint.chartSign_mul_self (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2)) :
    (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) *
        (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) =
      1 := by
  have hn :=
    SphereNormalCoordinates.chartJacobian_ne_zero (NativeParametrization.centered x) j
      B (NativeParametrization.zero_mem_centered_source x)
  have hs :
    SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j
            B 0) *
        SignType.sign
          (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j
            B 0) =
      1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hn)
  simpa only [SignType.coe_mul, SignType.coe_one] using congrArg (fun s : SignType => (s : ℤ)) hs

attribute [local instance] SpherePoint.instLocal2 in
/-- `sphereConnecting x dx (k + 1) a = sign (chartJacobian …) • outwardPointClass n j B x dx k a`.
`sphereConnecting x dx (k + 1) a = sign (chartJacobian …) • outwardPointClass n j B x dx k a`. -/
theorem SpherePoint.connecting_eq_sign_outward (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardPointClass n j B x dx k a := by
  change
    _ =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        ((SignType.sign
              (SphereNormalCoordinates.chartJacobian
                (NativeParametrization.centered x) j B 0) :
            ℤ) •
          LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a)
  rw [smul_smul, chartSign_mul_self n j B x, one_smul]

attribute [local instance] SpherePoint.instLocal2 in
/-- `outwardPointClass n j B x dx k` as a linear isomorphism
`H_{k+2}(Sⁿ⁺²) ≃ H_{k+1}(Sⁿ⁺¹)`. -/
def SpherePoint.outwardPointClassEquiv (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) := by
  let C := connectingHomologyEquiv x dx k
  let s : ℤ :=
    SignType.sign
      (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x) j B 0)
  have hs : s * s = 1 := chartSign_mul_self n j B x
  refine LinearEquiv.ofBijective (outwardPointClass n j B x dx k) ⟨?_, ?_⟩
  · intro a b hab
    apply C.injective
    have h := congrArg (fun z => s • z) hab
    change s • (s • C a) = s • (s • C b) at h
    simpa only [smul_smul, hs, one_smul] using h
  · intro b
    refine ⟨C.symm (s • b), ?_⟩
    change s • C (C.symm (s • b)) = b
    rw [C.apply_symm_apply, smul_smul, hs, one_smul]

attribute [local instance] SpherePoint.instLocal3 in
/-- The canonical connecting map `H_{k+2}(Sⁿ⁺²) → H_{k+1}(Sⁿ⁺¹)`: `outwardPointClass` at the
reference point with its reference neighbourhood. -/
def SpherePoint.outwardClass (n : ℕ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClass n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] SpherePoint.instLocal3 in
/-- `outwardClass n j B k` as a linear isomorphism. -/
def SpherePoint.outwardClassEquiv (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClassEquiv n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] SpherePoint.instLocal3 in
/-- `outwardPointClass n j B x d k = outwardClass n j B k` for every point `x` and datum `d`. -/
theorem SpherePoint.outwardPointClass_eq_global (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered x) L
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' W))
    (k : ℕ) : outwardPointClass n j B x d k = outwardClass n j B k :=
  outwardPointClass_eq n j B (referencePoint n) x (referenceNeighborhood n (referencePoint n)) d k

attribute [local instance] SpherePoint.instLocal3 in
/-- `sphereConnecting x d (k + 1) a = sign (chartJacobian (centered x) j B 0) • outwardClass n j B k a`.
`sphereConnecting x d (k + 1) a = sign (chartJacobian (centered x) j B 0) • outwardClass n j B k a`. -/
theorem SpherePoint.pointConnecting_eq_outward (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered x) L
        ((NativeParametrization.centered x).source ∩
          NativeParametrization.centered x ⁻¹' W))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian (NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardClass n j B k a := by
  rw [connecting_eq_sign_outward n j B x d k a, outwardPointClass_eq_global]

/-- The identification `H_{n+2}(Sⁿ⁺²) ≃ ℤ` through `outwardClassEquiv` and the top homology of
`Sⁿ⁺¹`. -/
def SpherePoint.sourceCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2) ≃ₗ[ℤ] ℤ :=
  (outwardClassEquiv n j B n).trans (SphereHomology.unitSphereHomologyTopEquiv n)

/-- The identification `H_{n+1}(S(N)) ≃ ℤ` through `(LinearSphereAction.homologyEquiv B)⁻¹` and the
top homology of `Sⁿ⁺¹`. -/
def SpherePoint.overlapCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (n + 1) ≃ₗ[ℤ] ℤ :=
  (LinearSphereAction.homologyEquiv B (n + 1)).symm.trans
    (SphereHomology.unitSphereHomologyTopEquiv n)

/-- The identification `H_{n+2}(OnePoint N) ≃ ℤ` through the suspension isomorphism
`OnePointCover.sphereHomologyEquiv` and `overlapCountMark`. -/
def SpherePoint.targetCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2) ≃ₗ[ℤ] ℤ :=
  (OnePointCover.sphereHomologyEquiv 1 zero_lt_one n).trans (overlapCountMark n B)

/-- `overlapCountMark n B` of `H_{n+1}(sphereMap B) a` is the top-homology mark of `a`. -/
theorem SpherePoint.overlapCountMark_linear (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (n + 1)) :
    overlapCountMark n B
        (SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1) a) =
      SphereHomology.unitSphereHomologyTopEquiv n a := by
  rw [← LinearSphereAction.homologyEquiv_apply]
  change
    SphereHomology.unitSphereHomologyTopEquiv n
        ((LinearSphereAction.homologyEquiv B (n + 1)).symm
          (LinearSphereAction.homologyEquiv B (n + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

/-- If `sphereConnecting 1 _ (n + 1) u = c • H_{n+1}(sphereMap B) (outwardClass n j B n a)`, then
`targetCountMark n B u = c * sourceCountMark n j B a`. -/
theorem SpherePoint.countMark_of_connecting (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (u : SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2))
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2))
    (c : ℤ)
    (h :
      OnePointCover.sphereConnecting 1 zero_lt_one (n + 1) u =
        c •
          SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1)
            (outwardClass n j B n a)) :
    targetCountMark n B u = c * sourceCountMark n j B a := by
  have h' := congrArg (overlapCountMark n B) h
  rw [map_zsmul, overlapCountMark_linear] at h'
  exact h'

end
