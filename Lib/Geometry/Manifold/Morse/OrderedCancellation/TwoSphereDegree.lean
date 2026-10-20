/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere

/-!
# Self-maps of the two-sphere with bijective `H₂` act by a unit

An automorphism of `ℤ` as a `ℤ`-module is multiplication by `1` or by `-1`
(`IntLinearAutomorphism.apply_one_eq_one_or_neg_one`).  Consequently, if `g : S² → Y` induces a
bijection on `H₂` and `Y` is homeomorphic to `S²` via `e`, then `H₂(g) = ±H₂(e)`
(`MorseCancellation.two_sphere_map_unit_of_homology_bijective`): the degree of a homology
isomorphism of `S²` is a unit, cf. Hatcher, *Algebraic Topology*, §2.2 (degree).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- A `ℤ`-linear automorphism `e` of `ℤ` is multiplication by `e 1`: `e k = e 1 * k`. -/
theorem IntLinearAutomorphism.apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (k : ℤ) : e k = e 1 * k := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul k 1

/-- A `ℤ`-linear automorphism `e` of `ℤ` sends `1` to `1` or to `-1`. -/
theorem IntLinearAutomorphism.apply_one_eq_one_or_neg_one (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := e.symm 1)
  rw [← apply_eq_mul, e.apply_symm_apply]

/-- Let `e : S² ≃ₜ Y` be a homeomorphism and `g : C(S², Y)` a map inducing a bijection on `H₂`.
Then `H₂(g) = k • H₂(e)` for some `k ∈ {1, -1}`: a homology isomorphism of the two-sphere has
degree `±1` relative to the homeomorphism. -/
theorem MorseCancellation.two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : (Hemisphere.Sphere 2) ≃ₜ Y) (g : C((Hemisphere.Sphere 2), Y))
    (hg : Function.Bijective (SingularMayerVietoris.singularHomologyMap g 2)) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap g 2 =
          k •
            SingularMayerVietoris.singularHomologyMap (e : C((Hemisphere.Sphere 2), Y)) 2 :=
  by
  let H := SphereHomology.unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap g 2) hg
  let J := SingularHomology.homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

end
