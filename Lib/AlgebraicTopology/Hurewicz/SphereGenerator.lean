/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.DegreeSix
import Lib.AlgebraicTopology.Hurewicz.HopfDegree

/-!
# Six-sphere maps realizing specified homology generators

For a simply connected target with vanishing second through fifth homotopy groups,
degree-six Hurewicz naturality identifies the actual induced homotopy map with the
actual homology map conjugated by Hurewicz isomorphisms. Hence a homology bijection
induces a homotopy bijection at the actual image basepoint.

Given a specified equivalence of target H6 with the integers, pull its inverse-at-one
class back by Hurewicz and choose a based cube representative. Factor that cube through
the fixed boundary-collapse sphere. Evaluation at the zero corner fixes the basepoint;
cube-chain functoriality fixes the image of the quotient cube class. Every target class
is an integer multiple of the specified generator, so this actual homology map is
surjective. Sphere homology and the supplied equivalence give an injection in the same
source-to-target direction. The Noetherian target criterion makes the surjection
injective. Naturality then gives bijectivity on pi6 for this very sphere map.

The generator sign is inherited from the supplied equivalence. No smooth structure,
homotopy inverse, or sphere recognition is asserted.
-/

set_option warningAsError true
set_option autoImplicit false

noncomputable section
open scoped Topology

namespace SixthHurewicz

/-- Hurewicz naturality transfers bijectivity of the actual degree-six homology map
to the actual homotopy map at the quotient sphere's basepoint. -/
theorem homotopyMap_bijective_of_homologyMap_bijective
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (hpi : ∀ k : ℕ, 2 ≤ k → k < 6 → ∀ x : X, Subsingleton (π_ k X x))
    (f : C(SphereCube.Sphere 6, X))
    (hf : Function.Bijective (SingularMayerVietoris.singularHomologyMap f 6)) :
    Function.Bijective (SixthHurewicz.homotopyMap f (SphereCube.point 6)) := by
  let : SimplyConnectedSpace (SphereCube.Sphere 6) := EuclideanSphere.simplyConnectedSpace 4
  let := Hurewicz.sphere_pi_subsingleton_of_lt 6 2 (by decide) (by decide) (SphereCube.point 6)
  let := Hurewicz.sphere_pi_subsingleton_of_lt 6 3 (by decide) (by decide) (SphereCube.point 6)
  let := Hurewicz.sphere_pi_subsingleton_of_lt 6 4 (by decide) (by decide) (SphereCube.point 6)
  let := Hurewicz.sphere_pi_subsingleton_of_lt 6 5 (by decide) (by decide) (SphereCube.point 6)
  let := hpi 2 (by decide) (by decide) (f (SphereCube.point 6))
  let := hpi 3 (by decide) (by decide) (f (SphereCube.point 6))
  let := hpi 4 (by decide) (by decide) (f (SphereCube.point 6))
  let := hpi 5 (by decide) (by decide) (f (SphereCube.point 6))
  let source := hurewiczLinearEquiv (SphereCube.point 6)
  let target := hurewiczLinearEquiv (f (SphereCube.point 6))
  let middle := LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap f 6) hf
  have natural (a : π_ 6 (SphereCube.Sphere 6) (SphereCube.point 6)) :
      middle (source (Additive.ofMul a)) =
        target (Additive.ofMul (homotopyMap f (SphereCube.point 6) a)) :=
    hurewiczLinearEquiv_natural f (SphereCube.point 6) (Additive.ofMul a)
  constructor
  · intro a b hab
    have hm : middle (source (Additive.ofMul a)) = middle (source (Additive.ofMul b)) :=
      (natural a).trans
        ((congrArg (fun c => target (Additive.ofMul c)) hab).trans (natural b).symm)
    exact congrArg Additive.toMul (source.injective (middle.injective hm))
  · intro b
    let a := source.symm (middle.symm (target (Additive.ofMul b)))
    refine ⟨Additive.toMul a, ?_⟩
    have ht : target (Additive.ofMul
        (homotopyMap f (SphereCube.point 6) (Additive.toMul a))) =
        target (Additive.ofMul b) := by
      calc
        _ = middle (source a) := (natural (Additive.toMul a)).symm
        _ = target (Additive.ofMul b) := by
          dsimp [a]
          rw [source.apply_symm_apply, middle.apply_symm_apply]
    exact congrArg Additive.toMul (target.injective ht)

/-- A specified integral H6 generator is realized by a sphere map with controlled
basepoint and bijective actual homology and homotopy maps. -/
theorem exists_sphereMap_of_homologySixEquiv
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (hpi : ∀ k : ℕ, 2 ≤ k → k < 6 → ∀ x : X, Subsingleton (π_ k X x))
    (x : X) (e : SingularMayerVietoris.SingularHomology X 6 ≃ₗ[ℤ] ℤ) :
    ∃ f : C(SphereCube.Sphere 6, X),
      f (SphereCube.point 6) = x ∧
      SingularMayerVietoris.singularHomologyMap f 6
        (Hurewicz.cubeHomologyClass (SphereCube.quotientLoop 6)) = e.symm 1 ∧
      Function.Bijective (SingularMayerVietoris.singularHomologyMap f 6) ∧
      Function.Bijective (SixthHurewicz.homotopyMap f (SphereCube.point 6)) := by
  let := hpi 2 (by decide) (by decide) x
  let := hpi 3 (by decide) (by decide) x
  let := hpi 4 (by decide) (by decide) x
  let := hpi 5 (by decide) (by decide) x
  let h := hurewiczLinearEquiv x
  let a := h.symm (e.symm 1)
  obtain ⟨p, hp⟩ := Quotient.exists_rep a.toMul
  have hrep : h (Additive.ofMul (⟦p⟧ : π_ 6 X x)) = Hurewicz.cubeHomologyClass p := rfl
  have hclass : Hurewicz.cubeHomologyClass p = e.symm 1 :=
    hrep.symm.trans ((congrArg h (congrArg Additive.ofMul hp)).trans
      (h.apply_symm_apply (e.symm 1)))
  let f := SphereCube.factorMap (by decide : 0 < 6) p
  have hpoint : f (SphereCube.point 6) = x := by
    dsimp [f]
    rw [← SphereCube.quotient_boundary 6 0 (SphereCube.zero_boundary (by decide)),
      SphereCube.factorMap_quotient]
    exact p.property 0 (SphereCube.zero_boundary (by decide))
  have himage : SingularMayerVietoris.singularHomologyMap f 6
      (Hurewicz.cubeHomologyClass (SphereCube.quotientLoop 6)) = e.symm 1 :=
    (SphereCube.factor_cubeHomologyClass_cycle (m := 4) p).trans hclass
  have hgen (z : SingularMayerVietoris.SingularHomology X 6) : z = e z • e.symm 1 := by
    apply e.injective
    calc
      e z = e z • e (e.symm 1) := by rw [e.apply_symm_apply]; simp
      _ = e (e z • e.symm 1) := (map_zsmul e.toAddEquiv (e z) (e.symm 1)).symm
  have hsurj : Function.Surjective (SingularMayerVietoris.singularHomologyMap f 6) := by
    intro z
    refine ⟨e z • Hurewicz.cubeHomologyClass (SphereCube.quotientLoop 6), ?_⟩
    rw [map_zsmul, himage]
    exact (hgen z).symm
  let := isNoetherian_of_injective e.toLinearMap e.injective
  have hinj : Function.Injective (SingularMayerVietoris.singularHomologyMap f 6) :=
    IsNoetherian.injective_of_surjective_of_injective
      ((SphereHomology.unitSphereHomologyTopEquiv 5).trans e.symm).toLinearMap
      (SingularMayerVietoris.singularHomologyMap f 6)
      ((SphereHomology.unitSphereHomologyTopEquiv 5).trans e.symm).injective hsurj
  exact ⟨f, hpoint, himage, ⟨hinj, hsurj⟩,
    homotopyMap_bijective_of_homologyMap_bijective hpi f ⟨hinj, hsurj⟩⟩

end SixthHurewicz
