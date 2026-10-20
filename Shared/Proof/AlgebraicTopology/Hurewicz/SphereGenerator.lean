/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix
import Lib.AlgebraicTopology.Hurewicz.HopfDegree

/-!
# Six-sphere maps realizing specified homology generators

Proof-specific: the degree `6` is hard-coded throughout although every step (degree-six Hurewicz
naturality, sphere homology, the Noetherian surjective-implies-injective criterion) is
degree-free; this is the `n = 6` instance of Hatcher, *Algebraic Topology*, Theorem 4.32 together
with naturality, whose general forms live in `Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean` and
`Lib/AlgebraicTopology/Hurewicz/Naturality.lean`.

For a simply connected target with vanishing second through fifth homotopy groups, degree-six
Hurewicz naturality identifies the induced homotopy map with the homology map conjugated by
Hurewicz isomorphisms, so a homology bijection induces a homotopy bijection at the image
basepoint.  Given a specified equivalence of the target's `H₆` with the integers, pulling its
inverse-at-one class back by Hurewicz and factoring a based cube representative through the
boundary-collapse sphere produces a sphere map whose homology map is surjective, hence (over a
Noetherian target) bijective, hence bijective on `π₆`.

Moved out of `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` by the round-8 D-file pass
(`Lib/reports/round-7/judgement/d-files.md`).

Moved verbatim from `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean`: the declarations
of that file that both the old proof and the center construction use
(`Lib/reports/center-proof/RECEIPT.md`).
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

end SixthHurewicz
