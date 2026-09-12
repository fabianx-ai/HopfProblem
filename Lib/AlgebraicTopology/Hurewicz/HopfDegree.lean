/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology

/-!
# Connectivity from the Hurewicz theorem

For a simply connected space whose integral homology vanishes in degrees `2 ≤ k < n`,
`HigherHurewicz.pi_subsingleton_of_homology_vanishing` proves that its homotopy groups
vanish in the same range. In particular, `HigherHurewicz.sphere_pi_subsingleton_of_lt`
proves `Subsingleton (π_ k (Degree.SphereCube.Sphere n) x)` for `2 ≤ k < n`.

## Outline of the proof

1. Strong induction supplies all lower homotopy-group hypotheses to
   `HigherHurewicz.hurewiczLinearEquivOfTwoLE`.
2. Injectivity transfers the assumed homology vanishing back to homotopy.
3. `EuclideanSphere.simplyConnectedSpace` and
   `SphereHomology.unitSphere_homology_subsingleton` specialize the result to spheres.

## Main definitions and results

* `HigherHurewicz.pi_subsingleton_of_homology_vanishing`: homology vanishing implies
  homotopy vanishing below the first possible nonzero degree.
* `HigherHurewicz.sphere_pi_subsingleton_of_lt`: the higher connectivity of spheres.

Spaces are in `Type` because the integral singular-chain interface is universe zero.
This file uses plain imports until its legacy dependencies support the module system.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 4.32;
  the sphere bootstrap is the application recorded in `Lib/docs/C.md`, §15.

## Tags

Hurewicz theorem, sphere, connectivity, homotopy group
-/

open Topology

noncomputable section

namespace Mathoverflow1973.HigherHurewicz

/-! ### Homology vanishing and strong induction -/

/-- In a simply connected space, homology vanishing below a degree implies homotopy
vanishing in degrees at least two below that degree. -/
theorem pi_subsingleton_of_homology_vanishing {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hH : ∀ k, 2 ≤ k → k < n → Subsingleton (SingularMayerVietoris.SingularHomology X k))
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) : Subsingleton (π_ k X x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    letI := hH k hk hkn
    have hpi : ∀ j, 2 ≤ j → j < k → Subsingleton (π_ j X x) :=
      fun j hj hjk => ih j hjk hj (by omega)
    have hsub : Subsingleton (Additive (π_ k X x)) :=
      (hurewiczLinearEquivOfTwoLE x k hk hpi).injective.subsingleton
    exact ⟨fun a b => congrArg Additive.toMul
      (@Subsingleton.elim _ hsub (Additive.ofMul a) (Additive.ofMul b))⟩

/-! ### Sphere connectivity -/

/-- The homotopy groups of the n-sphere vanish in degrees `2 ≤ k < n`. -/
theorem sphere_pi_subsingleton_of_lt (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (x : Degree.SphereCube.Sphere n) : Subsingleton (π_ k (Degree.SphereCube.Sphere n) x) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  letI : SimplyConnectedSpace (Degree.SphereCube.Sphere (n + 2)) :=
    EuclideanSphere.simplyConnectedSpace n
  exact pi_subsingleton_of_homology_vanishing x (n + 2)
    (fun j hj hjn => SphereHomology.unitSphere_homology_subsingleton (n + 1) j
      (by omega) (by omega)) k hk hkn

end Mathoverflow1973.HigherHurewicz
