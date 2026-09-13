/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Homotopy six-sphere data: connectivity and homology vanishing

`SixSphere` is the round unit sphere in `ℝ⁷`. A space homotopy equivalent to it
inherits its basic invariants: `simplyConnectedSpace_of_homotopySixSphere` and
`pathConnectedSpace_of_homotopySixSphere` give simple and path connectivity, and
`homotopySixSphere_homology_subsingleton` gives `Subsingleton` singular homology in
every degree other than `0` and `6` (transported through
`SingularHomology.homotopyEquivHomologyEquiv` from
`SphereHomology.unitSphere_homology_subsingleton`).

This is the hypothesis-generation input for the six-dimensional recognition
theorem (Smale 1961, Theorem A): the two-critical-point Morse conclusion is
assembled over this data, not inside this file.

## Main declarations

* `SixSphere` : the unit sphere in `EuclideanSpace ℝ (Fin 7)`.
* `simplyConnectedSpace_of_homotopySixSphere`,
  `pathConnectedSpace_of_homotopySixSphere` : connectivity of a homotopy `S⁶`.
* `homotopySixSphere_homology_subsingleton` : `Hₖ(M)` is a subsingleton for
  `k ∉ {0, 6}` when `M ≃ₕ SixSphere`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Ch. 9
  (the recognition application this data feeds).

## Twin

No Mathlib counterpart exists; the declarations are upstream-shaped but have no
Mathlib file to converge to.

## Tags

six-sphere, homotopy equivalence, simple connectivity, singular homology
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology
open scoped ContinuousMap


@[expose] public noncomputable section

namespace Mathoverflow1973

abbrev SixSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

theorem simplyConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ SixSphere) : SimplyConnectedSpace M := by
  let : SimplyConnectedSpace SixSphere := EuclideanSphere.simplyConnectedSpace 4
  exact e.simplyConnectedSpace

theorem pathConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ SixSphere) : PathConnectedSpace M := by
  let : SimplyConnectedSpace M := simplyConnectedSpace_of_homotopySixSphere e
  infer_instance

theorem homotopySixSphere_homology_subsingleton {M : Type} [TopologicalSpace M]
    (h : M ≃ₕ SixSphere) (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology M k) := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology SixSphere k) :=
    SphereHomology.unitSphere_homology_subsingleton 5 k hk hktop
  exact (SingularHomology.homotopyEquivHomologyEquiv h k).injective.subsingleton

end Mathoverflow1973
