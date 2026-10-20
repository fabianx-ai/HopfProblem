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
# Homotopy six-sphere data: connectivity and homology vanishing (proof-specific)

Proof-specific material of the six-sphere formalization; it is not library
mathematics and is therefore not registered in `Lib.lean`.  `SixSphere` is the
project's round unit sphere in `ℝ⁷`, and the three lemmas below are the
specialisations of Mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`,
`EuclideanSphere.simplyConnectedSpace` and of
`SphereHomology.unitSphere_homology_subsingleton` to that one sphere, used as
the hypothesis-generation input of the six-dimensional recognition argument
(Smale 1961, Theorem A).  Because every statement is pinned to `Fin 7`, none of
them is a textbook statement; the general facts they instantiate already live in
Mathlib and in `Lib.AlgebraicTopology.SingularHomology.SphereHomology`.

## Main declarations

* `SixSphere` : the unit sphere in `EuclideanSpace ℝ (Fin 7)`.
* `simplyConnectedSpace_of_homotopySixSphere`,
  `pathConnectedSpace_of_homotopySixSphere` : connectivity of a homotopy `S⁶`.
* `homotopySixSphere_homology_subsingleton` : `Hₖ(M)` is a subsingleton for
  `k ∉ {0, 6}` when `M ≃ₕ SixSphere`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Ch. 9
  (the recognition application this data feeds).

## Tags

six-sphere, homotopy equivalence, simple connectivity, singular homology
-/

open Set Function Filter Manifold Topology
open scoped ContinuousMap


@[expose] public noncomputable section

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

