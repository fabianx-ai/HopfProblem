/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance

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
