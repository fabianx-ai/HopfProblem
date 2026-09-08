module
public import Lib.Topology.Dimension.CubeBoundaryThreeDimension

set_option autoImplicit false
set_option warningAsError true

namespace TopologicalSpace.SphereTwo

/-- The standard two-sphere has covering dimension at most two (Corollary 6.2).
Transport the cube-boundary dimension bound along the inverse radial homeomorphism,
from the sphere to the cube boundary, using homeomorphism invariance of the bound. -/
public theorem hasCoveringDimensionLE_two :
    HasCoveringDimensionLE
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 2 :=
  HasCoveringDimensionLE.of_homeomorph
    CubeBoundaryThree.homeomorphSphere.symm CubeBoundaryThree.hasCoveringDimensionLE_two

/-- A Type0 space homeomorphic to the standard two-sphere has covering dimension at most two.
This is Corollary 6.3 in the common-universe-zero formal scope: apply homeomorphism transport
to the given map and the sphere bound. Independently large source universes require a separate
index-universe receipt and are not covered by this declaration. -/
public theorem hasCoveringDimensionLE_two_of_homeomorph
    {B : Type} [TopologicalSpace B]
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    HasCoveringDimensionLE B 2 :=
  HasCoveringDimensionLE.of_homeomorph g hasCoveringDimensionLE_two

end TopologicalSpace.SphereTwo
