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

end TopologicalSpace.SphereTwo
