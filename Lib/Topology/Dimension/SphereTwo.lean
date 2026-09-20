module
public import Lib.Topology.Dimension.CubeBoundaryThreeDimension

/-!
# Covering dimension of the two-sphere

The standard two-sphere `S² ⊆ ℝ³` has Lebesgue covering dimension at most two, and hence so does
every space homeomorphic to it.  This is the upper half of `dim Sⁿ = n` for `n = 2`; it is
obtained by transporting the bound for the boundary of the three-cube along the radial
homeomorphism.

## References

* R. Engelking, *Dimension Theory*, 1.8.3 and 1.8.6 (`dim Sⁿ = n`)
* W. Hurewicz and H. Wallman, *Dimension Theory*, Theorem IV 1 and Chapter IV §4
-/

set_option autoImplicit false
set_option warningAsError true

namespace TopologicalSpace.SphereTwo

/-- The standard two-sphere in `ℝ³` has Lebesgue covering dimension at most two: every open
cover has an open refinement in which no point lies in more than three members (Engelking,
*Dimension Theory*, 1.8.3). -/
public theorem hasCoveringDimensionLE_two :
    HasCoveringDimensionLE
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 2 :=
  HasCoveringDimensionLE.of_homeomorph
    CubeBoundaryThree.homeomorphSphere.symm CubeBoundaryThree.hasCoveringDimensionLE_two

/-- Every space in `Type` homeomorphic to the standard two-sphere has Lebesgue covering
dimension at most two, covering dimension being a topological invariant (Engelking, *Dimension
Theory*, 1.8.3).  The universe is not a restriction of the mathematics but of
`HasCoveringDimensionLE.of_homeomorph`, which, following the `ParacompactSpace` convention that
cover indices live in the space's universe, transports only between spaces in one universe. -/
public theorem hasCoveringDimensionLE_two_of_homeomorph
    {B : Type} [TopologicalSpace B]
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    HasCoveringDimensionLE B 2 :=
  HasCoveringDimensionLE.of_homeomorph g hasCoveringDimensionLE_two

end TopologicalSpace.SphereTwo
