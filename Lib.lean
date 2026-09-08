import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.Topology.Homotopy.Suspension
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.ChartedSpace.Transport
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Analysis.Complex.Mobius
import Lib.Geometry.Manifold.Instances.RiemannSphere
import Lib.Analysis.Complex.SchwarzReflection
import Lib.Analysis.Complex.RiemannMapping
import Lib.Analysis.Complex.RiemannMapping.Steps
import Lib.Analysis.Complex.Cousin
import Lib.Analysis.Complex.SquareRoot
import Lib.Geometry.Manifold.Complex.Biholomorph
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Topology.Homotopy.CellAttachment
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Algebra.Group.Filtration
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator
import Lib.AlgebraicTopology.Hurewicz.Subdivision
import Lib.AlgebraicTopology.Hurewicz.CubeGluing
import Lib.AlgebraicTopology.Hurewicz.Degree
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
import Lib.AlgebraicTopology.Hurewicz.CycleClasses
import Lib.AlgebraicTopology.Hurewicz.Degree1
import Lib.AlgebraicTopology.Hurewicz.H1Character
import Lib.AlgebraicTopology.Hurewicz.PeriodicLoop
import Lib.AlgebraicTopology.Hurewicz.SimplexPaths
import Lib.GroupTheory.Abelianization.SemidirectProduct
import Lib.GroupTheory.GroupExtension.Abelianization
import Lib.GroupTheory.GeneratingSet
import Lib.LinearAlgebra.CyclicAverage
import Lib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Lib.LinearAlgebra.FreeModule.RankTwoCokernel
import Lib.LinearAlgebra.SquareZero
import Lib.GroupTheory.SplitExtension
import Lib.GroupTheory.PresentedGroup.CentralTwist
import Lib.Topology.FiberBundle.TwoOpenTransition
import Lib.Topology.Covering.Quotient
import Lib.Topology.Covering.DiagonalQuotient
import Lib.Topology.Covering.InvariantSubset
import Lib.Topology.Homotopy.SublevelRetraction
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.MappingTorus.HomologyCover
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.PathClass

/-!
# Reusable V10 Section 6 library

This root exports proof-independent mathematics extracted from checked V10 modules and checked in
the Hopf development. Files below `Lib/` do not import `S6Shortcuts`, `S6`, `Hopf`, `Challenge`,
or `Solution`; proof-specific data and adapters live downstream.

The exported modules contain the reusable algebraic results formalized from V10 Section 6. Results
which still lack a Lean proof are documented as gaps rather than represented by placeholders.
-/
