import Shared.Proof.Algebra.Group.LatticeImageCollapse
import Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix
import Shared.Proof.AlgebraicTopology.Hurewicz.SphereGenerator
import Shared.Proof.Analysis.Complex.RiemannMapping.SectorRoots
import Shared.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization
import Shared.Proof.Data.Int.SignedResidual

/-!
# `Shared`: material used by both proofs

`Shared/Proof/` holds the non-library declarations that both the old proof (`Hopf/Proof`) and the
center construction (`Center/Proof`, `W4W1` on `center-solution`) use.  They were moved here
verbatim from `Hopf/Proof/`.  A module of `Shared` imports Mathlib and `Lib` only; `Hopf` and
`Center` may import `Shared`, `Lib` never does.  `Shared/Proof/AxiomAudit.lean` probes the tree
and is not imported here.
-/
