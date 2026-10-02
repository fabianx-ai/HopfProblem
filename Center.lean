import Center.Proof.Algebra.Group.LatticeImageCollapse
import Center.Proof.Algebra.Group.ResidualRelations
import Center.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter
import Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots
import Center.Proof.Topology.Sheaves.Cohomology.SphereTwo

/-!
# `Center`: material specific to the center construction

`Center/Proof/` holds declarations that only the center construction (the `W4W1` development of
branch `center-solution`) needs and that are not library mathematics.  They were moved here
verbatim from `Hopf/Proof/`, whose old proof is frozen.  A module of `Center` imports Mathlib and
`Lib` only; `Center` never imports `Hopf`, `Hopf` never imports `Center`, and `Lib` imports
neither.  `Center/Proof/AxiomAudit.lean` probes the tree and is not imported here.
-/
