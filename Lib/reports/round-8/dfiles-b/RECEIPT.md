# Round-8 receipt: `dfiles-b`

Packet: the D-verdict files of `Lib/reports/round-7/judgement/d-files.md` under `Lib/Algebra`,
`Lib/AlgebraicTopology`, `Lib/GroupTheory`, `Lib/LinearAlgebra`, `Lib/Analysis`, `Lib/Data`.
Worktree `/home/goblin/hopf-r8-dfiles-b`, branch `r8/dfiles-b`, base `4e15a034`.

Two files named in the packet were already settled by the round-7 names branch and were skipped:
`Lib/GroupTheory/SplitExtension.lean` (kept: Mathlib's `GroupExtension.Splitting` needs the
conjugation action) and `Lib/LinearAlgebra/Dual/Contragredient.lean` (already deleted at the base).

## Per item

| file | verdict executed | commit |
| --- | --- | --- |
| `Lib/Algebra/Group/SurjectiveDescent.lean` | deleted; Mathlib twins named below | `fff26c16` |
| `Lib/Algebra/Group/ResidualRelations.lean` | moved to `Hopf/Proof/Algebra/Group/ResidualRelations.lean` | `282ec4c1` |
| `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | moved to `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | `23f6eb4d` |
| `Lib/Algebra/Group/LatticeImageCollapse.lean` | moved to `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` |
| `Lib/Analysis/Real/MeshScale.lean` | folded into its only consumer, renamed out of Mathlib's `Real` | `b67b67df` |
| `Lib/Data/Int/SignedResidual.lean` | moved to `Hopf/Proof/Data/Int/SignedResidual.lean`, renamed out of Mathlib's `Int` | `cd893c55` |
| `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` | moved to `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` | `b5767bb7` |
| `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean` | moved to `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` | `ba11838f` |
| `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | moved to `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` |
| `Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean` | island kept in Lib, renamed by its statement | `67f49883` |
| `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean` | **partial**: stray general lemmas extracted; file cannot leave Lib (see below) | `513197b9` |
| `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean` | **partial**: general island given its own documented module; file cannot leave Lib (see below) | `9ec657d4` |

### `Lib/Algebra/Group/SurjectiveDescent.lean` — deleted

Auditors: "Mathlib already has it: `MonoidHom.liftOfSurjective`". The only consumer was
`Lib/AxiomAudit.lean`; its probe block and the `Lib.lean` entry were removed. Twins, verified with
`#check` under `lake env lean` before deleting:

| deleted | surviving twin |
| --- | --- |
| `descendHomOfSurjective` | `MonoidHom.liftOfSurjective` (Mathlib/Algebra/Group/Subgroup/Ker.lean) |
| `descendHomOfSurjective_comp` | `MonoidHom.liftOfRightInverse_comp` (`liftOfSurjective` is `liftOfRightInverse` at `Function.surjInv`) |
| `fibre_constant_of_ker_le` | Mathlib's `{ g // f.ker ≤ g.ker }` subtype packaging of the same hypothesis; the lemma existed only to convert that hypothesis into the fibre-constancy form `descendHomOfSurjective` demanded, and has no other use |

`MonoidHom.liftOfSurjective_comp` does **not** exist in Mathlib v4.33.0; the `_comp` twin is
`MonoidHom.liftOfRightInverse_comp`.

### `Lib/Algebra/Group/LatticeImageCollapse.lean` — moved, and is a duplicate

The 14 declarations duplicate the `LatticeCuspNormalClosure.*` family of
`Hopf/Proof/LCP/BoundaryTopology.lean`, stated there for `PeriodLattice = Fin 4 → ℤ`, `A₁`, `A₂`,
`ε = ![1,2,-4,0]`, `ε' = ![1,3,-3,0]` and `γ v = v 0` of `Hopf/Proof/FiniteCore.lean`. That family,
not this module, is what the proof uses; the module had no consumer at all. It was moved rather
than deleted so that no statement is lost (`image_firstBasis_eq` has no counterpart in the
`LatticeCuspNormalClosure` family), and it is pulled into the build by `Hopf/Proof/Final.lean`.
The duplication is recorded here for whoever removes one of the two copies.

### `Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean` — island kept in Lib

The D verdict is about the name ("the paper-facing lower transfer condition"), not the content:
all five declarations are generic over `[CommRing R]`, and the Lib file
`Lib/Algebra/Homology/ThreeColumnSpectralSequence/LowerTransfer.lean` consumes them, so moving
them under `Hopf/Proof` would make a Lib file import `Hopf.*` (forbidden by
`scripts/lib_stock_census.py`'s second guard). The island therefore stays in Lib and is renamed
to say what it asserts; the module docstring gains `## Main results` and a Weibel §5.2 reference.

### The two files that could not leave Lib

`Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean` (65 → 58 declarations) and
`Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean` (48 → 35 declarations) are consumed by
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` (and `MiddleBlocks.lean`,
`SurgeryHomology.lean`):

* from `LocalDegreeNeighborhoods`: `LocalDegree.nonempty_separatedNeighborhoods`,
  `LocalDegree.SeparatedNeighborhoods.overlapMap_coe`,
  `LocalDegree.NativeNeighborhood.singlePoint_cover`, `NativeChartTransition.*`;
* from `OnePointCover`: `OnePointCover.{oldPatch, finitePatch, cover, oldPatch_open,
  finitePatch_open, overlapRadius, overlapRadius_pos}`,
  `SphereNormalCoordinates.normalDerivative_smul_isInvertible`,
  `SpherePoint.{instLocal2, instLocal3}`.

`SurgeryCollapse.lean` belongs to the round-7 **monoliths** packet (another agent) and stays in
Lib, so moving either file under `Hopf/Proof` this round would make Lib files import `Hopf.*`.
What the auditors named as keepable/misfiled was done instead:

* `LinearSphereAction.{sphereMap_comp, sphereMap_trans, normalized_linearSphereMap,
  sphereMap_relative, homology_relative_sign}` → `Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean`
  (docstrings added; that module already owns `LinearSphereAction.sphereMap` and
  `homology_eq_sign_smul`).
* `SublevelDisk.{contractibleSpace, homology_subsingleton}` → `Lib/Geometry/Manifold/Morse/Reeb.lean`
  (docstrings added). The auditors said `Morse/SublevelSets`; `SublevelDisk` itself is declared in
  `Morse/Reeb.lean`, so that is the owner. `Reeb.lean` gains
  `import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance`.
* the 13 `SpherePoint.*` transport declarations → the new documented module
  `Lib/AlgebraicTopology/SingularHomology/SpherePointTransport.lean` ("the special orthogonal
  group acts transitively on the unit sphere by maps of determinant one, and such a map is the
  identity on singular homology"; Hatcher §2.2), which imports only `Mathlib` and
  `Lib.AlgebraicTopology.SingularHomology.LinearSphereAction` instead of `OnePointCover`'s
  48-import block.

**Left for a later round** (needs `SurgeryCollapse.lean` to be settled first): moving the
remaining native-chart / one-point-cover material of those two files under `Hopf/Proof`, their
48-import blocks, and the missing docstrings on their remaining declarations.

## Rename map

`rename-old-to-new.txt` is the human-readable map (`old new`). `rename.txt` is the file handed to
`lean-agent-ide dump --rename`, which per `spec/dump.md` must send every **new** name back to its
**old** spelling, i.e. it is the same map with the columns swapped.

| old | new |
| --- | --- |
| `Real.exists_mesh_scale` | `TopologicalSpace.CubeBoundaryThree.exists_mesh_scale` |
| `Int.signed_residual_coordinate_zero` | `ThreefoldHomology.signed_residual_coordinate_zero` |
| `ThreeColumnPage.LowerTransferCondition` | `ThreeColumnPage.LowerDifferentialsBijectiveAndNeZero` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_coefficients` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_coefficients` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_isUnit_of_coefficients_eq` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_isUnit_of_coefficients_eq` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_injective` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_injective` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_all_subsingleton` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_all_subsingleton` |
| `ThreeColumnSpectralSequence.Convergence.lowerTransferCondition` | `ThreeColumnSpectralSequence.Convergence.lowerDifferentialsBijectiveAndNeZero` |

## Lost names

`envdiff.txt` / `envdiff.json` (copied here) report, over the rename map:

```
constants before 38593 after 38588 (keys 38491 38486)
lost 8 added 3 of which source declarations: 3 0 ; names with changed type 0 of which source: 0
```

The three lost source declarations are exactly the three deleted above; no other name was lost and
no type changed.

| lost source name | surviving twin |
| --- | --- |
| `descendHomOfSurjective` | `MonoidHom.liftOfSurjective` |
| `descendHomOfSurjective_comp` | `MonoidHom.liftOfRightInverse_comp` |
| `fibre_constant_of_ker_le` | Mathlib's `{ g // f.ker ≤ g.ker }` subtype hypothesis |

The remaining five lost / three added entries are auxiliary (`_proof_*`, `.eq_1`) equation and
proof constants of the renamed and moved declarations, which the rename map does not cover;
`envdiff` does not judge them. `changed_type_source`, `changed_type_proof_naming`,
`changed_type_accepted` and `changed_type_all` are all empty.

### Module moves (reported, not judged)

```
      14  Lib.Algebra.Group.LatticeImageCollapse -> Hopf.Proof.Algebra.Group.LatticeImageCollapse
       1  Lib.Algebra.Group.ResidualRelations -> Hopf.Proof.Algebra.Group.ResidualRelations
       5  Lib.Algebra.Homology.ThreeColumnPage.LowerTransfer -> Lib.Algebra.Homology.ThreeColumnPage.LowerDifferentials
       1  Lib.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter -> Hopf.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter
      21  Lib.AlgebraicTopology.Hurewicz.DegreeSix -> Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix
       2  Lib.AlgebraicTopology.Hurewicz.SphereGenerator -> Hopf.Proof.AlgebraicTopology.Hurewicz.SphereGenerator
       5  Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods -> Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
       2  Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods -> Lib.Geometry.Manifold.Morse.Reeb
      13  Lib.AlgebraicTopology.SingularHomology.OnePointCover -> Lib.AlgebraicTopology.SingularHomology.SpherePointTransport
       1  Lib.Analysis.Real.MeshScale -> Lib.Topology.Dimension.CubeBoundaryThreeLebesgue
       1  Lib.Data.Int.SignedResidual -> Hopf.Proof.Data.Int.SignedResidual
      20  Lib.GroupTheory.PresentedGroup.CentralTwist -> Hopf.Proof.GroupTheory.PresentedGroup.CentralTwist
ambiguous module changes: 0
auxiliary constants that changed module: 34
```

`envdiff`'s `VERDICT FAIL` is the expected consequence of the three intentional deletions; every
lost source name is accounted for in the table above.

## Build

Every edited module was built in the foreground before each commit; the final state builds green:

```
lake build Lib Solution S6Shortcuts S6 Challenge Lib.AxiomAudit
Build completed successfully (9190 jobs).
real    10m28.960s
```

`Lib.AxiomAudit` emits only the three permitted axioms: over the whole audit the axiom lines are
`[propext, Classical.choice, Quot.sound]` (1712), `[propext, Quot.sound]` (112), `[propext]` (10),
and 12 declarations depend on no axiom; no other axiom appears.

```
python3 scripts/lib_stock_census.py --check
stock declarations under Hopf/: 123
ratchet PASS: 123 <= baseline 1648
```

The census is unchanged by the moves: `scripts/lib_stock_census.py` excludes `Hopf/Proof/`.

## New modules

Not registered in `Lib.lean` (they are proof-side):

* `Hopf/Proof/Algebra/Group/ResidualRelations.lean`
* `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean`
* `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean`
* `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean`
* `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean`
* `Hopf/Proof/Data/Int/SignedResidual.lean`
* `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean`

Registered in `Lib.lean`:

* `Lib/AlgebraicTopology/SingularHomology/SpherePointTransport.lean`
* `Lib/Algebra/Homology/ThreeColumnPage/LowerDifferentials.lean` (renamed from `LowerTransfer.lean`)

The three modules whose declarations have no consumer (`ResidualRelations`,
`FiniteStarCharacter`, `LatticeImageCollapse`) are pulled into the proof build by
`Hopf/Proof/Final.lean`; the others are imported by the file that uses them
(`Hopf/Proof/LCP/IntegralHomology.lean`, `Hopf/Proof/LCP/BoundaryTopology.lean`,
`Hopf/Recognition.lean`, `Hopf/Proof/Recognition.lean`).

## Commits

`4e15a034..` (oldest first)

```
fff26c16 Lib/Algebra/Group/SurjectiveDescent.lean: delete (Mathlib has it)
282ec4c1 Lib/Algebra/Group/ResidualRelations.lean: move to Hopf/Proof
23f6eb4d Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean: move to Hopf/Proof
31c38660 Lib/Algebra/Group/LatticeImageCollapse.lean: move to Hopf/Proof
b67b67df Lib/Analysis/Real/MeshScale.lean: fold into its only consumer
cd893c55 Lib/Data/Int/SignedResidual.lean: move to Hopf/Proof and out of Int
b5767bb7 Lib/GroupTheory/PresentedGroup/CentralTwist.lean: move to Hopf/Proof
ba11838f Lib/AlgebraicTopology/Hurewicz/{DegreeSix,SphereGenerator}.lean: move to Hopf/Proof
67f49883 Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean: name the island by its statement
513197b9 Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean: extract the stray general lemmas
9ec657d4 Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean: give the sphere-transport island its own owner
```

`DegreeSix` and `SphereGenerator` share one commit: `SphereGenerator` imports `DegreeSix` and is
its only Lib consumer, so splitting them would leave a Lib file importing `Hopf.*` at the
intermediate commit.
