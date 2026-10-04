# Facade dissolution: receipt

Seat: Claude Opus 5.5 (`claude-opus-5-5`), work seat, 2026-10-04. Branch `work/facades` from
`lib/integration` at `bc0e235e`; 24 facade commits, then this receipt. Nothing moved between trees; no
declaration, proof or non-facade docstring changed (the diff of every facade commit touches only `import`
lines, the deleted facade file and the new `README.md`).

## 1. Which modules are facades

Candidates = every `Lib/**/X.lean` with a directory `Lib/**/X/`: 34. Checked by stripping comments and
docstrings and listing every remaining line that is not `module` or an `import`:

- **24 import-only** (docstring + imports): dissolved, table below.
- **10 not facades** (they carry declarations next to their directory; left untouched):
  `Lib.Algebra.Homology.ThreeColumnPage` (244 non-import lines), `Lib.Algebra.Homology.ThreeColumnSpectralSequence` (123),
  `Lib.AlgebraicTopology.SingularCochains` (128), `Lib.AlgebraicTopology.SingularCochains.DualEvaluation` (745),
  `Lib.AlgebraicTopology.SingularSmallChains.Barycentric` (33: `subdivisionData` and the cover-small theorem),
  `Lib.CategoryTheory.Abelian.RightDerived` (88), `Lib.Topology.Sheaves.ConstantPushforward` (214),
  `Lib.Topology.Sheaves.FiniteClosedPushforward` (197), `Lib.Topology.Sheaves.OpenRestriction` (120),
  `Lib.Topology.Sheaves.PrincipalCoverLocalSystem` (199).

"pieces" = `.lean` files under the directory; "imports" = import lines of the facade; "consumers" = files
other than the facades themselves that imported it (including `Lib.lean`; the facades
`Flow.HeightTranslating` → `MorseLemma` and `Morse.Cancellation` → `Rearrangement`, `Connection` imported
other facades and were dissolved first). Kind: `module` = module-system file, `legacy` = no `module` line
(all imports re-export).

| facade | kind | pieces | imports in facade | consumers |
|---|---|---|---|---|
| `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | legacy | 8 | 8 | 24 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator` | legacy | 16 | 16 | 26 |
| `Lib.AlgebraicTopology.Hurewicz.Subdivision` | legacy | 8 | 8 | 22 |
| `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | module | 9 | 9 | 32 |
| `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | module | 14 | 14 | 69 |
| `Lib.Analysis.Calculus.MorseLemma` | module | 16 | 16 | 80 |
| `Lib.Analysis.Complex.RiemannMapping` | legacy | 10 | 9 | 12 |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation` | module | 10 | 1 | 1 |
| `Lib.Geometry.Manifold.Collar` | module | 8 | 8 | 58 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating` | module | 7 | 13 | 59 |
| `Lib.Geometry.Manifold.Immersion.Relative` | module | 12 | 12 | 50 |
| `Lib.Geometry.Manifold.Morse.Cancellation` | legacy | 12 | 15 | 48 |
| `Lib.Geometry.Manifold.Morse.Connection` | legacy | 18 | 18 | 51 |
| `Lib.Geometry.Manifold.Morse.Cubic` | module | 13 | 13 | 8 |
| `Lib.Geometry.Manifold.Morse.Existence` | module | 10 | 10 | 67 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation` | legacy | 11 | 11 | 3 |
| `Lib.Geometry.Manifold.Morse.Rearrangement` | module | 10 | 10 | 72 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse` | legacy | 14 | 14 | 2 |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows` | module | 11 | 11 | 80 |
| `Lib.Geometry.Manifold.Whitney.CleanStrips` | legacy | 10 | 10 | 13 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | legacy | 13 | 13 | 7 |
| `Lib.Geometry.Manifold.Whitney.FrameField` | legacy | 12 | 12 | 2 |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel` | legacy | 12 | 12 | 4 |
| `Lib.Topology.Dimension.CubeBoundaryThreeCells` | module | 7 | 7 | 3 |

Every facade's piece list is in its new `README.md`. 24 facades, 271 pieces.

## 2. Method (how "needs" was decided)

1. Dump of the head `bc0e235e` in this worktree (`lake env …/lean-agent-ide dump Solution Lib Shared Center
   Unused S6 S6Shortcuts --modules Hopf,Lib,Shared,Center,Unused,S6,S6Shortcuts,Solution`, 39,476
   constants; `Challenge` cannot be a dump root next to `Solution`: both define
   `Mathoverflow1973.mathoverflow_1973`).
2. `U(X)` = defining modules of all constants in the `uses` of X's constants; generated auxiliaries
   (`.eq_n`, `.match_n`, `._proof_n`, …) are also mapped to their parent, so an equation lemma realized in X
   still points to the module of its parent. For the two files without declarations the names are read
   from the text: `Lib/AxiomAudit.lean` (`#check`/`#print axioms` names) and
   `Lib/reports/wave-1/prism/lift_examples.lean` (`example := @name`).
3. Visibility is strict: a module sees its imports plus what they re-export; a module file re-exports its
   `public import`s only, a legacy file all imports. Sanity check: the head satisfies `U(X) ⊆ visible(X)`
   for every project file under this semantics (one exception, an equation lemma of
   `Lib.Topology.MappingTorus.SquareZeroWinding` recorded in `Hopf.Proof.LCP.LocalModels` by realization
   order: not a dependency).
4. Per consumer X: the facade import is dropped; X gets every module of `U(X)` that it saw only through a
   facade, then the set is reduced to an antichain (a module already re-exported by another import of X
   with the right visibility is dropped). `public` is kept exactly where X had `public import` of the
   facade (module files); legacy files keep plain `import`.
5. Downstream fix-point: if a module Y that does not import the facade saw `m` through a consumer Z's
   public facade import, `m` is added to Z (public), not to Y — Z keeps re-exporting what its importers
   relied on. 26 such additions, table §4.
6. Commits: one per facade (its consumers' lines, `Lib.lean`'s line, the deleted facade, the README); a new
   import is assigned to the facade it was seen through (directly imported piece directory first).
   Outer facades first (`Flow.HeightTranslating`, `Morse.Cancellation`), then the others alphabetically.

Scripts and plan (paths inside point to the job scratch): `Lib/reports/facades/{graph,plan,owners,apply}.py`,
`plan.json`.

## 3. `Lib.lean`

Each of the 24 facade lines is replaced, in place, by the facade's pieces in alphabetical order, leaving
out pieces `Lib.lean` already imported (the 10 FibreStalkEvaluation pieces and `RiemannMapping.Steps`); the
file is not globally sorted, so in-place replacement is the order-preserving choice. 260 piece lines added,
449 → 685 import lines.

**Deviation from the requested commit order:** the `Lib.lean` replacement is part of each facade commit,
not a separate commit, because a commit deleting a facade that `Lib.lean` still imports would not build.
There is no separate `Lib.lean` commit.

## 4. Pieces added beyond direct use

**Elaboration-driven additions (instances, notation, simp sets not visible in `uses`): none were needed.**
The first full build of the plan was green without any change.

Re-export additions (method step 5): a consumer keeps re-exporting what a downstream module used through
its facade import.

| consumer | added import | needed downstream by |
|---|---|---|
| `Hopf.Proof.Geometry.Manifold.Morse.BeltCancellation` | `Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy` | `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks` |
| `Hopf.SphereTopology` | `Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian` | `Hopf.Recognition` |
| `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse` | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation` |
| `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.MapGenLoop` | `Lib.AlgebraicTopology.Hurewicz.Naturality` |
| `Lib.AlgebraicTopology.Hurewicz.CubeGluing` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.ComposeHomotopies` | `Lib.AlgebraicTopology.Hurewicz.Straightening` |
| `Lib.AlgebraicTopology.Hurewicz.CubeGluing` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse` | `Lib.AlgebraicTopology.Hurewicz.Degree` |
| `Lib.AlgebraicTopology.Hurewicz.CubeGluing` | `Lib.AlgebraicTopology.Hurewicz.Subdivision.SubdivisionClass` | `Lib.AlgebraicTopology.Hurewicz.CubeSphere` |
| `Lib.Geometry.Manifold.Morse.AdaptedWindows` | `Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation` | `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks` |
| `Lib.Geometry.Manifold.Morse.AdaptedWindows` | `Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree` | `Lib.Geometry.Manifold.Morse.EqualRangeHomology` |
| `Lib.Geometry.Manifold.Morse.AdaptedWindows` | `Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange` | `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks` |
| `Lib.Geometry.Manifold.Morse.Cubic.AlignedRays` | `Lib.Geometry.Manifold.Collar.DiskTubular` | `Lib.Geometry.Manifold.Transversality.DiscTheorem` |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance` | `Lib.Geometry.Manifold.Morse.Existence.LevelSurgery` | `Lib.Geometry.Manifold.Morse.SurgeryWindows.BeltComplement` |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance` | `Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation` | `Lib.Geometry.Manifold.Morse.SurgeryWindows.ImageComplement` |
| `Lib.Geometry.Manifold.Whitney.AnnularExtension` | `Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.WhitneyDisc` |
| `Lib.Geometry.Manifold.Whitney.AnnularExtension` | `Lib.Geometry.Manifold.Whitney.CleanStrips.BeltIntersection` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.BeltBigon` |
| `Lib.Geometry.Manifold.Whitney.AnnularExtension` | `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.WhitneyDisc` |
| `Lib.Geometry.Manifold.Whitney.AnnularExtension` | `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` | `Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame` |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts` | `Lib.Geometry.Manifold.Morse.Connection.TimeChange` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripPair` |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts` | `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripPair` |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts` | `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripAlongArc` |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.FiberRestriction` | `Lib.Geometry.Manifold.Whitney.RankThreeModel.ModelGraphMotion` |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion` | `Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame` | `Lib.Geometry.Manifold.Whitney.RankThreeModel.CompatibleChart` |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion` | `Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal` | `Lib.Geometry.Manifold.Whitney.RankThreeModel.TangentAdaptedChart` |
| `Lib.Geometry.Manifold.WhitneyEmbedding` | `Lib.Geometry.Manifold.Morse.Existence.PartialChart` | `Lib.Geometry.Manifold.Whitney.FrameField.SheetCoordinates` |
| `Lib.Topology.Dimension.CubeBoundaryThreeBricks` | `Lib.Topology.Dimension.CubeBoundaryThreeCells.RelInterior` | `Lib.Topology.Dimension.CubeBoundaryThreeDimension` |
| `Lib.Topology.Dimension.CubeBoundaryThreeBricks` | `Lib.Topology.Dimension.CubeBoundaryThreeCells.Separation` | `Lib.Topology.Dimension.CubeBoundaryThreeDimension` |

Other files whose facade line simply disappears: `Lib.AxiomAudit` (`import Lib` already brings the
`CubeBoundaryThreeCells` pieces) and 108 more consumers whose other imports already re-export everything
they use from the facade (marked "—" in §5).

Non-piece modules: 14 new import lines name a module that is not a piece of the facade but was re-exported
by it (`Flow.Compact`, `Morse.CubicFlow`, `Transversality.Transverse`, `Transversality.SupportedIsotopy`,
`WhitneyEmbedding`; via `Flow.HeightTranslating` / `Morse.Cancellation`, whose facades imported those
modules directly).

## 5. Per-consumer reroute

205 consumer files + `Lib.lean`. Facade import lines removed 769 (consumers) + 24 (`Lib.lean`); new import
lines 152 (consumers) + 260 (`Lib.lean`). Import lines in the 206 touched files: 3,794 → 3,413.
"(re-export)" marks a §4 addition.

| consumer | old facade import(s) | new import(s) | import lines before → after |
|---|---|---|---|
| `Hopf.DifferentialTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 19 → 10 |
| `Hopf.Hurewicz` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 66 → 52 |
| `Hopf.LCP.BoundaryTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 92 → 77 |
| `Hopf.LCP.CuspFilling` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 75 → 61 |
| `Hopf.LCP.IntegralHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 94 → 79 |
| `Hopf.LCP.PeriodConstruction` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 80 → 66 |
| `Hopf.LCP.Specialization` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 78 → 64 |
| `Hopf.LibShims` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 25 → 24 |
| `Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 11 → 8 |
| `Hopf.Proof.DifferentialTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 20 → 11 |
| `Hopf.Proof.Final` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 98 → 83 |
| `Hopf.Proof.FiniteCore` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 64 → 50 |
| `Hopf.Proof.Geometry.Manifold.Morse.BeltCancellation` | `Lib.Geometry.Manifold.Whitney.RankThreeModel` | `Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy` (re-export) | 3 → 3 |
| `Hopf.Proof.Geometry.Manifold.Morse.CutTransport` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms`, `Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime`, `Lib.Geometry.Manifold.Morse.Rearrangement.TubeMotion`, `Lib.Geometry.Manifold.Morse.Connection.TimeChange` | 18 → 14 |
| `Hopf.Proof.Geometry.Manifold.Morse.OrderedCancellation.MiddleIndexBlocks` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 12 → 8 |
| `Hopf.Proof.Geometry.Manifold.Morse.Rearrangement.MiddleLevel` | `public Lib.Geometry.Manifold.Morse.Rearrangement` | `public Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness` | 2 → 2 |
| `Hopf.Proof.Geometry.Manifold.Morse.Rearrangement.SheetArc` | `public Lib.Geometry.Manifold.Morse.Rearrangement` | `public Lib.Geometry.Manifold.Immersion.Relative.AxisChart`, `public Lib.Geometry.Manifold.Immersion.Relative.TwoSheetArc`, `public Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart` | 2 → 4 |
| `Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.BeltIntersections` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Whitney.CleanStrips` | — (covered by other imports) | 19 → 13 |
| `Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.MiddleFamilies` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 14 → 11 |
| `Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.MiddlePresentation` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 10 → 7 |
| `Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.OuterIndexMinimal` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 9 → 5 |
| `Hopf.Proof.Geometry.Manifold.Morse.SurgeryHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 49 → 39 |
| `Hopf.Proof.Hurewicz` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 66 → 52 |
| `Hopf.Proof.LCP.AnalyticFillings` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | `Lib.Analysis.Complex.RiemannMapping.ConformalExtension`, `Lib.Analysis.Complex.RiemannMapping.DiscCompactification`, `Lib.Analysis.Complex.RiemannMapping.Existence` | 88 → 76 |
| `Hopf.Proof.LCP.BoundaryTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 94 → 79 |
| `Hopf.Proof.LCP.CuspFilling` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 74 → 60 |
| `Hopf.Proof.LCP.GlobalAssembly` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 87 → 72 |
| `Hopf.Proof.LCP.IntegralHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 97 → 82 |
| `Hopf.Proof.LCP.LocalModels` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 68 → 54 |
| `Hopf.Proof.LCP.PeriodConstruction` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 81 → 67 |
| `Hopf.Proof.LCP.Specialization` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 76 → 62 |
| `Hopf.Proof.Recognition` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 107 → 92 |
| `Hopf.Proof.Shortcuts` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 64 → 50 |
| `Hopf.Proof.SingularHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 35 → 25 |
| `Hopf.Proof.SphereTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 51 → 41 |
| `Hopf.Recognition` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.Subdivision`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition`, `Lib.Analysis.Complex.RiemannMapping` | — (covered by other imports) | 112 → 97 |
| `Hopf.SingularHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.Geometry.Manifold.Whitney.CleanStrips`, `Lib.Geometry.Manifold.Whitney.FrameField`, `Lib.Geometry.Manifold.Whitney.EmbeddedArcs`, `Lib.Geometry.Manifold.Whitney.RankThreeModel` | — (covered by other imports) | 42 → 28 |
| `Hopf.SphereTopology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.OrderedCancellation`, `Lib.Geometry.Manifold.Morse.SurgeryCollapse` | `Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian` (re-export), `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelIsotopy` | 63 → 53 |
| `Lib.lean` | the 24 facades | 260 pieces not imported before (see §3) | 449 → 685 |
| `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse` (re-export), `Lib.AlgebraicTopology.Hurewicz.PrismOperator.MapGenLoop` (re-export) | 2 → 3 |
| `Lib.AlgebraicTopology.Hurewicz.CubeGluing` | `Lib.AlgebraicTopology.Hurewicz.Subdivision` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.ComposeHomotopies` (re-export), `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse` (re-export), `Lib.AlgebraicTopology.Hurewicz.Subdivision.SubdivisionClass` (re-export) | 2 → 4 |
| `Lib.AlgebraicTopology.Hurewicz.CubeSphere` | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Cycle`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator.DegreeTwo` | 5 → 7 |
| `Lib.AlgebraicTopology.Hurewicz.CubeTriangulation` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex` | 2 → 2 |
| `Lib.AlgebraicTopology.Hurewicz.HomotopyExtension` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 2 → 1 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator.Basic` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 4 → 3 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator.CrossProductPoint` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct.Homology` | 2 → 2 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 5 → 4 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 3 → 2 |
| `Lib.AlgebraicTopology.Hurewicz.PrismOperator.TwoTriangles` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 3 → 2 |
| `Lib.AlgebraicTopology.Hurewicz.Subdivision.CubeClass` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareRotation` | 1 → 1 |
| `Lib.AlgebraicTopology.SingularHomology.CirclePaths` | `public Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.CrossProduct.Naturality` | 9 → 8 |
| `Lib.AlgebraicTopology.SingularHomology.CircleProduct` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 6 → 5 |
| `Lib.AlgebraicTopology.SingularHomology.Coproduct` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology` | 5 → 5 |
| `Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology` | 3 → 3 |
| `Lib.AlgebraicTopology.SingularHomology.LinearSphereAction` | `Lib.Geometry.Manifold.Immersion.Relative` | `Lib.Geometry.Manifold.Immersion.Relative.AxisChart` | 5 → 5 |
| `Lib.AlgebraicTopology.SingularHomology.LocalContributions` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 7 → 6 |
| `Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 5 → 4 |
| `Lib.AlgebraicTopology.SingularHomology.LocalDegree` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence` | 3 → 3 |
| `Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 47 → 37 |
| `Lib.AlgebraicTopology.SingularHomology.Naturality` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence` | 5 → 5 |
| `Lib.AlgebraicTopology.SingularHomology.OnePointCover` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 49 → 39 |
| `Lib.AlgebraicTopology.SingularHomology.PathClass` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 12 → 11 |
| `Lib.AlgebraicTopology.SingularHomology.Pontryagin` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `public Lib.AlgebraicTopology.SingularHomology.CrossProduct` | `public Lib.AlgebraicTopology.SingularHomology.CrossProduct.Associator`, `public Lib.AlgebraicTopology.SingularHomology.CrossProduct.Naturality` | 3 → 3 |
| `Lib.AlgebraicTopology.SingularHomology.SphereHomology` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 9 → 8 |
| `Lib.AlgebraicTopology.SingularHomology.Suspension` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence` | 6 → 6 |
| `Lib.AlgebraicTopology.SingularHomology.Torus` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 5 → 4 |
| `Lib.AlgebraicTopology.SingularHomology.TorusCoordinates` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 9 → 7 |
| `Lib.Analysis.Complex.Cousin` | `Lib.Analysis.Complex.RiemannMapping`, `Lib.Analysis.Calculus.MorseLemma` | `Lib.Analysis.Calculus.MorseLemma.PartitionOfUnity` | 4 → 3 |
| `Lib.Analysis.Complex.SquareRoot` | `Lib.Analysis.Complex.RiemannMapping`, `Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 5 → 3 |
| `Lib.Analysis.ODE.SmoothFlow` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating` | — (covered by other imports) | 4 → 2 |
| `Lib.AxiomAudit` | `Lib.Topology.Dimension.CubeBoundaryThreeCells` | — (covered by other imports) | 6 → 5 |
| `Lib.Geometry.Manifold.Collar.HeightCollar` | `public Lib.Geometry.Manifold.Flow.HeightTranslating` | — (covered by other imports) | 4 → 3 |
| `Lib.Geometry.Manifold.Flow.Compact` | `public Lib.Analysis.Calculus.MorseLemma` | `public Lib.Analysis.Calculus.MorseLemma.AdaptedDescentField` | 5 → 5 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.AbsorbingSublevel` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 5 → 4 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.AttachingUnion` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 8 → 7 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 3 → 2 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.DescentModel` | `public Lib.Analysis.Calculus.MorseLemma` | `public Lib.Analysis.Calculus.MorseLemma.AdaptedDescentField` | 3 → 3 |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.HandleCoordinates` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 5 → 4 |
| `Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension` | 2 → 2 |
| `Lib.Geometry.Manifold.Immersion.Relative.ChartPerturbation` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.Existence.ChartPerturbation`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension` | 3 → 4 |
| `Lib.Geometry.Manifold.Immersion.Relative.Embedding` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance` | 4 → 4 |
| `Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus` | `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Flow.Compact` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.AdaptedWindows` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.OrderedCancellation` | `Lib.Geometry.Manifold.Morse.Connection.LevelHolonomy`, `Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation` (re-export), `Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts`, `Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree` (re-export), `Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange` (re-export) | 48 → 42 |
| `Lib.Geometry.Manifold.Morse.BeltCancellation` | `Lib.Geometry.Manifold.Whitney.RankThreeModel` | `Lib.Geometry.Manifold.Morse.Connection.BeltArc`, `Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness`, `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.BeltBigon`, `Lib.Geometry.Manifold.Whitney.RankThreeModel.Cancellation` | 2 → 5 |
| `Lib.Geometry.Manifold.Morse.Birth` | `Lib.Geometry.Manifold.Morse.Cancellation` | `Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms`, `Lib.Geometry.Manifold.Morse.Cancellation.CubicModel`, `Lib.Geometry.Manifold.Morse.Cubic.LocalReplacement` | 1 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.BandHeight` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime` | 4 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.BandReplacement` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 5 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.BasinSheets` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 5 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.ConnectionData` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Connection.CubicFieldChart`, `Lib.Geometry.Manifold.Morse.Connection.EndpointBasins`, `Lib.Geometry.Manifold.Morse.Connection.PhaseFlow` | 4 → 5 |
| `Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Cubic.SurgeryWindowsExistence`, `Lib.Geometry.Manifold.Morse.CubicFlow` | 3 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.CubicConnection` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints` | 6 → 5 |
| `Lib.Geometry.Manifold.Morse.Cancellation.CubicModel` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Cancellation.LevelExit` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 5 → 3 |
| `Lib.Geometry.Manifold.Morse.Cancellation.LogarithmicCutoff` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Cancellation.LyapunovResidence` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Morse.Connection.NoReturn` | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Cancellation.TransverseGerms` | `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Transversality.Transverse` | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.CellStructure` | `Lib.Geometry.Manifold.Collar`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues` | 15 → 13 |
| `Lib.Geometry.Manifold.Morse.CircleGluing` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Connection` | `Lib.Geometry.Manifold.Immersion.Relative.Plane`, `Lib.Geometry.Manifold.Morse.Connection.LevelHolonomy`, `Lib.Geometry.Manifold.Morse.Connection.MinimumBasins` | 33 → 26 |
| `Lib.Geometry.Manifold.Morse.Connection.BeltArc` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.CubicFieldChart` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 7 → 6 |
| `Lib.Geometry.Manifold.Morse.Connection.CylinderHolonomy` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 6 → 5 |
| `Lib.Geometry.Manifold.Morse.Connection.EndpointBasins` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 6 → 5 |
| `Lib.Geometry.Manifold.Morse.Connection.FieldChartGluing` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.WhitneyEmbedding` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.LevelHolonomy` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 4 → 3 |
| `Lib.Geometry.Manifold.Morse.Connection.MinimumBasins` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.NoReturn` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Morse.CubicFlow` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.PhaseCylinder` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 4 → 3 |
| `Lib.Geometry.Manifold.Morse.Connection.PhaseFlow` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Morse.Cubic.LocalReplacement`, `Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates` | 8 → 9 |
| `Lib.Geometry.Manifold.Morse.Connection.SignEnumerations` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Analysis.Calculus.MorseLemma.SplitChart` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.Suspension` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.TimeChange` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.TransitionPhase` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Immersion.Relative.FrameField` | 3 → 3 |
| `Lib.Geometry.Manifold.Morse.Connection.TransportedCorrections` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Transversality.SupportedIsotopy` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Connection.TransverseBlocks` | `Lib.Geometry.Manifold.Morse.Rearrangement` | `Lib.Geometry.Manifold.Immersion.Relative.FrameField` | 5 → 5 |
| `Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts` | `Lib.Geometry.Manifold.Morse.Rearrangement` | — (covered by other imports) | 3 → 2 |
| `Lib.Geometry.Manifold.Morse.Cubic.AlignedRays` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Collar.DiskTubular` (re-export) | 9 → 7 |
| `Lib.Geometry.Manifold.Morse.Cubic.BasinBlock` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.Existence.BeltCore` | 6 → 4 |
| `Lib.Geometry.Manifold.Morse.Cubic.CoreBasins` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 9 → 6 |
| `Lib.Geometry.Manifold.Morse.Cubic.DescentField` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 8 → 5 |
| `Lib.Geometry.Manifold.Morse.Cubic.EndpointChart` | `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Flow.Compact` | 3 → 3 |
| `Lib.Geometry.Manifold.Morse.Cubic.LevelOrbit` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 7 → 4 |
| `Lib.Geometry.Manifold.Morse.Cubic.SplitCoordinates` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 8 → 5 |
| `Lib.Geometry.Manifold.Morse.Cubic.SublevelFlow` | `public Lib.Geometry.Manifold.Flow.HeightTranslating` | `public Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Cubic.SurgeryWindowsExistence` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows.Windows` | 6 → 4 |
| `Lib.Geometry.Manifold.Morse.CubicFlow` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Morse.Cubic` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows.Windows`, `public Lib.Geometry.Manifold.Morse.Cubic.AxisParameter`, `public Lib.Geometry.Manifold.Morse.Cubic.CoreBasins` | 7 → 6 |
| `Lib.Geometry.Manifold.Morse.CutTransport` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection` | — (covered by other imports) | 16 → 8 |
| `Lib.Geometry.Manifold.Morse.Existence.AttachingUnion` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating` | `public Lib.Geometry.Manifold.Flow.HeightTranslating.AttachingUnion` | 5 → 4 |
| `Lib.Geometry.Manifold.Morse.Existence.BeltCore` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating` | — (covered by other imports) | 8 → 6 |
| `Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues` | `public Lib.Analysis.Calculus.MorseLemma` | `public Lib.Analysis.Calculus.MorseLemma.Existence` | 3 → 3 |
| `Lib.Geometry.Manifold.Morse.Existence.LevelSurgery` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating` | `public Lib.Geometry.Manifold.Flow.HeightTranslating.HandleCoordinates` | 5 → 4 |
| `Lib.Geometry.Manifold.Morse.Existence.RegularLocus` | `public Lib.Analysis.Calculus.MorseLemma` | `public Lib.Analysis.Calculus.MorseLemma.CriticalPoints` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.HandleAttachment` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 5 → 4 |
| `Lib.Geometry.Manifold.Morse.Index` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating`, `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 7 → 4 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 8 → 5 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cancellation` | `Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms` | 6 → 5 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization` | `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 10 → 7 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues` | 7 → 4 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cancellation` | `Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms` | 5 → 4 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.PairCancellation` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy`, `Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness` | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 8 → 7 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 9 → 5 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere` | 6 → 5 |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 9 → 5 |
| `Lib.Geometry.Manifold.Morse.RadialFilling` | `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere` | 2 → 2 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.BasinImages` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 11 → 7 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | `public Lib.Geometry.Manifold.Immersion.Relative.Arc` | 12 → 9 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.LongitudinalBlend` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 12 → 8 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | `public Lib.Geometry.Manifold.Immersion.Relative.FrameField` | 10 → 7 |
| `Lib.Geometry.Manifold.Morse.Rearrangement.TubeMotion` | `public Lib.Geometry.Manifold.Morse.Existence`, `public Lib.Geometry.Manifold.Collar`, `public Lib.Geometry.Manifold.Morse.SurgeryWindows`, `public Lib.Geometry.Manifold.Immersion.Relative` | — (covered by other imports) | 14 → 10 |
| `Lib.Geometry.Manifold.Morse.RearrangementAmbient` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | `Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality` | 48 → 39 |
| `Lib.Geometry.Manifold.Morse.RearrangementTheorem` | `Lib.Geometry.Manifold.Morse.Cancellation` | `Lib.Geometry.Manifold.Morse.Cancellation.BandReplacement`, `Lib.Geometry.Manifold.Morse.Cancellation.LevelExit`, `Lib.Geometry.Manifold.Morse.Connection.TimeChange`, `Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation` | 1 → 4 |
| `Lib.Geometry.Manifold.Morse.SublevelSets` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating`, `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 8 → 5 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 14 → 11 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 8 → 7 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskCollapse` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 10 → 9 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling` | `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Whitney.CleanStrips`, `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.ImmersionRepair` | 10 → 6 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleCollapse` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Whitney.CleanStrips` | — (covered by other imports) | 25 → 20 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 15 → 12 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.IndexOrdering` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 18 → 11 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelIsotopy` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | `Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts` | 16 → 11 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 16 → 10 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 13 → 12 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.MinimumReduction` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Morse.Cubic`, `Lib.Geometry.Manifold.Morse.SurgeryWindows` | — (covered by other imports) | 17 → 12 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 8 → 7 |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.Geometry.Manifold.Whitney.CleanStrips`, `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SphereNormalCoordinates` | 15 → 13 |
| `Lib.Geometry.Manifold.Morse.SurgeryHomology` | `Lib.Analysis.Calculus.MorseLemma`, `Lib.Geometry.Manifold.Flow.HeightTranslating`, `Lib.Geometry.Manifold.Morse.Existence`, `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.SurgeryWindows`, `Lib.Geometry.Manifold.Morse.Cancellation`, `Lib.Geometry.Manifold.Immersion.Relative`, `Lib.Geometry.Manifold.Morse.Rearrangement`, `Lib.Geometry.Manifold.Morse.Connection`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 50 → 40 |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance` | `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Morse.Existence.LevelSurgery` (re-export), `public Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation` (re-export) | 3 → 4 |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows.BeltComplement` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating` | — (covered by other imports) | 8 → 6 |
| `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData` | `public Lib.Geometry.Manifold.Collar` | `public Lib.Geometry.Manifold.Collar.LevelTransport`, `public Lib.Geometry.Manifold.Collar.SphereCoordinates`, `public Lib.Geometry.Manifold.Morse.Existence.BeltCore` | 4 → 6 |
| `Lib.Geometry.Manifold.RegularLevel` | `public Lib.Analysis.Calculus.MorseLemma` | — (covered by other imports) | 4 → 3 |
| `Lib.Geometry.Manifold.Transversality.CenteredChart` | `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Flow.Compact` | 3 → 3 |
| `Lib.Geometry.Manifold.Transversality.MorseBelt` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows` | `public Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData` | 2 → 2 |
| `Lib.Geometry.Manifold.Transversality.RegularValues` | `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Flow.Compact`, `public Lib.Geometry.Manifold.Morse.Existence.PartialChart` | 2 → 3 |
| `Lib.Geometry.Manifold.Transversality.Transverse` | `public Lib.Geometry.Manifold.Morse.Existence` | — (covered by other imports) | 3 → 2 |
| `Lib.Geometry.Manifold.VectorBundle.ProjectionBundle` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating`, `public Lib.Geometry.Manifold.Morse.Existence` | — (covered by other imports) | 15 → 12 |
| `Lib.Geometry.Manifold.Whitney.AnnularExtension` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood` (re-export), `Lib.Geometry.Manifold.Whitney.CleanStrips.BeltIntersection` (re-export), `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary` (re-export), `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` (re-export) | 2 → 5 |
| `Lib.Geometry.Manifold.Whitney.CleanStrips.CrossingChart` | `Lib.Geometry.Manifold.Collar`, `Lib.Geometry.Manifold.Morse.Existence` | — (covered by other imports) | 5 → 3 |
| `Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate` | `Lib.Geometry.Manifold.Morse.Existence` | `Lib.Geometry.Manifold.Morse.Existence.PartialChart` | 2 → 2 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood`, `Lib.Geometry.Manifold.Morse.Connection.TimeChange` (re-export), `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary` (re-export), `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` (re-export) | 2 → 5 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SmallPerturbation` | `Lib.Geometry.Manifold.Collar` | `Lib.Geometry.Manifold.Collar.SmallPerturbation` | 2 → 2 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SphereNormalCoordinates` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Whitney.CleanStrips.SphereNormal` | 4 → 4 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripInterpolation` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate`, `Lib.Geometry.Manifold.Whitney.CleanStrips.StripModel` | 3 → 4 |
| `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.TransverseCoordinates` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Immersion.Relative.FrameField`, `Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate` | 2 → 3 |
| `Lib.Geometry.Manifold.Whitney.FrameField.BoundaryField` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary` | 2 → 2 |
| `Lib.Geometry.Manifold.Whitney.FrameField.Complement` | `Lib.Geometry.Manifold.Collar` | `Lib.Geometry.Manifold.Collar.RangeTransport` | 2 → 2 |
| `Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal` | `Lib.Geometry.Manifold.Whitney.CleanStrips` | `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` | 3 → 3 |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.FiberRestriction` (re-export), `Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SmallPerturbation`, `Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame` (re-export), `Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal` (re-export) | 2 → 5 |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRecognition` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | `Lib.Geometry.Manifold.Whitney.FrameField.BoundaryArcs` | 2 → 2 |
| `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRetiming` | `Lib.Geometry.Manifold.Whitney.EmbeddedArcs` | `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData` | 2 → 2 |
| `Lib.Geometry.Manifold.WhitneyEmbedding` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating`, `public Lib.Geometry.Manifold.Morse.Existence` | `public Lib.Geometry.Manifold.Morse.Existence.AttachingUnion`, `public Lib.Geometry.Manifold.Morse.Existence.PartialChart` (re-export) | 16 → 15 |
| `Lib.Topology.Dimension.CubeBoundaryThreeBricks` | `public Lib.Topology.Dimension.CubeBoundaryThreeCells` | `public Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage`, `public Lib.Topology.Dimension.CubeBoundaryThreeCells.RelInterior` (re-export), `public Lib.Topology.Dimension.CubeBoundaryThreeCells.Separation` (re-export), `public Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary` | 7 → 10 |
| `Lib.Topology.Homotopy.CellAttachment` | `Lib.Geometry.Manifold.Collar`, `Lib.Analysis.Calculus.MorseLemma`, `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 11 → 8 |
| `Lib.Topology.Homotopy.CylinderHEP` | `public Lib.Analysis.Calculus.MorseLemma`, `public Lib.Geometry.Manifold.Flow.HeightTranslating`, `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 11 → 8 |
| `Lib.Topology.MappingTorus.Basic` | `public Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 12 → 11 |
| `Lib.Topology.MappingTorus.HomologyCover` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris` | — (covered by other imports) | 13 → 12 |
| `Lib.Topology.MappingTorus.Wang` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | — (covered by other imports) | 27 → 25 |
| `Lib.reports.wave-1.prism.lift_examples` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator` | `Lib.AlgebraicTopology.Hurewicz.PrismOperator.ComposeHomotopies`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator.SubdivisionTriangleClass` | 1 → 2 |
| `Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris`, `Lib.AlgebraicTopology.Hurewicz.PrismOperator`, `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | — (covered by other imports) | 10 → 7 |

## 6. Where the facade docstrings went

Uniformly to a new `README.md` in the facade's directory (`Lib/<path>/<File>/README.md`, 24 files): the
facade's module docstring verbatim (each facade had exactly one `/-! … -/` block), followed by a
`## Modules` section naming the former facade and listing every piece. No piece docstring was edited.

## 7. Import map for `W4W1` on `center-solution`

Appended as a subsection of the import map in `Lib/reports/center-proof/RECEIPT.md`. Of the six facade
names that `W4W1/` imports (7 lines), two are dissolved here:

| CS import line(s) | replace by |
|---|---|
| `W4W1/NativeCornerThree.lean:1` `Lib.Analysis.Complex.RiemannMapping` | `Lib.Analysis.Complex.RiemannMapping.{Existence, DiscBoundaryEscape, HalfStripChart, RectanglePrimitive, ModulusOneReflection, BoundaryDerivative, ConformalExtension, PrincipalRoot, DiscCompactification}` (the deleted facade's nine imports; `.Steps` comes through `.Existence`) |
| `W4W1/CenterHigherNearbyComparison.lean:7`, `W4W1/CenterR1ZeroStalkCriterion.lean:1` `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation` | `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive` (the facade's only import; all ten pieces are an acceptable superset) |
| `Lib.Algebra.Homology.ThreeColumnPage`, `Lib.Topology.Sheaves.ConstantPushforward`, `Lib.Topology.Sheaves.OpenRestriction`, `Lib.Topology.Sheaves.PrincipalCoverLocalSystem` | unchanged: not facades here (§1) |

## 8. Checks (head = last facade commit `f04fdeff`; logs in the job scratch, `final-*.log`)

Lake `…/leanprover--lean4---v4.33.0/bin/lake`, `taskset -c 0-7`, no `-j`.

```
lake build Lib                                   Build completed successfully (9405 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9465 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8868 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9419 jobs).
  probes (grep -cE "^info: <file>.*(depends on axioms|does not depend)"):
    Lib/AxiomAudit.lean 3785   Shared/Proof/AxiomAudit.lean 54   Center/Proof/AxiomAudit.lean 7   Unused/ 34
  all 3866 'depends on axioms' lists ⊆ {propext, Classical.choice, Quot.sound}; sorryAx 0; errors 0
lake env lean Lib/reports/wave-1/prism/lift_examples.lean      exit 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root→Center; Center→Hopf): all empty
grep -rnE '^(public )?import (<24 facade names>)\s*$' over the tree (without .lake): empty
```

Job counts are lower than at `bc0e235e` (Lib 9429 in REPLAY-7c §5) by the deleted facade modules.

Intermediate facade commits were not built one by one; only the final head (and, before the per-facade
commits, a trial tree equal to the head up to the order of import lines, which gave the same results) was
built. Each commit only drops one facade, and the imports added in it are the ones seen through that
facade, so the other facades still present keep every other route open; I expect each commit to build but
have not checked it.

## 9. Environment diff (`envdiff.json`, `envdiff.txt`)

Base: dump of `bc0e235e` (above). After: the same command on the head.

```
constants before 39476 after 39476 (keys 39369 39369 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):      (none)
ambiguous module changes: 0
auxiliary constants that changed module: 1
VERDICT PASS
```

The one auxiliary move: `SingularMayerVietoris.stdVertices.eq_1` is now realized in
`Lib.AlgebraicTopology.Hurewicz.CubeTriangulation` instead of
`Lib.AlgebraicTopology.SingularHomology.CrossProduct.Affine` (an equation lemma is realized in the first
module that needs it; the import order changed). Same type, not a source declaration.

Reproduce: `python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_final.jsonl --receipt envdiff.json`
with both dumps made by the dump command of §2 at `bc0e235e` and at the head.

## 10. Left

- The 10 non-facades of §1 (`ThreeColumnPage`, `ThreeColumnSpectralSequence`, `SingularCochains`,
  `SingularCochains.DualEvaluation`, `SingularSmallChains.Barycentric`, `Abelian.RightDerived`,
  `Sheaves.ConstantPushforward`, `FiniteClosedPushforward`, `OpenRestriction`, `PrincipalCoverLocalSystem`)
  keep a module next to a same-named directory; whether to move their declarations into a piece is a
  separate decision. Reproduce: `for f in $(find Lib -name '*.lean'); do [ -d "${f%.lean}" ] && echo $f; done`.
- Per-commit builds of the 24 facade commits were not run (§8). Reproduce: `git rebase -x 'lake build Lib
  Solution Shared Center' bc0e235e` in a scratch worktree.
- The "better homes" of both MERGE receipts and the rename wave (NEXT_STEPS item 4, after this step) are
  not part of this task.
- `Lib.lean` remains unsorted as before; pieces sit where their facade line was.
