# Center/Proof and Shared/Proof: receipt

Seat: Claude Opus 5.5 (model ID `claude-opus-5-5`), work seat. Branch `fix/center-proof` in
`/home/goblin/hopf-fix-center`, base `b210042f`. Not merged into `lib/integration`.

Commits: `a460339b` (Center/Proof, first five moves), `6bcd3825` (first receipt), `4ae8b0ef`
(Shared/Proof, owner decision of 2026-10-02, plus the two Center moves it unblocked), `a212d624`
(SphereTwo docstring location), `7f4b883d` (receipt), `457b3861` (LatticeImageCollapse
Center → Shared), then this receipt.

## Layout

`Lib` (generic) ← `Shared/Proof` (used by both proofs) ← `Hopf/Proof` (old proof, frozen) and
`Center/Proof` (center construction only). `Shared` imports Mathlib and `Lib` only; `Hopf` and
`Center` may import `Shared`; `Hopf` and `Center` never import each other; `Lib` imports none of
them. `[[lean_lib]] name = "Center"` and `name = "Shared"` in `lakefile.toml`, roots `Center.lean`
and `Shared.lean` (each with a short module docstring stating the rule), neither in
`defaultTargets` (as `Hopf`). The axiom probes are `Center/Proof/AxiomAudit.lean` and
`Shared/Proof/AxiomAudit.lean`, imported by nothing. `Hopf/Proof/AxiomAudit.lean` lost its last
probe (`rotatedPrincipalRootFour_reverse_of_wedge`, now in Center) and was deleted as an empty
Hopf/Proof file. No other repository document lists the trees, so no other doc was edited.

## Final tree per file

| file at `b210042f` (Hopf/Proof/…) | decls | → Center/Proof | → Shared/Proof | stays Hopf/Proof | file afterwards |
|---|---|---|---|---|---|
| `Algebra/Group/LatticeImageCollapse.lean` | 14 | 0 | 14 | 0 | deleted |
| `Algebra/Group/ResidualRelations.lean` | 1 | 1 | 0 | 0 | deleted |
| `AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | 1 | 1 | 0 | 0 | deleted |
| `AlgebraicTopology/Hurewicz/DegreeSix.lean` | 21 | 0 | 4 | 17 | kept (cut) |
| `AlgebraicTopology/Hurewicz/SphereGenerator.lean` | 2 | 1 | 1 | 0 | deleted |
| `Analysis/Complex/RiemannMapping/SectorRoots.lean` | 28 | 2 | 21 | 5 | kept (cut) |
| `Analysis/Complex/RiemannMapping/TriangleNormalization.lean` | 17 | 0 | 13 | 4 | kept (cut) |
| `Data/Int/SignedResidual.lean` | 1 | 0 | 1 | 0 | deleted |
| `Geometry/Manifold/Morse/BeltCancellation.lean` | 10 | 0 | 0 | 10 | unchanged |
| `Geometry/Manifold/Morse/CutTransport.lean` | 42 | 0 | 0 | 42 | unchanged |
| `Geometry/Manifold/Morse/MiddleBlocks.lean` | 27 | 0 | 0 | 27 | unchanged |
| `Geometry/Manifold/Morse/MinimalSystem.lean` | 4 | 0 | 0 | 4 | unchanged |
| `Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` | 5 | 0 | 0 | 5 | unchanged |
| `Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` | 2 | 0 | 0 | 2 | unchanged |
| `Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` | 2 | 0 | 0 | 2 | unchanged |
| `Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` | 7 | 0 | 0 | 7 | unchanged |
| `Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` | 6 | 0 | 0 | 6 | unchanged |
| `Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` | 16 | 0 | 0 | 16 | unchanged |
| `Geometry/Manifold/Morse/SurgeryCollapse/OuterIndexMinimal.lean` | 1 | 0 | 0 | 1 | unchanged |
| `Geometry/Manifold/Morse/SurgeryHomology.lean` | 2 | 0 | 0 | 2 | unchanged |
| `GroupTheory/PresentedGroup/CentralTwist.lean` | 20 | 0 | 0 | 20 | unchanged |
| `Topology/Sheaves/Cohomology/SphereTwo.lean` | 4 | 4 | 0 | 0 | deleted |
| **total** | 233 | 9 | 54 | 170 | |

Plus the two anonymous `local instance`s of `SphereTwo.lean` (to Center). Structure fields and
auto-generated lemmas are not counted. Module docstrings of moved whole files are verbatim, except
the one location sentence of `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` l.36
(`Hopf/Proof/` → `Center/Proof/`). Each new file cut out of a Hopf file copies the Hopf file's
header (copyright, imports, module docstring, `open`s, `noncomputable section`, file-level
`set_option`s) and appends one sentence saying where it was moved from; the remaining Hopf files
gained one `import Shared.…` line and are otherwise only shorter. Importers fixed:
`Hopf/Proof/Final.lean` (four imports of the first Center moves dropped),
`Hopf/Proof/Recognition.lean` (`Hopf.Proof…SphereGenerator` → `Shared.Proof…SphereGenerator`),
`Hopf/Proof/LCP/IntegralHomology.lean` (`Hopf.Proof.Data.Int.SignedResidual` →
`Shared.Proof.Data.Int.SignedResidual`).

## Method

Owner's method: classify by git history, usage as cross-check.

- History: one pass of `git log --no-renames -p HEAD center-solution -- '*.lean'` (1890 commits),
  every added declaration line recorded by short name; the first addition (namespace-checked by
  hand where short names collide, e.g. `A1`, `gamma`, `epsilon`) is the introducing commit, the
  first addition at the current `Hopf/Proof` path the moving commit. Introducing commit CS-only
  (`22d23761..center-solution`; the center work starts at `ae2726db`, 2026-08-30) or an exact replay
  of one (same author date and subject) → **center**; otherwise → **old** (all of them trace to
  `cc698c96:Solution.lean`, through the rename `c6e63534` MorseCancel→MorseCancellation or the
  suffix strip `6e5c4c30` where those show up first, each checked by hand).
- Usage (a), old proof: Lean environment of every `Hopf/**`, `S6/**`, `Solution`, `S6Shortcuts`
  module, `getUsedConstants`, closed through the candidate files. Exact.
- Usage (b), W4W1: grep of `W4W1/**`, `W4W1.lean`, `W4-W1-Solution.lean` at `center-solution`,
  closed under the Lean dependency edges among candidates. Grep evidence, not a build.
- Tree: center history and no old-proof use → Center; used by both (a) and (b) → Shared; else Hopf.
  Both (a) and (b) are closed under dependencies, so Shared is closed (checked: the only edge from
  a Shared declaration to a Hopf one was `hurewiczLinearEquiv` → `hurewiczInverse._proof_1`, an
  auxiliary proof term Lean shares between the two definitions, not a real dependency; the build
  confirms).

### Corrections to the first report

- The "both" list had **43** entries, not 47 (arithmetic error in the first hand-back).
- Three of them were grep noise and stay in Hopf as old-only: `SixSphere` (`MinimalSystem.lean:50`;
  the W4W1 hit `W4W1/CenterNativeComplexAtlas.lean:85` resolves to `W4W1.SixSphere` of
  `W4W1/Worlds.lean:34`, because the use sits inside `namespace W4W1.CenterNativeComplexAtlas`),
  `TwistGroup` (`CentralTwist.lean:36`; the hit `W4W1/UnitVanKampenConsumer.lean:238` is the
  namespace prefix of `TwistGroup.main_realization_generators_eq_one`, an old-proof theorem of
  `Hopf/Proof/LCP/BoundaryTopology.lean`), and `twistRelators` (both only through `TwistGroup`).
  So Shared first received 43 − 3 = 40.
- `LatticeImageCollapse` (14) was first moved to Center and then, by the owner's decision, moved
  whole to `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` (`457b3861`): on
  `center-solution` the old-proof files `Hopf/Proof/FiniteCore.lean:65` and
  `Hopf/Proof/LCP/BoundaryTopology.lean` (l. 20664–20680) use the family too, so by the owner's
  rule it is used by both proofs. Shared now holds 54, Center 9.
- `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective`: history center (`ea3aa7d4` on CS,
  replay `35a7942e`), but `Hopf/Proof/Recognition.lean:405` (`sphereMap_piSix_bijective`) uses it,
  so it is "both" and went to **Shared**, by the owner's decision. It is one of the 40.

## Remaining history/usage disagreements (reported, not resolved)

1. `homotopyMap_bijective_of_homologyMap_bijective`: history center, in Shared (above).
2. `LatticeImageCollapse.*` (14, now **Shared**): history center (`74eae34b`, replay `49179556`),
   unused by our old proof, used by `W4W1/CenterNativeFundamentalGroup.lean`; on
   `center-solution` also used by the old-proof files `Hopf/Proof/FiniteCore.lean:65` and
   `Hopf/Proof/LCP/BoundaryTopology.lean` (l. 20664–20680; a CS-side rewiring never replayed here,
   our BoundaryTopology keeps its own `LatticeCuspNormalClosure.*`). Hence Shared, so that rewiring
   rebases as Hopf → Shared. The statements restate the old `Mathoverflow1973.LatticeCuspNormalClosure.*` of
   `cc698c96:Solution.lean` l. 211268–211320 under a new namespace.
3. `LatticeImageCollapse.image_firstBasis_eq` (Shared with its file): history center, usage neither.
4. `SixthHurewicz.hurewiczFunction` (`DegreeSix.lean:71`, Hopf): history old, usage W4W1 only
   (`W4W1/CenterResidualCharacter.lean:245`). Stays in Hopf per "old history stays"; note that
   W4W1 on CS imports `Hopf.Proof.*` anyway.
5. Old history, usage neither (stay in Hopf): `DegreeSix.lean` `cubeHomologyClass_homotopic`,
   `hurewiczPi6`, `hurewiczMap`, `hurewiczMap_representative`, `hurewiczInverse`,
   `hurewiczPi6Equiv`, `cubeChain_natural`, `cubeCycle_natural`, `cubeHomologyClass_natural`,
   `hurewiczFunction_natural`, `hurewiczMap_natural`.
6. Usage (b) counts direct W4W1 mentions only. W4W1 on `center-solution` also imports old-proof
   modules (`Hopf.Proof.LCP.*`, `Hopf.Proof.Recognition`), so it reaches many old declarations
   transitively; those are not counted as "both".

## IMPORT MAP for the rebase of `center-solution`

Names are unchanged; only module paths differ (CS = module on `center-solution` today).

| declarations | module on CS | module here |
|---|---|---|
| `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth` | `Lib.Algebra.Group.ResidualRelations` | `Center.Proof.Algebra.Group.ResidualRelations` |
| `LatticeImageCollapse.*` (14) | `Lib.Algebra.Group.LatticeImageCollapse` | `Shared.Proof.Algebra.Group.LatticeImageCollapse` |
| `FundamentalGroup.VanKampen.exists_stageCharacter` | `Lib.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter` | `Center.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter` |
| `TopCat.Sheaf.*_of_homeomorph_sphereTwo` (4) | `Lib.Topology.Sheaves.Cohomology.SphereTwo` | `Center.Proof.Topology.Sheaves.Cohomology.SphereTwo` |
| `RiemannBoundary.principalRoot_three_reverse_of_wedge`, `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | `Lib.Analysis.Complex.RiemannMapping` (l. 2418, 2515) | `Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots` |
| `SixthHurewicz.exists_sphereMap_of_homologySixEquiv` | `Lib.AlgebraicTopology.Hurewicz.SphereGenerator` | `Center.Proof.AlgebraicTopology.Hurewicz.SphereGenerator` |
| `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` | `Lib.AlgebraicTopology.Hurewicz.SphereGenerator` | `Shared.Proof.AlgebraicTopology.Hurewicz.SphereGenerator` |
| `SixthHurewicz.{cubeHomologyClass, homotopyMap, hurewiczLinearEquiv, hurewiczLinearEquiv_natural}` | `Lib.AlgebraicTopology.Hurewicz.DegreeSix` | `Shared.Proof.AlgebraicTopology.Hurewicz.DegreeSix` |
| `RiemannBoundary.{cubic_sector_slack, quartic_sector_slack, principalRoot_three_upper, quarticRootRotation, quarticRootRotation_re, quarticRootRotation_im, norm_quarticRootRotation, quarticRootRotation_pow_four, rotatedPrincipalRootFour, rotatedPrincipalRootFour_pow, rotatedPrincipalRootFour_zero, norm_rotatedPrincipalRootFour, rotatedPrincipalRootFour_re, rotatedPrincipalRootFour_im, rotatedPrincipalRootFour_re_add_im, rotatedPrincipalRootFour_upper, rotatedPrincipalRootFour_ofReal_nonneg_boundary, rotatedPrincipalRootFour_ofReal_nonpos_im, continuousOn_rotatedPrincipalRootFour_closedUpper, continuousAt_rotatedPrincipalRootFour_zero, analyticOnNhd_rotatedPrincipalRootFour_upper}` (21) | `Lib.Analysis.Complex.RiemannMapping` | `Shared.Proof.Analysis.Complex.RiemannMapping.SectorRoots` |
| `TriangleRiemannNormalization.{discCoordinate, discCoordinate_injective, discCoordinate_ne, discCoordinate_norm_le, punctureMap, punctureMap_isEmbedding, punctureMap_surjective, punctureHomeomorph, normalizationHomeomorph, normalizationHomeomorph_apply, normalizationHomeomorph_first, normalizationHomeomorph_second, normalizationHomeomorph_strict_iff}` (13) | `Lib.Analysis.Complex.RiemannMapping` | `Shared.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization` |
| `ThreefoldHomology.signed_residual_coordinate_zero` | `Lib.Data.Int.SignedResidual` | `Shared.Proof.Data.Int.SignedResidual` |

W4W1 importers on CS that change: `CenterNativeFundamentalGroup.lean` l. 9, 11, 13;
`CenterBaseCohomologicalDimension.lean` l. 1; `NativeCornerThree.lean` l. 1 and the
`NativeCornerFour` / `NativeMarkedNormalization` / `WorldCircuitCoreB` /
`CenterChargedAssembly` / `CenterResidualCharacter` import blocks (they reach the RiemannMapping,
DegreeSix, SphereGenerator and SignedResidual material through `Lib.*` today; here through
`Shared.Proof.*`, `Center.Proof.*`, or, for old-proof declarations, `Hopf.Proof.*`). The 34
Shared declarations from the CS monolith `Lib.Analysis.Complex.RiemannMapping` sit there next to
library material that stayed in `Lib.Analysis.Complex.RiemannMapping.*` here, so a CS file
importing the monolith may need both the `Lib` facade and the `Shared`/`Center` modules.
CS's `Hopf/Proof/FiniteCore.lean:65` import of `Lib.Algebra.Group.LatticeImageCollapse` becomes
`Shared.Proof.Algebra.Group.LatticeImageCollapse` (allowed: Hopf may import Shared).

The two anonymous `local instance`s of `SphereTwo.lean` get auto-generated names from the module
root (`…_hopf` before, `…_center` now); local and unreferenced.

### Facade dissolution (`work/facades`, receipt `Lib/reports/facades/RECEIPT.md`)

The import-only facade modules are deleted on this branch. Of the six facade names that `W4W1/` imports on
CS (7 import lines), two are deleted here; the other four are not facades on this branch (they carry
declarations next to their directory) and stay valid import targets.

| CS import line(s) | here | replace by |
|---|---|---|
| `W4W1/NativeCornerThree.lean:1` `import Lib.Analysis.Complex.RiemannMapping` | deleted | `Lib.Analysis.Complex.RiemannMapping.{Existence, DiscBoundaryEscape, HalfStripChart, RectanglePrimitive, ModulusOneReflection, BoundaryDerivative, ConformalExtension, PrincipalRoot, DiscCompactification}` (the nine imports of the deleted facade; the tenth piece, `.Steps`, comes in through `.Existence`) — plus the `Shared`/`Center` modules of the table above |
| `W4W1/CenterHigherNearbyComparison.lean:7`, `W4W1/CenterR1ZeroStalkCriterion.lean:1` `import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation` | deleted | `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive` (the facade's only import; all ten pieces of the directory are an acceptable superset) |
| `W4W1/Worlds.lean:8` `public import Lib.Algebra.Homology.ThreeColumnPage` | module with declarations | unchanged |
| `W4W1/CenterConstantPushforward.lean:8` `import Lib.Topology.Sheaves.ConstantPushforward` | module with declarations | unchanged |
| `W4W1/CenterCuspRegularCoordinateDisc.lean:8` `import Lib.Topology.Sheaves.OpenRestriction` | module with declarations | unchanged |
| `W4W1/CenterRegularH1LocalSystem.lean:8` `import Lib.Topology.Sheaves.PrincipalCoverLocalSystem` | module with declarations | unchanged |

The replacement lists are exactly the deleted facades' import lines, so a rebased W4W1 file sees the same
environment as through the facade here. Caveat: CS's own `Lib.Analysis.Complex.RiemannMapping` (the
monolith there) also imports `Mathlib`, `SchwarzReflection`, `Mobius` and `Instances.RiemannSphere`; the
facade here did not, independently of this dissolution.

### Better homes (`work/homes`, receipt `Lib/reports/homes/RECEIPT.md`)

Module paths only; declaration names unchanged. Command:
`git grep -nE '^(public )?import Lib\.' center-solution -- W4W1 W4W1.lean W4-W1-Solution.lean` (141 lines).

**No import line of `W4W1/`, `W4W1.lean` or `W4-W1-Solution.lean` names a moved module.** One entry of
the facade table above changes: in the replacement list for `W4W1/NativeCornerThree.lean:1`
(`import Lib.Analysis.Complex.RiemannMapping`), `Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection`
is now `Lib.Analysis.Complex.ModulusOneReflection`.

For future replays: none of the old module paths below exists on CS (they are pieces of this branch's
splits). The material lives on CS in the monolith of the second column; a replayed CS commit that edits
it, or a CS file that needs it, goes to the new module.

| moved here (old → new) | on CS inside |
|---|---|
| `Lib.AlgebraicTopology.SingularHomology.CrossProduct.HomologyDescent` (5 decls) → `Lib.AlgebraicTopology.SingularHomology.ModuleHomology` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` |
| `SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo`, `SingularChains.pointChain_mem_supported`: `…Hurewicz.CubeChainDecomposition.Concatenation` → `Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains` | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` |
| `SingularHomology.zeroSimplexValue_const`, `SingularHomology.crossProductZeroLeft_pointChain`: same → `Lib.AlgebraicTopology.SingularHomology.CrossProduct.Chain` | same |
| `SingularChains.inducedChain_pointChain`: same → `Lib.AlgebraicTopology.SingularHomology.Chains` | same |
| `Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents` → `Lib.AlgebraicTopology.SingularHomology.PathComponents` | `Lib.Geometry.Manifold.Morse.OrderedCancellation` |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall` → `Lib.AlgebraicTopology.SingularHomology.PuncturedBall` | `Lib.Geometry.Manifold.Morse.SurgeryCollapse` |
| `Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover` (14 decls) → `Lib.AlgebraicTopology.SingularHomology.OnePointCover` | `Lib.Geometry.Manifold.Morse.SurgeryCollapse` |
| `Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition` → `Lib.Analysis.SpecialFunctions.SmoothTransition` | `Lib.Geometry.Manifold.Morse.Rearrangement` |
| `Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality` → `Lib.Geometry.Manifold.Transversality.AmbientIsotopy` | `Lib.Geometry.Manifold.Morse.Rearrangement` |
| `Lib.Geometry.Manifold.Transversality.MorseBelt` → `Lib.Geometry.Manifold.Morse.MorseBelt` | `Lib.Geometry.Manifold.Transversality.Basic` |
| `Lib.Geometry.Manifold.Whitney.CleanStrips.BeltIntersection` → `Lib.Geometry.Manifold.Morse.BeltIntersection` | `Lib.Geometry.Manifold.Whitney.CleanStrips` |
| `Lib.Geometry.Manifold.Flow.HeightTranslating.{HandleCoordinates, DescentModel, AttachingUnion}` → `Lib.Geometry.Manifold.Morse.HandleAttachment.{HandleCoordinates, DescentModel, AttachingUnion}` | `Lib.Geometry.Manifold.Flow.HeightTranslating` |
| `Lib.Analysis.Calculus.MorseLemma.{LinearPerturbation, CriticalPoints, SignedMorseChart, SplitChart, DescentField, AdaptedDescentField}` → `Lib.Geometry.Manifold.Morse.<same>` | `Lib.Analysis.Calculus.MorseLemma` |
| `Lib.Analysis.Calculus.MorseLemma.Existence` → `Lib.Geometry.Manifold.Morse.Existence.MorseFunction` | `Lib.Analysis.Calculus.MorseLemma` |
| `Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection` → `Lib.Analysis.Complex.ModulusOneReflection` | `Lib.Analysis.Complex.RiemannMapping` |
| `Lib.Geometry.Manifold.Morse.Cubic.SublevelFlow` → `Lib.Dynamics.Flow.Sublevel` | `Lib.Geometry.Manifold.Morse.Cubic` |
| `Lib.Geometry.Manifold.Morse.Cubic.LocalReplacement` → `Lib.Geometry.Manifold.LocalReplacement` | `Lib.Geometry.Manifold.Morse.Cubic` |
| `Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation` → `Lib.Geometry.Manifold.SmoothApproximation` | `Lib.Geometry.Manifold.Morse.Existence` |
| `Lib.Geometry.Manifold.Collar.SphereCoordinates` (`SphereCoordinates.ofLinearIsometry`) → `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData` | `Lib.Geometry.Manifold.Collar` |

New module names here that did not exist before and do not exist on CS: the right-hand sides above except
`ModuleHomology`, `SmallChains`, `CrossProduct.Chain`, `Chains`, `SingularHomology.OnePointCover`,
`SurgeryData` (existing targets). `Lib.Geometry.Manifold.Morse.Existence` (a CS monolith, a dissolved
facade here) was deliberately not reused.

## Checks (head `457b3861` before this receipt)

Baseline before any edit, `b210042f`: `lake build Lib Unused Hopf.Proof.AxiomAudit` →
`Build completed successfully (9435 jobs).`, 0 errors, 40 probes (Hopf/Proof/AxiomAudit 6, Unused
34), all `[propext, Classical.choice, Quot.sound]`.

After the LatticeImageCollapse move to Shared, at `457b3861` (Lake pinned with `taskset -c 0-7`):

- `lake build Lib` → `Build completed successfully (9429 jobs).`
- `lake build Solution S6Shortcuts S6 Challenge` → `Build completed successfully (9489 jobs).`;
  `'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]`.
  Additionally every `Hopf/**` and `S6/**` module was built explicitly at `4ae8b0ef` (before this
  last move, which touches no Hopf file):
  `Build completed successfully (9490 jobs).`
- `lake build Shared` → `Build completed successfully (8803 jobs).`
- `lake build Center` → `Build completed successfully (8870 jobs).`
- `lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused` →
  `Build completed successfully (9443 jobs).`; probes Lib 3762, Shared 54, Center 7, Unused 34,
  total 3857, every one exactly `[propext, Classical.choice, Quot.sound]`.
  (`Hopf.Proof.AxiomAudit` no longer exists; see Layout.)
- `python3 scripts/lib_stock_census.py --check` → `stock declarations under Hopf/: 123`,
  `ratchet PASS: 123 <= baseline 1648` (unchanged).
- `grep -rnE '^(public )?import (Shared|Hopf|Center)' --include=*.lean Lib/` → empty (without
  `--include` there are 9 pre-existing hits in text logs under `Lib/docs/`, unchanged).
- `grep -rnE '^(public )?import (Hopf|Center)' Shared/ Shared.lean` → empty.
- `grep -rnE '^(public )?import Center' Hopf/ S6/ *.lean` (without `Center.lean`) → empty.
- `grep -rnE '^(public )?import Hopf' Center/ Center.lean` → empty.
- No `sorry`/`axiom` in `Shared/`, `Center/`, `Hopf/` (the only `sorry` in the tree is the
  statement in `Challenge.lean`, by design).


## Open items

1. `homotopyMap_bijective_of_homologyMap_bijective`: center history, in Shared because of the
   old-proof use.
2. (b) is grep evidence on `center-solution`, not a build of it; three grep hits were noise.
3. Remaining module docstrings of the cut Hopf files still describe the whole former file (e.g.
   `Hopf/Proof/…/SectorRoots.lean` still names `rotatedPrincipalRootFour`); left verbatim.

## Corrections (review 2026-10-04)

Review: `/home/goblin/.claude/jobs/06995e68/tmp/review-center/REVIEW.md` (Fable seat, findings F1–F7,
R1). Fixes on branch `fix/center-review` (Claude Opus 5.5, model ID `claude-opus-5-5`), base
`b25f3507`. The text above is left as written; these paragraphs supersede it where they disagree.

Correction (review 2026-10-04): F1. The appendix row "| 58 | `SixthHurewicz.cubeHomologyClass` | old
| … | both | SixSphereCube.factor_cubeHomologyClass @ Hopf.Recognition | W4W1/WorldCircuitCoreB.lean:45 |
**Shared** …" is wrong: `WorldCircuitCoreB.lean:45` mentions `Hurewicz.cubeHomologyClass` of `Lib`, not the
`SixthHurewicz` wrapper, and no `W4W1` file mentions the wrapper. The row is "old-only", final tree **Hopf**
`Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean`; moved back verbatim to its original position (before
`cubeHomologyClass_homotopic`) by `db37bd77`, its probe dropped from `Shared/Proof/AxiomAudit.lean`
(`Hopf/Proof` has no audit file; the Hopf `DegreeSix` declarations are probed nowhere). Counts: the table row
"`AlgebraicTopology/Hurewicz/DegreeSix.lean` | 21 | 0 | 4 | 17" is 21 | 0 | 3 | 18, and "**total** | 233 | 9 |
54 | 170" is 233 | 9 | **53** | **171**; "Shared now holds 54, Center 9" is Shared 53, Center 9. In the import
map, the row "`SixthHurewicz.{cubeHomologyClass, homotopyMap, hurewiczLinearEquiv,
hurewiczLinearEquiv_natural}`" loses `cubeHomologyClass` (it is an old-proof declaration in
`Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix` here, in `Lib.AlgebraicTopology.Hurewicz.DegreeSix` on CS).

Correction (review 2026-10-04): F2. "Names are unchanged; only module paths differ." is false for one name:
`Int.signed_residual_coordinate_zero` on `center-solution` (`Lib/Data/Int/SignedResidual.lean`,
`namespace Int`) is `ThreefoldHomology.signed_residual_coordinate_zero` here (renamed by the round-8 commit
`cd893c55`). The rebase therefore needs one identifier edit, not only an import edit:
`W4W1/CenterChargedAssembly.lean:1060` `exact Int.signed_residual_coordinate_zero k` →
`exact ThreefoldHomology.signed_residual_coordinate_zero k` (CS's
`Hopf/Proof/LCP/IntegralHomology.lean:23052` uses the `Int.` name too). All other moved names are
unchanged.

Correction (review 2026-10-04): F3. The row "| 71 | `SixthHurewicz.hurewiczFunction` | … | W4W1-only | — |
W4W1/CenterResidualCharacter.lean:245 | **Hopf** …" rests on a misresolved hit: that line uses
`SingularChains.hurewiczFunction` of `Lib`. The usage is "neither" (tree **Hopf** unchanged), and
disagreement item 4 ("`SixthHurewicz.hurewiczFunction` … usage W4W1 only") is withdrawn.

Correction (review 2026-10-04): F4. "The two anonymous `local instance`s of `SphereTwo.lean` get
auto-generated names from the module root (`…_hopf` before, `…_center` now); local and unreferenced." The
instances are referenced in the *types* of three of the four SphereTwo theorems, whose type hashes therefore
changed with identical text: `TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo`,
`TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo`,
`TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo`. The
cause is only the module-root suffix of the instance names (`_hopf` → `_center`; on `center-solution` they
end in `_lib`); the instances are the same terms. The rebase is not affected.

Correction (review 2026-10-04): F5. The importer paragraph ("W4W1 importers on CS that change: …") is
incomplete. Explicit import lines in `W4W1` on `center-solution` that name a mapped module (verified with
`git -C /home/goblin/hopf grep -nE '^(public )?import Lib…' center-solution -- W4W1`):
`CenterNativeFundamentalGroup.lean` l. 9 (`…VanKampen.FiniteStarCharacter`), 11
(`…LatticeImageCollapse`), 13 (`…ResidualRelations`); `CenterBaseCohomologicalDimension.lean` l. 1
(`…SphereTwo`); `NativeCornerThree.lean` l. 1 (`Lib.Analysis.Complex.RiemannMapping`); and
`WorldCircuitCoreB.lean` l. 10 `import Lib.AlgebraicTopology.Hurewicz.SphereGenerator` — a module that does
not exist here (hard import error, not a transitive reach), to be replaced by
`Shared.Proof.AlgebraicTopology.Hurewicz.SphereGenerator` and
`Center.Proof.AlgebraicTopology.Hurewicz.SphereGenerator`. (`W4-W1-Solution.lean:8` `import Lib` compiles
and the file uses no moved name.) Files that reach moved names only transitively and need an added import
or inherit one: `NativeCornerFour` (through `NativeCornerThree`; uses `rotatedPrincipalRootFour*`),
`NativeMarkedNormalization` and `NativeHalfFord` (Shared `TriangleNormalization`), `CenterChargedAssembly`
(Shared `SignedResidual`, reached through `Hopf.Proof.LCP.IntegralHomology`; only F2's rename remains).
`CenterResidualCharacter` needs no import edit on account of this split (F3).

Correction (review 2026-10-04): F7. "probes Lib 3762, Shared 54, Center 7, Unused 34, total 3857, every one
exactly `[propext, Classical.choice, Quot.sound]`": the axiom lists are all ⊆ {propext, Classical.choice,
Quot.sound} (of the 61 Shared/Center probes, 55 are the full list, 4 `[propext]`, 2 `[propext,
Quot.sound]`), not all exactly that list. After these fixes the counts are Shared 53, Center 9 (the two
missing Center probes, F6, added by `28d5127e`). Also "Each new file cut out of a Hopf file copies the
Hopf file's header … and appends one sentence": `Center/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`
has a rewritten module docstring; it now names both wedge reversals it holds (`87c166b8`, which also
rejoins the broken appended sentence of `Center/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean`).

Note (review 2026-10-04, R1, outside this receipt's scope): on `center-solution`, 21 files under `W4W1/`
plus `W4-W1-Solution.lean` (22 in all) import `Hopf.Proof.*` / `Hopf.*`, so `W4W1` as `Center/Proof` cannot
meet "`Center` never imports `Hopf`" by import-line edits alone; that is the owner's call. The files
(`git -C /home/goblin/hopf grep -lE '^(public )?import Hopf' center-solution -- W4W1 W4-W1-Solution.lean`):
`W4-W1-Solution.lean`, `W4W1/{CenterChargedAssembly, CenterCuspBase, CenterCuspGamma,
CenterCuspRadiusPreimage, CenterFamily, CenterFinitePatchBridge, CenterFiniteRadiusRetraction,
CenterH1CuspSpecialization, CenterHigherFiniteCoordinates, CenterPeriodicLoop, CenterR0H2Coordinate,
CenterRegularH1LocalSystem, CenterRegularH1Monodromy, CenterRegularHigherMonodromy, CenterResidualCharacter,
CenterSphereCohomology, ConcreteGammaConsumer, CoreAH1LocalSystem/DiagonalQuotientFibreMarking,
FreeCoverLift, UnitVanKampenConsumer, WorldCircuitCoreB}.lean`.

## Appendix: per-declaration classification and final tree

Lines refer to `b210042f`. "CS" hash = original commit on `center-solution`, the second hash its
replay here. Usage: (a) old proof, (b) W4W1 at `center-solution`.

#### `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean` — 14: 14 Shared

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 39 | `LatticeImageCollapse.A1` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:706 | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 43 | `LatticeImageCollapse.A2` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:750 | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 47 | `LatticeImageCollapse.epsilon` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 50 | `LatticeImageCollapse.epsilonPrime` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 53 | `LatticeImageCollapse.gamma` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 55 | `LatticeImageCollapse.image_eq_one_of_gamma_eq_zero` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 83 | `LatticeImageCollapse.image_eq_zpow_gamma` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:714 | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 110 | `LatticeImageCollapse.gamma_epsilonPrime` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 112 | `LatticeImageCollapse.image_epsilonPrime_eq` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 125 | `LatticeImageCollapse.image_firstBasis_eq` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | neither | — | — | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 138 | `LatticeImageCollapse.A1_fixes_epsilon` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 140 | `LatticeImageCollapse.image_epsilon_commute_first` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:730 | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 152 | `LatticeImageCollapse.A2_fixes_epsilonPrime` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |
| 154 | `LatticeImageCollapse.image_epsilon_commute_second` | center | `74eae34b` (CS) = `49179556` `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:758 | **Shared** `Shared/Proof/Algebra/Group/LatticeImageCollapse.lean` |

#### `Hopf/Proof/Algebra/Group/ResidualRelations.lean` — 1: 1 Center

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 29 | `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth` | center | `98594552` (CS) = `24513987` `Lib/Algebra/Group/ResidualRelations.lean` | `282ec4c1` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:1290 | **Center** `Center/Proof/Algebra/Group/ResidualRelations.lean` |

#### `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` — 1: 1 Center

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 31 | `FundamentalGroup.VanKampen.exists_stageCharacter` | center | `a39000b6` (CS) = `0e3e53c2` `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | `23f6eb4d` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:209 | **Center** `Center/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` |

#### `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` — 21: 4 Shared, 17 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 37 | `SixthHurewicz.fundamentalCubeChain` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 40 | `SixthHurewicz.cubeChain` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 44 | `SixthHurewicz.cubeChain_eq_induced` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 49 | `SixthHurewicz.cubeCycle` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeCycle @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 54 | `SixthHurewicz.cubeCycle_val` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeCycle @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 58 | `SixthHurewicz.cubeHomologyClass` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | SixSphereCube.factor_cubeHomologyClass @ Hopf.Recognition | W4W1/WorldCircuitCoreB.lean:45 | **Shared** `Shared/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 62 | `SixthHurewicz.cubeHomologyClass_homotopic` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 67 | `SixthHurewicz.homotopyMap` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | BasedDiskLifting.exists_based_disk_lift @ Hopf.Proof.Recognition | W4W1/WorldCircuitCoreB.lean:48 | **Shared** `Shared/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 71 | `SixthHurewicz.hurewiczFunction` | old | `cc698c96` `Solution.lean` | `ba11838f` | W4W1-only | — | W4W1/CenterResidualCharacter.lean:245 | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 75 | `SixthHurewicz.hurewiczPi6` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 79 | `SixthHurewicz.hurewiczMap` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 83 | `SixthHurewicz.hurewiczMap_representative` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 90 | `SixthHurewicz.hurewiczInverse` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 98 | `SixthHurewicz.hurewiczLinearEquiv` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv @ Hopf.Proof.Recognition | (transitive) | **Shared** `Shared/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 106 | `SixthHurewicz.hurewiczPi6Equiv` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 119 | `SixthHurewicz.cubeChain_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 124 | `SixthHurewicz.cubeCycle_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 131 | `SixthHurewicz.cubeHomologyClass_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 137 | `SixthHurewicz.hurewiczFunction_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 143 | `SixthHurewicz.hurewiczMap_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | **Hopf** `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |
| 149 | `SixthHurewicz.hurewiczLinearEquiv_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` |

#### `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` — 2: 1 Center, 1 Shared

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 40 | `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` | center | `ea3aa7d4` (CS) = `35a7942e` `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` | both | sphereMap_piSix_bijective @ Hopf.Proof.Recognition | (transitive) | **Shared** `Shared/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` |
| 83 | `SixthHurewicz.exists_sphereMap_of_homologySixEquiv` | center | `ea3aa7d4` (CS) = `35a7942e` `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` | W4W1-only | — | W4W1/WorldCircuitCoreB.lean:61 | **Center** `Center/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` |

#### `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` — 28: 2 Center, 21 Shared, 5 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 23 | `RiemannBoundary.cubic_sector_slack` | old | `6e5c4c30` `Lib/Analysis/Complex/RiemannMapping.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerThree.lean:265 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 35 | `RiemannBoundary.quartic_sector_slack` | old | `6e5c4c30` `Lib/Analysis/Complex/RiemannMapping.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 49 | `RiemannBoundary.principalRoot_three_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerThree.lean:254 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 70 | `RiemannBoundary.principalRoot_three_ofReal_nonneg_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 76 | `RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 89 | `RiemannBoundary.principalRoot_three_real_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 103 | `RiemannBoundary.principalRoot_three_reverse_of_wedge` | center | `b3f08b95` (CS) = `259b165e` `Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean` | `ff9dfc00` | W4W1-only | — | W4W1/NativeCornerThree.lean:909 | **Center** `Center/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 197 | `RiemannBoundary.quarticRootRotation` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerSectorFour_pow_im_pos @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 202 | `RiemannBoundary.quarticRootRotation_re` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 208 | `RiemannBoundary.quarticRootRotation_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 214 | `RiemannBoundary.norm_quarticRootRotation` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 218 | `RiemannBoundary.quarticRootRotation_ne_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.cornerSectorFour_root_pow @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 223 | `RiemannBoundary.quarticRootRotation_pow_four` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.quarticRootRotation_inv_mul_pow_four @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 233 | `RiemannBoundary.rotatedPrincipalRootFour` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:18 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 238 | `RiemannBoundary.rotatedPrincipalRootFour_pow` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_power @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:412 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 246 | `RiemannBoundary.rotatedPrincipalRootFour_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:358 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 251 | `RiemannBoundary.norm_rotatedPrincipalRootFour` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:295 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 257 | `RiemannBoundary.rotatedPrincipalRootFour_re` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 265 | `RiemannBoundary.rotatedPrincipalRootFour_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 273 | `RiemannBoundary.rotatedPrincipalRootFour_re_add_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 280 | `RiemannBoundary.rotatedPrincipalRootFour_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:312 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 306 | `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerFour.lean:322 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 312 | `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerFour.lean:341 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 321 | `RiemannBoundary.rotatedPrincipalRootFour_real_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 331 | `RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:430 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 336 | `RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:439 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 341 | `RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_analyticOnNhd @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:420 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |
| 350 | `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | center | `e238166c` (CS) = `044f1f68` `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` | `044f1f68` | W4W1-only | — | W4W1/NativeCornerFour.lean:755 | **Center** `Center/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` |

#### `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` — 17: 13 Shared, 4 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 25 | `TriangleRiemannNormalization.discCoordinate` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 30 | `TriangleRiemannNormalization.discCoordinate_injective` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 36 | `TriangleRiemannNormalization.discCoordinate_ne` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeMarkedNormalization.lean:95 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 41 | `TriangleRiemannNormalization.discCoordinate_norm_le` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 46 | `TriangleRiemannNormalization.punctureMap` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 52 | `TriangleRiemannNormalization.punctureMap_isEmbedding` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 67 | `TriangleRiemannNormalization.punctureMap_surjective` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 83 | `TriangleRiemannNormalization.punctureHomeomorph` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeMarkedNormalization.lean:108 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 89 | `TriangleRiemannNormalization.normalizationHomeomorph` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:50 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 103 | `TriangleRiemannNormalization.normalizationHomeomorph_apply` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_apply @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:138 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 118 | `TriangleRiemannNormalization.normalizationHomeomorph_first` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_centerOne @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:166 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 128 | `TriangleRiemannNormalization.normalizationHomeomorph_second` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_centerTwo @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:169 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 139 | `TriangleRiemannNormalization.normalizationHomeomorph_strict_iff` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:173 | **Shared** `Shared/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 155 | `TriangleRiemannNormalization.normalization_orientation_ne_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.normalizationOrientation_ne_zero @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 166 | `RiemannMapping.triangleSideParameter` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.exists_triangleMap_side_limits @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 170 | `RiemannMapping.triangleSideParameter_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.triangleSideBoundaryGerm_inverse_limit @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |
| 175 | `RiemannMapping.continuousAt_triangleSideParameter_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.triangleSideBoundaryGerm_inverse_limit @ Hopf.Proof.LCP.AnalyticFillings | — | **Hopf** `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` |

#### `Hopf/Proof/Data/Int/SignedResidual.lean` — 1: 1 Shared

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 26 | `ThreefoldHomology.signed_residual_coordinate_zero` | old | `cc698c96` `Solution.lean` | `cd893c55` | both | ThreefoldHomology.FifthDegree.fifthWangCoordinate_vanishes @ Hopf.Proof.LCP.IntegralHomology | W4W1/CenterChargedAssembly.lean:1060 | **Shared** `Shared/Proof/Data/Int/SignedResidual.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` — 10: 10 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 45 | `AdaptedWindows.belt_complement_reaches_lower_level` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_relative_family_lower_transport @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 73 | `AdaptedWindows.exists_belt_complement_lower_transport` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 109 | `MorseCancellation.lower_transport_upperMeridian_eq` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 126 | `AdaptedWindows.exists_lower_transport_with_meridians` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 147 | `AdaptedWindows.exists_lower_passage_homology_relation` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_passage_derivative_class_addition @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 200 | `MorseCancellation.radialParameterChart` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 217 | `MorseCancellation.radialParameterChart_zero_mem_source` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 231 | `MorseCancellation.radialParameterChart_zero` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 249 | `MorseCancellation.radialParameterChart_apply` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |
| 259 | `MorseCancellation.radialParameterChart_link` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` — 42: 42 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 77 | `AdaptedWindows.level_transport_homotopic_in_sublevel` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.native_attaching_class_of_flow_section @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 144 | `MorseCancellation.regular_sublevel_inclusion_bijective` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.middle_inclusion_step @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 160 | `MorseCancellation.canonicalMiddleMatrix` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 167 | `MorseCancellation.canonicalMiddleMatrix_equalCut` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 182 | `MorseCancellation.native_index_order_of_equal_index_exchange` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_middle_family_value_exchange @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 228 | `AdaptedWindows.backward_basin_reaches_intermediate_cut` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 246 | `AdaptedWindows.transported_basin_image_of_reaching` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 282 | `AdaptedWindows.upper_point_not_on_belt_of_lower_orbit` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 303 | `MorseCancellation.lower_backward_basins_preserved` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 375 | `MorseCancellation.lower_forward_basins_preserved` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 404 | `AdaptedWindows.reaches_cut_of_forward_holonomy` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 436 | `AdaptedWindows.section_class_of_flow_transport` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_lower_cut_geometric_matrix @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 460 | `MorseCancellation.signed_relation_of_regular_cut_transport` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_common_cut_prescribed_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 490 | `MorseCancellation.exists_sheet_arc_tube_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 540 | `MorseCancellation.exists_clean_sheet_arc_tube_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 633 | `MorseCancellation.exists_relative_sheet_passages_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 742 | `MorseCancellation.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 803 | `MorseCancellation.exists_centered_passage_clock` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 822 | `MorseCancellation.passageNormalProduct` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 826 | `MorseCancellation.passageNormalProduct_det` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 837 | `MorseCancellation.relative_normal_frame_det` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 859 | `MorseCancellation.passage_normal_relative_det_neg` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 872 | `MorseCancellation.mfderiv_normal_trace_model` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 898 | `MorseCancellation.LongitudinalTubeMotion.normal_trace_mfderiv` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 949 | `MorseCancellation.mfderiv_retime_unit_rate` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 982 | `MorseCancellation.fderiv_retimed_trace_parameter` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1011 | `MorseCancellation.exists_shared_passage_frames` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1044 | `MorseCancellation.CenteredSheetPassage` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1058 | `MorseCancellation.LongitudinalTubeMotion.centeredSheetPassage` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1088 | `MorseCancellation.bijective_trace_normal_of_native_transverse` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1114 | `MorseCancellation.hasFDerivAt_terminal_normal_factor` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1138 | `MorseCancellation.regular_below_pivot_of_regular_lower_band` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1151 | `MorseCancellation.lower_window_le_of_radius_le` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1159 | `MorseCancellation.common_cut_band_of_smaller_radius` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_repeatable_column_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1173 | `MorseCancellation.higher_window_separation_of_value_order` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_repeatable_column_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1180 | `MorseCancellation.canonicalMiddleMatrix_single_class_addition` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1199 | `MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1232 | `MorseCancellation.low_index_cut_of_preserved_other_values` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1259 | `MorseCancellation.regularCutHomologyEquiv` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_lower_cut_geometric_matrix @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1268 | `ManifoldMorse.MorseSurgeryData.instLocal1` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1273 | `MorseCancellation.consecutive_last_two_first_three` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | MorseCancellation.cancel_from_complete_middle_family @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |
| 1315 | `MorseCancellation.native_index_excluded_of_count_zero` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` — 27: 27 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 61 | `MorseCancellation.nativeMorseCount_eq_interval_length` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 97 | `MorseCancellation.native_middle_block_counts` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 143 | `AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 223 | `MorseCancellation.nativeIndexThreeAttachingSphere_regular` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 255 | `AdaptedWindows.exists_native_core_inclusion_equiv` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_core_inclusion_homology_comparison @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 279 | `MorseCancellation.nativeMiddleBaseCut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.canonical_middle_matrix_surjective @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 284 | `MorseCancellation.nativeMiddleCutSequence` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.middle_section_classes_span @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 291 | `MorseCancellation.nativeMiddleCutSequence_bands` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.ordered_middle_inclusion_relations @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 345 | `AdaptedWindows.no_connection_above_canonical_cut` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 390 | `MorseCancellation.lower_cuts_preserved_of_critical_bound` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 417 | `AdaptedWindows.exists_common_cut_value_exchange` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_middle_family_value_exchange @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 525 | `MorseCancellation.nativeMiddleBasinFamily_equalCut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 577 | `MorseCancellation.nativeMiddleBasinFamily_labels_injective` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 594 | `AdaptedWindows.backward_basin_reaches_compact_section` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 621 | `AdaptedWindows.exists_relative_surgery_cut_transport` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_relative_family_lower_transport @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 766 | `MorseCancellation.nativeMiddleBasinFamily_replace_zero` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_common_cut_prescribed_family_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 810 | `MorseCancellation.attaching_contributions_opposite_of_relative_det_neg` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.choose_prescribed_normal_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 835 | `MorseCancellation.exists_centered_passage_normal_factors` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 958 | `MorseCancellation.opposite_centered_passages_of_normal_factors` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1022 | `MorseCancellation.exists_native_opposite_centered_passages` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_native_prescribed_centered_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1076 | `MorseCancellation.nativeMiddleBasinFamily_reindex` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1090 | `MorseCancellation.native_middle_block_complete_and_cut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_native_belt_cut_family @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1165 | `ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1180 | `ManifoldMorse.MorseSurgeryData.exists_transverse_representative` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | MorseCancellation.exists_single_intersection_of_unit_coordinate @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1220 | `AdaptedWindows.cancel_single_basin_section_isotopy` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | MorseCancellation.cancel_from_preserved_unit_belt_cut @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1340 | `MorseCancellation.middle_blocks_complete_of_no_four_five` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.ordered_no_middle_indices_count_two @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |
| 1382 | `MorseCancellation.critical_pair_of_surgery_count_two` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` — 4: 4 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 50 | `SixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | noise (W4W1/CenterNativeComplexAtlas.lean:85) | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` |
| 53 | `simplyConnectedSpace_of_homotopySixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` |
| 58 | `pathConnectedSpace_of_homotopySixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` |
| 63 | `homotopySixSphere_homology_subsingleton` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` — 5: 5 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 40 | `MorseCancellation.nativeIndexThreeAttachingSphere` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` |
| 53 | `MorseCancellation.IsNativeMiddleBasinFamily` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` |
| 68 | `MorseCancellation.outer_index_minimality_neg` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.outer_index_minimal_outer_counts_zero @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` |
| 102 | `MorseCancellation.exists_middle_index_blocks` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` |
| 178 | `MorseCancellation.nativeMiddleBlockPoint` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.canonical_middle_matrix_surjective @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` — 2: 2 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 30 | `AdaptedWindows.pathConnectedSpace_middle_level` | old | `cc698c96` `Solution.lean` | `7747b4d3` | old-only | MorseCancellation.exists_native_middle_level_circle_isotopy @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` |
| 46 | `AdaptedWindows.pathConnectedSpace_index_three_upper_level` | old | `cc698c96` `Solution.lean` | `7747b4d3` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` — 2: 2 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 33 | `MorseCancellation.exists_sheet_arc_tube` | old | `c6e63534` `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | `2b1157f7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` |
| 136 | `MorseCancellation.exists_clean_two_sheet_arc_avoiding` | old | `c6e63534` `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | `2b1157f7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` — 7: 7 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 50 | `ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 112 | `MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices` | old | `c6e63534` `Hopf/SphereTopology.lean` | `0a2c13b6` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 155 | `ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 206 | `ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 270 | `ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 336 | `ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_single_intersection_of_unit_coordinate @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |
| 376 | `AdaptedWindows.exists_transverse_middle_belt_loop` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_handle_trade_transverse_level_data @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` — 6: 6 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 42 | `AdaptedWindows.exists_middle_family_descent` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |
| 126 | `AdaptedWindows.exists_middle_family_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |
| 245 | `AdaptedWindows.exists_regular_band_middle_basin_family` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.exists_common_cut_prescribed_slide @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |
| 266 | `AdaptedWindows.exists_middle_basin_family_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |
| 296 | `AdaptedWindows.exists_middle_block_realization` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |
| 420 | `AdaptedWindows.exists_ordered_middle_family` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.minimal_ordered_index_two_count_zero @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` — 16: 16 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 38 | `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 46 | `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 56 | `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 74 | `ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 92 | `ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 109 | `ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 135 | `ManifoldMorse.SurgeryWindows.indexTwoBasis_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 170 | `ManifoldMorse.SurgeryWindows.indexTwoBasis` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 194 | `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.middle_inclusion_step @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 201 | `ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 214 | `ManifoldMorse.MorseSurgeryData.coreBoundary_two_range` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.native_index_three_inclusion_relation @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 242 | `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 257 | `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 265 | `ManifoldMorse.MorseSurgeryData.indexThreePresentation` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 278 | `ManifoldMorse.SurgeryWindows.middlePresentation` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |
| 299 | `ManifoldMorse.SurgeryWindows.middleMatrix` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_bijective_of_complete_blocks @ Hopf.Proof.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/OuterIndexMinimal.lean` — 1: 1 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 35 | `MorseCancellation.exists_outer_index_minimal_ordered_morse_system` | old | `c6e63534` `Hopf/SphereTopology.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/OuterIndexMinimal.lean` |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryHomology.lean` — 2: 2 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 83 | `ManifoldMorse.MorseSurgeryData.upperLevelInclusion` | old | `cc698c96` `Solution.lean` | `efce6afa` | old-only | ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count @ Hopf.Recognition | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryHomology.lean` |
| 90 | `ManifoldMorse.SurgeryWindows.lastUpperHomeomorph` | old | `cc698c96` `Solution.lean` | `efce6afa` | old-only | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | — | **Hopf** `Hopf/Proof/Geometry/Manifold/Morse/SurgeryHomology.lean` |

#### `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` — 20: 20 Hopf

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 29 | `twistRelators` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | noise ((transitive)) | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 36 | `TwistGroup` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | noise (W4W1/UnitVanKampenConsumer.lean:238) | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 40 | `TwistGroup.c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 44 | `TwistGroup.x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 48 | `TwistGroup.y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 52 | `TwistGroup.c_commute_x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 56 | `TwistGroup.x_mul_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 60 | `TwistGroup.x_cube` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 64 | `TwistGroup.y_fourth` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 68 | `TwistGroup.x_commute_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 77 | `TwistGroup.x_fourth` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 88 | `TwistGroup.x_eq_c_power` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 98 | `TwistGroup.y_eq_c_power` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 108 | `TwistGroup.generated_by_c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_group_trivial @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 124 | `TwistGroup.realizationImages` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 128 | `TwistGroup.realizationImages_relators` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 136 | `TwistGroup.realizationHom` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 143 | `TwistGroup.realizationHom_c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 150 | `TwistGroup.realizationHom_x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |
| 157 | `TwistGroup.realizationHom_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | **Hopf** `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` |

#### `Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` — 4: 4 Center

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) | evidence (b) | final tree |
|---|---|---|---|---|---|---|---|---|
| 66 | `TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo` | center | `61de5232` (CS) = `cf943cab` `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:43 | **Center** `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` |
| 112 | `TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo` | center | `c0786d53` (CS) = `f778d0e3` `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:102 | **Center** `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` |
| 141 | `TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo` | center | `03f30fb5` (CS) = `27eb3fac` `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:77 | **Center** `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` |
| 157 | `TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo` | center | `03f30fb5` (CS) = `27eb3fac` `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:62 | **Center** `Center/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` |
