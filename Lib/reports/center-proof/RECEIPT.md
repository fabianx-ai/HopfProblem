# Center/Proof: receipt

Seat: Claude Opus 5.5 (model ID `claude-opus-5-5`), work seat. Branch `fix/center-proof` in
`/home/goblin/hopf-fix-center`, base `b210042f`. Not merged into `lib/integration`.

## What was done

New tree `Center/` (`[[lean_lib]] name = "Center"` in `lakefile.toml`, root `Center.lean`; not
in `defaultTargets`, same as `Hopf`). Moved verbatim out of `Hopf/Proof/` (commit `a460339b`):

| from (Hopf/Proof) | to (Center/Proof) | declarations |
|---|---|---|
| `Algebra/Group/ResidualRelations.lean` (whole file, deleted from Hopf) | `Algebra/Group/ResidualRelations.lean` | 1 |
| `Algebra/Group/LatticeImageCollapse.lean` (whole file, deleted from Hopf) | `Algebra/Group/LatticeImageCollapse.lean` | 14 |
| `AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` (whole file, deleted) | same path | 1 |
| `Topology/Sheaves/Cohomology/SphereTwo.lean` (whole file, deleted) | same path | 4 theorems + 2 anonymous `local instance`s |
| `Analysis/Complex/RiemannMapping/SectorRoots.lean` (one theorem, file stays) | `Analysis/Complex/RiemannMapping/SectorRoots.lean` (new file: header, imports, `open`, `noncomputable section` copied; new 4-line module docstring) | 1 (`RiemannBoundary.principalRoot_three_reverse_of_wedge`) |

Total: 21 named declarations + 2 anonymous local instances. Importer fixes: `Hopf/Proof/Final.lean`
drops its four imports of the moved whole files (they were there only so the files got built; no
declaration of the old proof uses them). The five probes of the moved declarations move from
`Hopf/Proof/AxiomAudit.lean` to the new `Center/Proof/AxiomAudit.lean` (not imported by
`Center.lean`, like the Hopf one); the Hopf docstring now names only the one remaining probe
(`rotatedPrincipalRootFour_reverse_of_wedge`) and points to the Center file. `Center.lean`
carries a short module docstring stating the tree's rule; no other repository document lists the
trees (README.md, AGENTS.md, Lib/README.md and Unused/README.md each describe only their own
tree), so no further documentation was edited.

Not done, by the brief's "no other cleanup": module docstrings of the moved files are verbatim and
some now say the wrong place (`SphereTwo.lean` l.35–36 "it lives under `Hopf/Proof/`"; the moved
files' "Moved out of `Lib/...`" notes are still true).

## Method

Owner's method (mid-task change): classify by git history, usage as cross-check.

- History: one pass of `git log --no-renames -p HEAD center-solution -- '*.lean'` (1890 commits),
  recording every added declaration line by short name; the first addition of the declaration
  (namespace-checked by hand where short names collide, e.g. `A1`, `gamma`, `epsilon`) is the
  introducing commit, the first addition at its current `Hopf/Proof` path on our branch is the
  moving commit. Introducing commits were sorted into: CS-only (`22d23761..center-solution`,
  i.e. the center work, which starts with `ae2726db` on 2026-08-30) or an exact replay of one
  (same author date and subject) → **center**; otherwise (initial `cc698c96` `Solution.lean`,
  the `MorseCancel`→`MorseCancellation` rename `c6e63534` and the suffix strip `6e5c4c30`, each
  verified to have the declaration already in `cc698c96:Solution.lean`) → **old**.
- Usage (a): Lean environment of every `Hopf/**`, `S6/**`, `Solution`, `S6Shortcuts` module
  (`Challenge` is the bare statement, imports only Mathlib); `getUsedConstants` of every constant,
  closure through the 22 candidate files. Usage (b): text grep of `W4W1/**`, `W4W1.lean`,
  `W4-W1-Solution.lean` at `center-solution` (full names; short names only when ≥ 14 chars),
  closed under the Lean dependency edges among the candidates. (b) is grep evidence, not a build.
- No declaration with history "generic Lib material introduced on the master line" was found:
  every one is either center-introduced or already in `cc698c96`.

## Classification summary per file

| file (Hopf/Proof/…) | decls | history center | history old | moved | usage both | usage neither |
|---|---|---|---|---|---|---|
| `Algebra/Group/LatticeImageCollapse.lean` | 14 | 14 | 0 | 14 | 0 | 1 |
| `Algebra/Group/ResidualRelations.lean` | 1 | 1 | 0 | 1 | 0 | 0 |
| `AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | 1 | 1 | 0 | 1 | 0 | 0 |
| `AlgebraicTopology/Hurewicz/DegreeSix.lean` | 21 | 0 | 21 | 0 | 4 | 11 |
| `AlgebraicTopology/Hurewicz/SphereGenerator.lean` | 2 | 2 | 0 | 0 | 1 | 0 |
| `Analysis/Complex/RiemannMapping/SectorRoots.lean` | 28 | 2 | 26 | 1 | 21 | 0 |
| `Analysis/Complex/RiemannMapping/TriangleNormalization.lean` | 17 | 0 | 17 | 0 | 13 | 0 |
| `Data/Int/SignedResidual.lean` | 1 | 0 | 1 | 0 | 1 | 0 |
| `Geometry/Manifold/Morse/BeltCancellation.lean` | 10 | 0 | 10 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/CutTransport.lean` | 42 | 0 | 42 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/MiddleBlocks.lean` | 27 | 0 | 27 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/MinimalSystem.lean` | 4 | 0 | 4 | 0 | 1 | 0 |
| `Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` | 5 | 0 | 5 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` | 2 | 0 | 2 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` | 2 | 0 | 2 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` | 7 | 0 | 7 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` | 6 | 0 | 6 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` | 16 | 0 | 16 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/SurgeryCollapse/OuterIndexMinimal.lean` | 1 | 0 | 1 | 0 | 0 | 0 |
| `Geometry/Manifold/Morse/SurgeryHomology.lean` | 2 | 0 | 2 | 0 | 0 | 0 |
| `GroupTheory/PresentedGroup/CentralTwist.lean` | 20 | 0 | 20 | 0 | 2 | 0 |
| `Topology/Sheaves/Cohomology/SphereTwo.lean` | 4 | 4 | 0 | 4 | 0 | 0 |
| **total** | 233 | 24 | 209 | 21 | 43 | 12 |

(Structure fields of `MorseCancellation.CenteredSheetPassage` and auto-generated equation lemmas
are not counted; the two anonymous local instances of `SphereTwo.lean` are counted separately.)

## History center but NOT moved (blocked, or usage disagrees) — open items

| declaration | file:line | history | usage | why not moved |
|---|---|---|---|---|
| `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean:252` (after the cut) | `e238166c` (CS) = `044f1f68` (ours, integration 7 replay, written straight into Hopf/Proof) | W4W1 only (`W4W1/NativeCornerFour.lean:755`, `:762`) | depends on `RiemannBoundary.rotatedPrincipalRootFour` and `RiemannBoundary.quarticRootRotation`, which are old (cc698c96) and used by the old proof (`SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero` etc. in `Hopf/Proof/LCP/AnalyticFillings`). Moving it would make `Center` import `Hopf`. |
| `SixthHurewicz.exists_sphereMap_of_homologySixEquiv` | `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean:83` | `ea3aa7d4` (CS) = `35a7942e` (ours), moved into Hopf/Proof by `ba11838f` | W4W1 only (`W4W1/WorldCircuitCoreB.lean:61`) | depends on `homotopyMap_bijective_of_homologyMap_bijective` (below, used by old proof) and on old `DegreeSix` declarations (`homotopyMap`, `hurewiczLinearEquiv`, `hurewiczLinearEquiv_natural`). |
| `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` | `…/Hurewicz/SphereGenerator.lean:40` | `ea3aa7d4` (CS) = `35a7942e` (ours): written on CS as a generalisation of the proof of `sphereMap_piSix_bijective`, and that same commit rewired `Hopf/Proof/Recognition.lean` to use it | **both**: (a) `sphereMap_piSix_bijective` @ `Hopf/Proof/Recognition.lean:405`; (b) transitively via the line above | history says center, usage says old proof. Not resolved. |

`SphereGenerator.lean` therefore stays whole in `Hopf/Proof`.

## Disagreements between history and usage (reported, not resolved)

1. `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` — history center, used by the old
   proof (see above).
2. `LatticeImageCollapse.*` (14, moved) — history center (file created by `74eae34b`
   "feat(Lib): add lattice image collapse and commutations", replay `49179556`), unused by the old
   proof on our branch, used by `W4W1/CenterNativeFundamentalGroup.lean` (706, 714, 728, 730, 750,
   758). But on `center-solution` the *old-proof* files `Hopf/Proof/FiniteCore.lean:65` and
   `Hopf/Proof/LCP/BoundaryTopology.lean` (l. 20664–20680) import/use
   `Lib.Algebra.Group.LatticeImageCollapse` (a CS-side rewiring that was never replayed here; our
   `BoundaryTopology` keeps its own `LatticeCuspNormalClosure.*` copies). After the rebase those
   CS commits would need `Hopf` → `Center`, which is forbidden; they must keep the local copies.
   The statements also duplicate the old `Mathoverflow1973.LatticeCuspNormalClosure.*` family of
   `cc698c96:Solution.lean` (l. 211268–211320) in a new namespace.
3. `LatticeImageCollapse.image_firstBasis_eq` (moved) — history center, usage neither (no
   consumer in W4W1 or the old proof; it has no `LatticeCuspNormalClosure` counterpart).
4. `SixthHurewicz.hurewiczFunction` (`DegreeSix.lean:71`) — history old (`cc698c96`), usage W4W1
   only (`W4W1/CenterResidualCharacter.lean:245`). Stays.
5. Old history, usage neither (stay): `DegreeSix.lean` `cubeHomologyClass_homotopic` (62),
   `hurewiczPi6` (75), `hurewiczMap` (79), `hurewiczMap_representative` (83), `hurewiczInverse`
   (90), `hurewiczPi6Equiv` (106), `cubeChain_natural` (119), `cubeCycle_natural` (124),
   `cubeHomologyClass_natural` (131), `hurewiczFunction_natural` (137), `hurewiczMap_natural` (143).
6. Brief's "known case" `TriangleNormalization.lean` and the `rotatedPrincipalRootFour*` family of
   `SectorRoots.lean`: history old (all in `cc698c96:Solution.lean`) and usage **both**
   (`Hopf/Proof/LCP/AnalyticFillings` and `W4W1/NativeMarkedNormalization.lean`,
   `W4W1/NativeCornerFour.lean`). They stay; see the "both" list.

## "Both" list (old history, used by the old proof and by W4W1) — not moved

Evidence: (a) first old-proof consumer from the Lean environment, (b) first W4W1 grep hit at
`center-solution` ("transitive" = only through another listed declaration).

- `SixthHurewicz.cubeHomologyClass` (AlgebraicTopology/Hurewicz/DegreeSix.lean:58): (a) SixSphereCube.factor_cubeHomologyClass @ Hopf.Recognition; (b) W4W1/WorldCircuitCoreB.lean:45
- `SixthHurewicz.homotopyMap` (AlgebraicTopology/Hurewicz/DegreeSix.lean:67): (a) BasedDiskLifting.exists_based_disk_lift @ Hopf.Proof.Recognition; (b) W4W1/WorldCircuitCoreB.lean:48
- `SixthHurewicz.hurewiczLinearEquiv` (AlgebraicTopology/Hurewicz/DegreeSix.lean:98): (a) SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv @ Hopf.Proof.Recognition; (b) (transitive)
- `SixthHurewicz.hurewiczLinearEquiv_natural` (AlgebraicTopology/Hurewicz/DegreeSix.lean:149): (a) (transitive); (b) (transitive)
- `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` (AlgebraicTopology/Hurewicz/SphereGenerator.lean:40): (a) sphereMap_piSix_bijective @ Hopf.Proof.Recognition; (b) (transitive)
- `RiemannBoundary.cubic_sector_slack` (Analysis/Complex/RiemannMapping/SectorRoots.lean:23): (a) (transitive); (b) W4W1/NativeCornerThree.lean:265
- `RiemannBoundary.quartic_sector_slack` (Analysis/Complex/RiemannMapping/SectorRoots.lean:35): (a) (transitive); (b) (transitive)
- `RiemannBoundary.principalRoot_three_upper` (Analysis/Complex/RiemannMapping/SectorRoots.lean:49): (a) SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerThree.lean:254
- `RiemannBoundary.quarticRootRotation` (Analysis/Complex/RiemannMapping/SectorRoots.lean:197): (a) SpecialPeriods.Triangle.cornerSectorFour_pow_im_pos @ Hopf.Proof.LCP.AnalyticFillings; (b) (transitive)
- `RiemannBoundary.quarticRootRotation_re` (Analysis/Complex/RiemannMapping/SectorRoots.lean:202): (a) (transitive); (b) (transitive)
- `RiemannBoundary.quarticRootRotation_im` (Analysis/Complex/RiemannMapping/SectorRoots.lean:208): (a) (transitive); (b) (transitive)
- `RiemannBoundary.norm_quarticRootRotation` (Analysis/Complex/RiemannMapping/SectorRoots.lean:214): (a) (transitive); (b) (transitive)
- `RiemannBoundary.quarticRootRotation_pow_four` (Analysis/Complex/RiemannMapping/SectorRoots.lean:223): (a) SpecialPeriods.Triangle.quarticRootRotation_inv_mul_pow_four @ Hopf.Proof.LCP.AnalyticFillings; (b) (transitive)
- `RiemannBoundary.rotatedPrincipalRootFour` (Analysis/Complex/RiemannMapping/SectorRoots.lean:233): (a) SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:18
- `RiemannBoundary.rotatedPrincipalRootFour_pow` (Analysis/Complex/RiemannMapping/SectorRoots.lean:238): (a) SpecialPeriods.Triangle.cornerParameterFour_power @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:412
- `RiemannBoundary.rotatedPrincipalRootFour_zero` (Analysis/Complex/RiemannMapping/SectorRoots.lean:246): (a) SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:358
- `RiemannBoundary.norm_rotatedPrincipalRootFour` (Analysis/Complex/RiemannMapping/SectorRoots.lean:251): (a) SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:295
- `RiemannBoundary.rotatedPrincipalRootFour_re` (Analysis/Complex/RiemannMapping/SectorRoots.lean:257): (a) (transitive); (b) (transitive)
- `RiemannBoundary.rotatedPrincipalRootFour_im` (Analysis/Complex/RiemannMapping/SectorRoots.lean:265): (a) (transitive); (b) (transitive)
- `RiemannBoundary.rotatedPrincipalRootFour_re_add_im` (Analysis/Complex/RiemannMapping/SectorRoots.lean:273): (a) (transitive); (b) (transitive)
- `RiemannBoundary.rotatedPrincipalRootFour_upper` (Analysis/Complex/RiemannMapping/SectorRoots.lean:280): (a) SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:312
- `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary` (Analysis/Complex/RiemannMapping/SectorRoots.lean:306): (a) (transitive); (b) W4W1/NativeCornerFour.lean:322
- `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im` (Analysis/Complex/RiemannMapping/SectorRoots.lean:312): (a) (transitive); (b) W4W1/NativeCornerFour.lean:341
- `RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper` (Analysis/Complex/RiemannMapping/SectorRoots.lean:331): (a) SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:430
- `RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero` (Analysis/Complex/RiemannMapping/SectorRoots.lean:336): (a) SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:439
- `RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper` (Analysis/Complex/RiemannMapping/SectorRoots.lean:341): (a) SpecialPeriods.Triangle.cornerParameterFour_analyticOnNhd @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeCornerFour.lean:420
- `TriangleRiemannNormalization.discCoordinate` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:25): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings; (b) (transitive)
- `TriangleRiemannNormalization.discCoordinate_injective` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:30): (a) (transitive); (b) (transitive)
- `TriangleRiemannNormalization.discCoordinate_ne` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:36): (a) (transitive); (b) W4W1/NativeMarkedNormalization.lean:95
- `TriangleRiemannNormalization.discCoordinate_norm_le` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:41): (a) (transitive); (b) (transitive)
- `TriangleRiemannNormalization.punctureMap` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:46): (a) (transitive); (b) (transitive)
- `TriangleRiemannNormalization.punctureMap_isEmbedding` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:52): (a) (transitive); (b) (transitive)
- `TriangleRiemannNormalization.punctureMap_surjective` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:67): (a) (transitive); (b) (transitive)
- `TriangleRiemannNormalization.punctureHomeomorph` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:83): (a) (transitive); (b) W4W1/NativeMarkedNormalization.lean:108
- `TriangleRiemannNormalization.normalizationHomeomorph` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:89): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeMarkedNormalization.lean:50
- `TriangleRiemannNormalization.normalizationHomeomorph_apply` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:103): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph_apply @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeMarkedNormalization.lean:138
- `TriangleRiemannNormalization.normalizationHomeomorph_first` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:118): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph_centerOne @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeMarkedNormalization.lean:166
- `TriangleRiemannNormalization.normalizationHomeomorph_second` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:128): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph_centerTwo @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeMarkedNormalization.lean:169
- `TriangleRiemannNormalization.normalizationHomeomorph_strict_iff` (Analysis/Complex/RiemannMapping/TriangleNormalization.lean:139): (a) RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings; (b) W4W1/NativeMarkedNormalization.lean:173
- `ThreefoldHomology.signed_residual_coordinate_zero` (Data/Int/SignedResidual.lean:26): (a) ThreefoldHomology.FifthDegree.fifthWangCoordinate_vanishes @ Hopf.Proof.LCP.IntegralHomology; (b) W4W1/CenterChargedAssembly.lean:1060
- `SixSphere` (Geometry/Manifold/Morse/MinimalSystem.lean:50): (a) ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology; (b) W4W1/CenterNativeComplexAtlas.lean:85
- `twistRelators` (GroupTheory/PresentedGroup/CentralTwist.lean:29): (a) TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology; (b) (transitive)
- `TwistGroup` (GroupTheory/PresentedGroup/CentralTwist.lean:36): (a) TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology; (b) W4W1/UnitVanKampenConsumer.lean:238

## IMPORT MAP for the rebase of `center-solution`

Names are unchanged; only module paths differ. (CS = `center-solution`, module as it is there today.)

| declaration | module on CS | module here |
|---|---|---|
| `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth` | `Lib.Algebra.Group.ResidualRelations` | `Center.Proof.Algebra.Group.ResidualRelations` |
| `LatticeImageCollapse.*` (all 14: `A1`, `A2`, `epsilon`, `epsilonPrime`, `gamma`, `image_eq_one_of_gamma_eq_zero`, `image_eq_zpow_gamma`, `gamma_epsilonPrime`, `image_epsilonPrime_eq`, `image_firstBasis_eq`, `A1_fixes_epsilon`, `image_epsilon_commute_first`, `A2_fixes_epsilonPrime`, `image_epsilon_commute_second`) | `Lib.Algebra.Group.LatticeImageCollapse` | `Center.Proof.Algebra.Group.LatticeImageCollapse` |
| `FundamentalGroup.VanKampen.exists_stageCharacter` | `Lib.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter` | `Center.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter` |
| `TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo`, `…hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo`, `…higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo`, `…higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo` | `Lib.Topology.Sheaves.Cohomology.SphereTwo` | `Center.Proof.Topology.Sheaves.Cohomology.SphereTwo` |
| `RiemannBoundary.principalRoot_three_reverse_of_wedge` | `Lib.Analysis.Complex.RiemannMapping` (monolith on CS, l. 2418) | `Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots` |
| (not moved) `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | `Lib.Analysis.Complex.RiemannMapping` (l. 2515) | `Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots` (unchanged) |

Importers on CS that change: `W4W1/CenterNativeFundamentalGroup.lean` l. 9, 11, 13;
`W4W1/CenterBaseCohomologicalDimension.lean` l. 1; `W4W1/NativeCornerThree.lean` l. 1 (add
`Center.Proof.Analysis.Complex.RiemannMapping.SectorRoots`). Conflict to expect:
`Hopf/Proof/FiniteCore.lean:65` on CS imports `Lib.Algebra.Group.LatticeImageCollapse` (see
disagreement 2). CS's `Lib.lean` lines 2, 4, 147, 425 and the CS `Lib/AxiomAudit.lean` probes of
these declarations drop out.

The two anonymous `local instance`s of `SphereTwo.lean` get auto-generated names from the module
root: `…_hopf` before, `…_center` now (`instAdditiveSheafOpensCarrierGrothendieckTopologyAddCommGrpCatObjOppositeFunctorSheafSectionsOpTop_center`,
`instHasExtSheafOpensCarrierGrothendieckTopologyAddCommGrpCat_center`). They are local and
referenced by no one.

## Checks (head after the move commit `a460339b`)

Baseline before editing, `b210042f`: `lake build Lib Unused Hopf.Proof.AxiomAudit` →
`Build completed successfully (9435 jobs).`, 0 errors, 40 probes (Hopf/Proof/AxiomAudit 6,
Unused 34), all `[propext, Classical.choice, Quot.sound]`. (`Lib.AxiomAudit` is not part of
`lake build Lib`.)

After the move:

- `lake build Lib` → `Build completed successfully (9429 jobs).`
- `lake build Solution S6Shortcuts S6 Challenge` → `Build completed successfully (9486 jobs).`;
  `'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `lake build Center` → `Build completed successfully (8780 jobs).`
- `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit Center.Proof.AxiomAudit Unused` →
  `Build completed successfully (9437 jobs).`; probes: Lib/AxiomAudit 3762, Hopf/Proof/AxiomAudit 1,
  Center/Proof/AxiomAudit 5, Unused 34; total 3802, every one `[propext, Classical.choice, Quot.sound]`.
- `python3 scripts/lib_stock_census.py --check` → `stock declarations under Hopf/: 123`,
  `ratchet PASS: 123 <= baseline 1648` (unchanged).
- `grep -rnE '^(public )?import (Hopf|Center)' Lib/` → no `.lean` hit; 9 pre-existing hits in
  text logs under `Lib/docs/` (`*.lean.txt`, `*.md`), unchanged from `b210042f`.
- `grep -rnE '^(public )?import Hopf' Center/ Center.lean` → empty.
- `grep -rnE '^(public )?import Center' Hopf/ S6/ *.lean` (without `Center.lean`) → empty.
- `sorry`/`axiom`: none in `Center/`, `Center.lean` or the edited Hopf files (the only `sorry` in
  the tree is the statement in `Challenge.lean`, by design).
- Warnings: the moved cube-root theorem keeps its two pre-existing linter suggestions
  (`Try simp at hi`), now at `Center/…/SectorRoots.lean:55,63`.

## Open items

1. The two blocked center declarations (`rotatedPrincipalRootFour_reverse_of_wedge`,
   `exists_sphereMap_of_homologySixEquiv`) need an owner decision: their old-proof dependencies
   are used by both proofs, so they can only move if those dependencies move to `Lib` (or the
   rule changes).
2. `homotopyMap_bijective_of_homologyMap_bijective`: center history, old-proof use.
3. `LatticeImageCollapse` on CS is also consumed by CS's old-proof files (rebase conflict).
4. Moved-file docstrings that still say `Hopf/Proof/` (left verbatim per the brief).
5. (b) is grep evidence on `center-solution`, not a build of it.

## Appendix: per-declaration classification

Lines refer to `b210042f`. "CS" hash = original commit on `center-solution`, "ours" = its replay here.

#### `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean` — 14: 13 moved (W4W1-only), 1 moved (neither)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 39 | `LatticeImageCollapse.A1` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:706 | **moved** |
| 43 | `LatticeImageCollapse.A2` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:750 | **moved** |
| 47 | `LatticeImageCollapse.epsilon` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 50 | `LatticeImageCollapse.epsilonPrime` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 53 | `LatticeImageCollapse.gamma` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 55 | `LatticeImageCollapse.image_eq_one_of_gamma_eq_zero` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 83 | `LatticeImageCollapse.image_eq_zpow_gamma` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:714 | **moved** |
| 110 | `LatticeImageCollapse.gamma_epsilonPrime` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 112 | `LatticeImageCollapse.image_epsilonPrime_eq` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 125 | `LatticeImageCollapse.image_firstBasis_eq` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | neither | — | — | **moved** |
| 138 | `LatticeImageCollapse.A1_fixes_epsilon` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 140 | `LatticeImageCollapse.image_epsilon_commute_first` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:730 | **moved** |
| 152 | `LatticeImageCollapse.A2_fixes_epsilonPrime` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | (transitive) | **moved** |
| 154 | `LatticeImageCollapse.image_epsilon_commute_second` | center | `74eae34b` (CS) = `49179556` (ours) `Lib/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:758 | **moved** |

#### `Hopf/Proof/Algebra/Group/ResidualRelations.lean` — 1: 1 moved (W4W1-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 29 | `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth` | center | `98594552` (CS) = `24513987` (ours) `Lib/Algebra/Group/ResidualRelations.lean` | `282ec4c1` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:1290 | **moved** |

#### `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` — 1: 1 moved (W4W1-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 31 | `FundamentalGroup.VanKampen.exists_stageCharacter` | center | `a39000b6` (CS) = `0e3e53c2` (ours) `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | `23f6eb4d` | W4W1-only | — | W4W1/CenterNativeFundamentalGroup.lean:209 | **moved** |

#### `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` — 21: 1 stays (W4W1-only), 4 stays (both), 11 stays (neither), 5 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 37 | `SixthHurewicz.fundamentalCubeChain` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | stays |
| 40 | `SixthHurewicz.cubeChain` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | stays |
| 44 | `SixthHurewicz.cubeChain_eq_induced` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeChain @ Hopf.Recognition | — | stays |
| 49 | `SixthHurewicz.cubeCycle` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeCycle @ Hopf.Recognition | — | stays |
| 54 | `SixthHurewicz.cubeCycle_val` | old | `cc698c96` `Solution.lean` | `ba11838f` | old-only | SixSphereCube.factor_cubeCycle @ Hopf.Recognition | — | stays |
| 58 | `SixthHurewicz.cubeHomologyClass` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | SixSphereCube.factor_cubeHomologyClass @ Hopf.Recognition | W4W1/WorldCircuitCoreB.lean:45 | stays |
| 62 | `SixthHurewicz.cubeHomologyClass_homotopic` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 67 | `SixthHurewicz.homotopyMap` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | BasedDiskLifting.exists_based_disk_lift @ Hopf.Proof.Recognition | W4W1/WorldCircuitCoreB.lean:48 | stays |
| 71 | `SixthHurewicz.hurewiczFunction` | old | `cc698c96` `Solution.lean` | `ba11838f` | W4W1-only | — | W4W1/CenterResidualCharacter.lean:245 | stays |
| 75 | `SixthHurewicz.hurewiczPi6` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 79 | `SixthHurewicz.hurewiczMap` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 83 | `SixthHurewicz.hurewiczMap_representative` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 90 | `SixthHurewicz.hurewiczInverse` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 98 | `SixthHurewicz.hurewiczLinearEquiv` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv @ Hopf.Proof.Recognition | (transitive) | stays |
| 106 | `SixthHurewicz.hurewiczPi6Equiv` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 119 | `SixthHurewicz.cubeChain_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 124 | `SixthHurewicz.cubeCycle_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 131 | `SixthHurewicz.cubeHomologyClass_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 137 | `SixthHurewicz.hurewiczFunction_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 143 | `SixthHurewicz.hurewiczMap_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | neither | — | — | stays |
| 149 | `SixthHurewicz.hurewiczLinearEquiv_natural` | old | `cc698c96` `Solution.lean` | `ba11838f` | both | (transitive) | (transitive) | stays |

#### `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` — 2: 1 stays (W4W1-only), 1 stays (both)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 40 | `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective` | center | `ea3aa7d4` (CS) = `35a7942e` (ours) `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` | both | sphereMap_piSix_bijective @ Hopf.Proof.Recognition | (transitive) | stays |
| 83 | `SixthHurewicz.exists_sphereMap_of_homologySixEquiv` | center | `ea3aa7d4` (CS) = `35a7942e` (ours) `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` | W4W1-only | — | W4W1/WorldCircuitCoreB.lean:61 | stays |

#### `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` — 28: 1 moved (W4W1-only), 1 stays (W4W1-only), 21 stays (both), 5 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 23 | `RiemannBoundary.cubic_sector_slack` | old | `6e5c4c30` `Lib/Analysis/Complex/RiemannMapping.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerThree.lean:265 | stays |
| 35 | `RiemannBoundary.quartic_sector_slack` | old | `6e5c4c30` `Lib/Analysis/Complex/RiemannMapping.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 49 | `RiemannBoundary.principalRoot_three_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerThree.lean:254 | stays |
| 70 | `RiemannBoundary.principalRoot_three_ofReal_nonneg_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | (transitive) | — | stays |
| 76 | `RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | (transitive) | — | stays |
| 89 | `RiemannBoundary.principalRoot_three_real_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 103 | `RiemannBoundary.principalRoot_three_reverse_of_wedge` | center | `b3f08b95` (CS) = `259b165e` (ours) `Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean` | `ff9dfc00` | W4W1-only | — | W4W1/NativeCornerThree.lean:909 | **moved** |
| 197 | `RiemannBoundary.quarticRootRotation` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerSectorFour_pow_im_pos @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | stays |
| 202 | `RiemannBoundary.quarticRootRotation_re` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 208 | `RiemannBoundary.quarticRootRotation_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 214 | `RiemannBoundary.norm_quarticRootRotation` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 218 | `RiemannBoundary.quarticRootRotation_ne_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.cornerSectorFour_root_pow @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 223 | `RiemannBoundary.quarticRootRotation_pow_four` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.quarticRootRotation_inv_mul_pow_four @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | stays |
| 233 | `RiemannBoundary.rotatedPrincipalRootFour` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:18 | stays |
| 238 | `RiemannBoundary.rotatedPrincipalRootFour_pow` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_power @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:412 | stays |
| 246 | `RiemannBoundary.rotatedPrincipalRootFour_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:358 | stays |
| 251 | `RiemannBoundary.norm_rotatedPrincipalRootFour` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:295 | stays |
| 257 | `RiemannBoundary.rotatedPrincipalRootFour_re` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 265 | `RiemannBoundary.rotatedPrincipalRootFour_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 273 | `RiemannBoundary.rotatedPrincipalRootFour_re_add_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 280 | `RiemannBoundary.rotatedPrincipalRootFour_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:312 | stays |
| 306 | `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerFour.lean:322 | stays |
| 312 | `RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeCornerFour.lean:341 | stays |
| 321 | `RiemannBoundary.rotatedPrincipalRootFour_real_boundary` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 331 | `RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_continuousOn @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:430 | stays |
| 336 | `RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:439 | stays |
| 341 | `RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | SpecialPeriods.Triangle.cornerParameterFour_analyticOnNhd @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeCornerFour.lean:420 | stays |
| 350 | `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | center | `e238166c` (CS) = `044f1f68` (ours) `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` | `044f1f68` | W4W1-only | — | W4W1/NativeCornerFour.lean:755 | stays |

#### `Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization.lean` — 17: 13 stays (both), 4 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 25 | `TriangleRiemannNormalization.discCoordinate` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings | (transitive) | stays |
| 30 | `TriangleRiemannNormalization.discCoordinate_injective` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 36 | `TriangleRiemannNormalization.discCoordinate_ne` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeMarkedNormalization.lean:95 | stays |
| 41 | `TriangleRiemannNormalization.discCoordinate_norm_le` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 46 | `TriangleRiemannNormalization.punctureMap` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 52 | `TriangleRiemannNormalization.punctureMap_isEmbedding` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 67 | `TriangleRiemannNormalization.punctureMap_surjective` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | (transitive) | stays |
| 83 | `TriangleRiemannNormalization.punctureHomeomorph` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | (transitive) | W4W1/NativeMarkedNormalization.lean:108 | stays |
| 89 | `TriangleRiemannNormalization.normalizationHomeomorph` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:50 | stays |
| 103 | `TriangleRiemannNormalization.normalizationHomeomorph_apply` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_apply @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:138 | stays |
| 118 | `TriangleRiemannNormalization.normalizationHomeomorph_first` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_centerOne @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:166 | stays |
| 128 | `TriangleRiemannNormalization.normalizationHomeomorph_second` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_centerTwo @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:169 | stays |
| 139 | `TriangleRiemannNormalization.normalizationHomeomorph_strict_iff` | old | `cc698c96` `Solution.lean` | `8e8fe025` | both | RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff @ Hopf.Proof.LCP.AnalyticFillings | W4W1/NativeMarkedNormalization.lean:173 | stays |
| 155 | `TriangleRiemannNormalization.normalization_orientation_ne_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.normalizationOrientation_ne_zero @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 166 | `RiemannMapping.triangleSideParameter` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.exists_triangleMap_side_limits @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 170 | `RiemannMapping.triangleSideParameter_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.triangleSideBoundaryGerm_inverse_limit @ Hopf.Proof.LCP.AnalyticFillings | — | stays |
| 175 | `RiemannMapping.continuousAt_triangleSideParameter_zero` | old | `cc698c96` `Solution.lean` | `8e8fe025` | old-only | RiemannMapping.triangleSideBoundaryGerm_inverse_limit @ Hopf.Proof.LCP.AnalyticFillings | — | stays |

#### `Hopf/Proof/Data/Int/SignedResidual.lean` — 1: 1 stays (both)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 26 | `ThreefoldHomology.signed_residual_coordinate_zero` | old | `cc698c96` `Solution.lean` | `cd893c55` | both | ThreefoldHomology.FifthDegree.fifthWangCoordinate_vanishes @ Hopf.Proof.LCP.IntegralHomology | W4W1/CenterChargedAssembly.lean:1060 | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean` — 10: 10 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 45 | `AdaptedWindows.belt_complement_reaches_lower_level` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_relative_family_lower_transport @ Hopf.Recognition | — | stays |
| 73 | `AdaptedWindows.exists_belt_complement_lower_transport` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | (transitive) | — | stays |
| 109 | `MorseCancellation.lower_transport_upperMeridian_eq` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | (transitive) | — | stays |
| 126 | `AdaptedWindows.exists_lower_transport_with_meridians` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | (transitive) | — | stays |
| 147 | `AdaptedWindows.exists_lower_passage_homology_relation` | old | `cc698c96` `Solution.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_passage_derivative_class_addition @ Hopf.Recognition | — | stays |
| 200 | `MorseCancellation.radialParameterChart` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | stays |
| 217 | `MorseCancellation.radialParameterChart_zero_mem_source` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | stays |
| 231 | `MorseCancellation.radialParameterChart_zero` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | stays |
| 249 | `MorseCancellation.radialParameterChart_apply` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | (transitive) | — | stays |
| 259 | `MorseCancellation.radialParameterChart_link` | old | `c6e63534` `Hopf/SingularHomology.lean` | `1a7358c0` | old-only | MorseCancellation.exists_radial_link_meridian_with_derivative @ Hopf.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` — 42: 42 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 77 | `AdaptedWindows.level_transport_homotopic_in_sublevel` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.native_attaching_class_of_flow_section @ Hopf.Recognition | — | stays |
| 144 | `MorseCancellation.regular_sublevel_inclusion_bijective` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.middle_inclusion_step @ Hopf.Recognition | — | stays |
| 160 | `MorseCancellation.canonicalMiddleMatrix` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | stays |
| 167 | `MorseCancellation.canonicalMiddleMatrix_equalCut` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | stays |
| 182 | `MorseCancellation.native_index_order_of_equal_index_exchange` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_middle_family_value_exchange @ Hopf.Recognition | — | stays |
| 228 | `AdaptedWindows.backward_basin_reaches_intermediate_cut` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | stays |
| 246 | `AdaptedWindows.transported_basin_image_of_reaching` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | stays |
| 282 | `AdaptedWindows.upper_point_not_on_belt_of_lower_orbit` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | stays |
| 303 | `MorseCancellation.lower_backward_basins_preserved` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 375 | `MorseCancellation.lower_forward_basins_preserved` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 404 | `AdaptedWindows.reaches_cut_of_forward_holonomy` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 436 | `AdaptedWindows.section_class_of_flow_transport` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_lower_cut_geometric_matrix @ Hopf.Recognition | — | stays |
| 460 | `MorseCancellation.signed_relation_of_regular_cut_transport` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_common_cut_prescribed_slide @ Hopf.Recognition | — | stays |
| 490 | `MorseCancellation.exists_sheet_arc_tube_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 540 | `MorseCancellation.exists_clean_sheet_arc_tube_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 633 | `MorseCancellation.exists_relative_sheet_passages_with_normal_change` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 742 | `MorseCancellation.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 803 | `MorseCancellation.exists_centered_passage_clock` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 822 | `MorseCancellation.passageNormalProduct` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 826 | `MorseCancellation.passageNormalProduct_det` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 837 | `MorseCancellation.relative_normal_frame_det` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 859 | `MorseCancellation.passage_normal_relative_det_neg` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 872 | `MorseCancellation.mfderiv_normal_trace_model` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 898 | `MorseCancellation.LongitudinalTubeMotion.normal_trace_mfderiv` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 949 | `MorseCancellation.mfderiv_retime_unit_rate` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 982 | `MorseCancellation.fderiv_retimed_trace_parameter` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1011 | `MorseCancellation.exists_shared_passage_frames` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1044 | `MorseCancellation.CenteredSheetPassage` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | stays |
| 1058 | `MorseCancellation.LongitudinalTubeMotion.centeredSheetPassage` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1088 | `MorseCancellation.bijective_trace_normal_of_native_transverse` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1114 | `MorseCancellation.hasFDerivAt_terminal_normal_factor` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1138 | `MorseCancellation.regular_below_pivot_of_regular_lower_band` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |
| 1151 | `MorseCancellation.lower_window_le_of_radius_le` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | stays |
| 1159 | `MorseCancellation.common_cut_band_of_smaller_radius` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_repeatable_column_slide @ Hopf.Recognition | — | stays |
| 1173 | `MorseCancellation.higher_window_separation_of_value_order` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_repeatable_column_slide @ Hopf.Recognition | — | stays |
| 1180 | `MorseCancellation.canonicalMiddleMatrix_single_class_addition` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | stays |
| 1199 | `MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | stays |
| 1232 | `MorseCancellation.low_index_cut_of_preserved_other_values` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | stays |
| 1259 | `MorseCancellation.regularCutHomologyEquiv` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | AdaptedWindows.exists_lower_cut_geometric_matrix @ Hopf.Recognition | — | stays |
| 1268 | `ManifoldMorse.MorseSurgeryData.instLocal1` | old | `cc698c96` `Solution.lean` | `8c6fbde4` | old-only | ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward @ Hopf.Recognition | — | stays |
| 1273 | `MorseCancellation.consecutive_last_two_first_three` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | MorseCancellation.cancel_from_complete_middle_family @ Hopf.Recognition | — | stays |
| 1315 | `MorseCancellation.native_index_excluded_of_count_zero` | old | `c6e63534` `Hopf/Recognition.lean` | `8c6fbde4` | old-only | (transitive) | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` — 27: 27 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 61 | `MorseCancellation.nativeMorseCount_eq_interval_length` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | stays |
| 97 | `MorseCancellation.native_middle_block_counts` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | stays |
| 143 | `AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | stays |
| 223 | `MorseCancellation.nativeIndexThreeAttachingSphere_regular` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | stays |
| 255 | `AdaptedWindows.exists_native_core_inclusion_equiv` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_core_inclusion_homology_comparison @ Hopf.Recognition | — | stays |
| 279 | `MorseCancellation.nativeMiddleBaseCut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.canonical_middle_matrix_surjective @ Hopf.Proof.Recognition | — | stays |
| 284 | `MorseCancellation.nativeMiddleCutSequence` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.middle_section_classes_span @ Hopf.Proof.Recognition | — | stays |
| 291 | `MorseCancellation.nativeMiddleCutSequence_bands` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.ordered_middle_inclusion_relations @ Hopf.Recognition | — | stays |
| 345 | `AdaptedWindows.no_connection_above_canonical_cut` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | (transitive) | — | stays |
| 390 | `MorseCancellation.lower_cuts_preserved_of_critical_bound` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | stays |
| 417 | `AdaptedWindows.exists_common_cut_value_exchange` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_middle_family_value_exchange @ Hopf.Recognition | — | stays |
| 525 | `MorseCancellation.nativeMiddleBasinFamily_equalCut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | stays |
| 577 | `MorseCancellation.nativeMiddleBasinFamily_labels_injective` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_first_middle_pivot @ Hopf.Recognition | — | stays |
| 594 | `AdaptedWindows.backward_basin_reaches_compact_section` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_higher_middle_family @ Hopf.Recognition | — | stays |
| 621 | `AdaptedWindows.exists_relative_surgery_cut_transport` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | AdaptedWindows.exists_relative_family_lower_transport @ Hopf.Recognition | — | stays |
| 766 | `MorseCancellation.nativeMiddleBasinFamily_replace_zero` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_common_cut_prescribed_family_slide @ Hopf.Recognition | — | stays |
| 810 | `MorseCancellation.attaching_contributions_opposite_of_relative_det_neg` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.choose_prescribed_normal_passage @ Hopf.Recognition | — | stays |
| 835 | `MorseCancellation.exists_centered_passage_normal_factors` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | stays |
| 958 | `MorseCancellation.opposite_centered_passages_of_normal_factors` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | (transitive) | — | stays |
| 1022 | `MorseCancellation.exists_native_opposite_centered_passages` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_native_prescribed_centered_passage @ Hopf.Recognition | — | stays |
| 1076 | `MorseCancellation.nativeMiddleBasinFamily_reindex` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | AdaptedWindows.exists_labelled_integer_slide @ Hopf.Recognition | — | stays |
| 1090 | `MorseCancellation.native_middle_block_complete_and_cut` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_native_belt_cut_family @ Hopf.Recognition | — | stays |
| 1165 | `ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count @ Hopf.Recognition | — | stays |
| 1180 | `ManifoldMorse.MorseSurgeryData.exists_transverse_representative` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | MorseCancellation.exists_single_intersection_of_unit_coordinate @ Hopf.Recognition | — | stays |
| 1220 | `AdaptedWindows.cancel_single_basin_section_isotopy` | old | `cc698c96` `Solution.lean` | `c356eb79` | old-only | MorseCancellation.cancel_from_preserved_unit_belt_cut @ Hopf.Recognition | — | stays |
| 1340 | `MorseCancellation.middle_blocks_complete_of_no_four_five` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.ordered_no_middle_indices_count_two @ Hopf.Proof.Recognition | — | stays |
| 1382 | `MorseCancellation.critical_pair_of_surgery_count_two` | old | `c6e63534` `Hopf/Recognition.lean` | `c356eb79` | old-only | MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere @ Hopf.Proof.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean` — 4: 1 stays (both), 3 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 50 | `SixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | both | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | W4W1/CenterNativeComplexAtlas.lean:85 | stays |
| 53 | `simplyConnectedSpace_of_homotopySixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | (transitive) | — | stays |
| 58 | `pathConnectedSpace_of_homotopySixSphere` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere @ Hopf.Proof.Recognition | — | stays |
| 63 | `homotopySixSphere_homology_subsingleton` | old | `cc698c96` `Solution.lean` | `5d75d095` | old-only | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean` — 5: 5 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 40 | `MorseCancellation.nativeIndexThreeAttachingSphere` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | AdaptedWindows.exists_canonical_basin_sphere @ Hopf.Recognition | — | stays |
| 53 | `MorseCancellation.IsNativeMiddleBasinFamily` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | AdaptedWindows.exists_arbitrary_column_addition @ Hopf.Recognition | — | stays |
| 68 | `MorseCancellation.outer_index_minimality_neg` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.outer_index_minimal_outer_counts_zero @ Hopf.SphereTopology | — | stays |
| 102 | `MorseCancellation.exists_middle_index_blocks` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | stays |
| 178 | `MorseCancellation.nativeMiddleBlockPoint` | old | `c6e63534` `Hopf/SphereTopology.lean` | `01c6893b` | old-only | MorseCancellation.canonical_middle_matrix_surjective @ Hopf.Proof.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` — 2: 2 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 30 | `AdaptedWindows.pathConnectedSpace_middle_level` | old | `cc698c96` `Solution.lean` | `7747b4d3` | old-only | MorseCancellation.exists_native_middle_level_circle_isotopy @ Hopf.SphereTopology | — | stays |
| 46 | `AdaptedWindows.pathConnectedSpace_index_three_upper_level` | old | `cc698c96` `Solution.lean` | `7747b4d3` | old-only | AdaptedWindows.exists_higher_family_prescribed_passage @ Hopf.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` — 2: 2 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 33 | `MorseCancellation.exists_sheet_arc_tube` | old | `c6e63534` `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | `2b1157f7` | old-only | (transitive) | — | stays |
| 136 | `MorseCancellation.exists_clean_two_sheet_arc_avoiding` | old | `c6e63534` `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | `2b1157f7` | old-only | (transitive) | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/BeltIntersections.lean` — 7: 7 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 50 | `ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 112 | `MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices` | old | `c6e63534` `Hopf/SphereTopology.lean` | `0a2c13b6` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | stays |
| 155 | `ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 206 | `ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 270 | `ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 336 | `ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_single_intersection_of_unit_coordinate @ Hopf.Recognition | — | stays |
| 376 | `AdaptedWindows.exists_transverse_middle_belt_loop` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_handle_trade_transverse_level_data @ Hopf.SphereTopology | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddleFamilies.lean` — 6: 6 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 42 | `AdaptedWindows.exists_middle_family_descent` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 126 | `AdaptedWindows.exists_middle_family_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 245 | `AdaptedWindows.exists_regular_band_middle_basin_family` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.exists_common_cut_prescribed_slide @ Hopf.Recognition | — | stays |
| 266 | `AdaptedWindows.exists_middle_basin_family_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 296 | `AdaptedWindows.exists_middle_block_realization` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 420 | `AdaptedWindows.exists_ordered_middle_family` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.minimal_ordered_index_two_count_zero @ Hopf.Proof.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/MiddlePresentation.lean` — 16: 16 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 38 | `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count @ Hopf.Recognition | — | stays |
| 46 | `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | MorseCancellation.last_index_two_collapse_is_primitive @ Hopf.Recognition | — | stays |
| 56 | `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 74 | `ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 92 | `ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 109 | `ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 135 | `ManifoldMorse.SurgeryWindows.indexTwoBasis_step` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 170 | `ManifoldMorse.SurgeryWindows.indexTwoBasis` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third @ Hopf.Recognition | — | stays |
| 194 | `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.middle_inclusion_step @ Hopf.Recognition | — | stays |
| 201 | `ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | (transitive) | — | stays |
| 214 | `ManifoldMorse.MorseSurgeryData.coreBoundary_two_range` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | AdaptedWindows.native_index_three_inclusion_relation @ Hopf.Recognition | — | stays |
| 242 | `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | stays |
| 257 | `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | stays |
| 265 | `ManifoldMorse.MorseSurgeryData.indexThreePresentation` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective @ Hopf.Recognition | — | stays |
| 278 | `ManifoldMorse.SurgeryWindows.middlePresentation` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third @ Hopf.Recognition | — | stays |
| 299 | `ManifoldMorse.SurgeryWindows.middleMatrix` | old | `cc698c96` `Solution.lean` | `0a2c13b6` | old-only | ManifoldMorse.SurgeryWindows.middleMatrix_bijective_of_complete_blocks @ Hopf.Proof.Recognition | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/OuterIndexMinimal.lean` — 1: 1 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 35 | `MorseCancellation.exists_outer_index_minimal_ordered_morse_system` | old | `c6e63534` `Hopf/SphereTopology.lean` | `0a2c13b6` | old-only | MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices @ Hopf.SphereTopology | — | stays |

#### `Hopf/Proof/Geometry/Manifold/Morse/SurgeryHomology.lean` — 2: 2 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 83 | `ManifoldMorse.MorseSurgeryData.upperLevelInclusion` | old | `cc698c96` `Solution.lean` | `efce6afa` | old-only | ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count @ Hopf.Recognition | — | stays |
| 90 | `ManifoldMorse.SurgeryWindows.lastUpperHomeomorph` | old | `cc698c96` `Solution.lean` | `efce6afa` | old-only | ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton @ Hopf.SphereTopology | — | stays |

#### `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` — 20: 2 stays (both), 18 stays (old-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 29 | `twistRelators` | old | `cc698c96` `Solution.lean` | `b5767bb7` | both | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | (transitive) | stays |
| 36 | `TwistGroup` | old | `cc698c96` `Solution.lean` | `b5767bb7` | both | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | W4W1/UnitVanKampenConsumer.lean:238 | stays |
| 40 | `TwistGroup.c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 44 | `TwistGroup.x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 48 | `TwistGroup.y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 52 | `TwistGroup.c_commute_x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 56 | `TwistGroup.x_mul_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 60 | `TwistGroup.x_cube` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 64 | `TwistGroup.y_fourth` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 68 | `TwistGroup.x_commute_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 77 | `TwistGroup.x_fourth` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 88 | `TwistGroup.x_eq_c_power` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.c_twistOrder @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 98 | `TwistGroup.y_eq_c_power` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 108 | `TwistGroup.generated_by_c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_group_trivial @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 124 | `TwistGroup.realizationImages` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 128 | `TwistGroup.realizationImages_relators` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | (transitive) | — | stays |
| 136 | `TwistGroup.realizationHom` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 143 | `TwistGroup.realizationHom_c` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 150 | `TwistGroup.realizationHom_x` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | stays |
| 157 | `TwistGroup.realizationHom_y` | old | `cc698c96` `Solution.lean` | `b5767bb7` | old-only | TwistGroup.main_realization_generators_eq_one @ Hopf.Proof.LCP.BoundaryTopology | — | stays |

#### `Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` — 4: 4 moved (W4W1-only)

| line | declaration | history | introduced in (file) | into Hopf/Proof by | usage | evidence (a) old proof | evidence (b) W4W1 @ center-solution | action |
|---|---|---|---|---|---|---|---|---|
| 66 | `TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo` | center | `61de5232` (CS) = `cf943cab` (ours) `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:43 | **moved** |
| 112 | `TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo` | center | `c0786d53` (CS) = `f778d0e3` (ours) `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:102 | **moved** |
| 141 | `TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo` | center | `03f30fb5` (CS) = `27eb3fac` (ours) `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:77 | **moved** |
| 157 | `TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo` | center | `03f30fb5` (CS) = `27eb3fac` (ours) `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` | `702a01f0` | W4W1-only | — | W4W1/CenterBaseCohomologicalDimension.lean:62 | **moved** |

