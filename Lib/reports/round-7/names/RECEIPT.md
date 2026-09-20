# Round 7 — names, Mathlib duplicates, missing imports, the `Hopf/` half of the mixed commits

Branch `r7/names`, base `46c22597`, Lean v4.33.0 / Mathlib v4.33.0.
Sources of truth: `Lib/reports/textbook-audit/AUDIT.md` (cross-cutting finding 6 and the per-file
table), `Lib/reviews/INTEGRATION-6.md` §2 and §4, `NEXT_STEPS.md` top,
`Lib/reports/integration-6/commit-classification.txt`.

## Commits

| # | sha | subject |
|---|---|---|
| A | `b1ffa17e` | refactor: strip the `_mo1973_NNNN` suffixes from Lib declaration names |
| B1 | `6cf79583` | refactor: delete `Lib/CategoryTheory/Sites/Leray/DegreeZero.lean` |
| B2 | `86377b36` | refactor: delete `Lib/LinearAlgebra/Dual/Contragredient.lean` |
| B3 | `7504253c` | refactor: drop `MorseCancellation.range_tanh` for `Real.tanh_bijOn` |
| C | `dd6d4154` | feat: import the thirteen Lib modules `Lib.lean` was missing |
| D1 | `77af0c88` | feat(lib): extract gluing manifold core (Hopf part of `7416076` + `240fe7dd`) |
| D2 | `2ff989ba` | Extract generic based disk lifting from homotopy surjectivity (`6206e6ac`) |
| D3 | `af087836` | Extract prescribed-side disk lifting with nullhomotopic boundary (`068ab07c`) |
| D4 | `089a3b4c` | Extract relative disk lifting from homotopy group vanishing (`0a09c935`) |
| D5 | `549aaf81` | Assemble relative disk lifting from low vanishing and top surjectivity (`abcb24db`) |
| D6 | `38b31474` | Extract sphere generator map and Hurewicz naturality connector (`ea3aa7d4`) |
| D7 | `b5730f83` | Extract normalized invertible-column kernel equivalence into Lib (`3ade4538`) |
| D8 | `be90840b` | Extract invertible-column surjectivity into Lib (`988ae7b7`) |
| D9 | `2049e70e` | Extract signed residual arithmetic into reusable library (`f79b9dc2`) |
| D10 | `697f3cca` | Extract reusable signed-pair surjectivity criterion (`cdeb00ff`) |

## Piece A — the `_mo1973_NNNN` suffixes

28 declarations in 12 `Lib/` files, 86 occurrences, all stripped to the suffix-free name; the map is
`rename.txt` next to this file (28 lines, `old new`, user-facing names).

No alternative name was needed: none of the 28 stripped names collides with anything, checked twice —
`grep` for the short name as a word over `Lib Hopf S6 Solution.lean S6.lean S6Shortcuts.lean
Challenge.lean` (0 hits each), and against the 39,037 distinct names of the base environment dump
(`dump Solution Lib --modules Hopf,Lib` at `46c22597`), plain and private-mangled (0 hits each). All
28 live in project namespaces (`Hurewicz.*`, `PeriodTorusHigherHomology.*`, `OnePointCover`,
`LocalDegree.NativeNeighborhood`, `SphereNormalCoordinates`, `MappingTorusHomology.Covering`), so no
Mathlib name is in reach.

19 of the 28 are `private`; they were renamed the same way. The only consumer outside `Lib/` was
`Hopf/Proof/LCP/IntegralHomology.lean`, three call sites of
`MappingTorusHomology.Covering.inverseMonodromy_period_mo1973_27385`. `Hopf/` has 1,020 further
`_mo1973_` occurrences of its own declarations; those were left alone — only the exact token of the
one Lib consumer was rewritten there.

The edit removes a suffix from identifiers and changes nothing else.

## Piece B — what Mathlib already has

Three landed, three are left with a reason. Each Mathlib name was confirmed by `#check` in this
Mathlib before any deletion (scratch file under the job directory).

### Deleted

| file | Mathlib twin | consumers |
|---|---|---|
| `Lib/CategoryTheory/Sites/Leray/DegreeZero.lean` | `CategoryTheory.Functor.rightDerivedZeroIsoSelf` | none (only the `Lib.lean` import and two `AxiomAudit` probe pairs) |
| `Lib/LinearAlgebra/Dual/Contragredient.lean` | `Representation.dual` | none (only the `Lib.lean` import and seven `AxiomAudit` probe pairs) |
| `MorseCancellation.range_tanh` in `Lib/Geometry/Manifold/Morse/Cubic.lean` | `Real.tanh_bijOn` (with `Set.image_univ`) | its own two uses, rewritten to `← Set.image_univ, Real.tanh_bijOn.image_eq` |

### Left, with the reason

| file | why it stays |
|---|---|
| `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` | The file is one registered `instance`, `CategoryTheory.Sheaf.cohomologyAddCommGroup := Ext.instAddCommGroup`. Rerouting was **tried**: all ten call sites were rewritten to `CategoryTheory.Abelian.Ext.instAddCommGroup`, the eight `public import`s of the module were replaced by its own three Mathlib imports, and the file deleted. `lake build Lib` then fails with `failed to synthesize Add (Sheaf.H Q 0)` / `AddZero (Sheaf.H F n)` in `ShortExactDegreeOne` and `FiniteClosedPushforward/Cohomology`: `Sheaf.H` is not reducible to `Ext` for instance search, so Mathlib's instance does not fire and this registration is load-bearing. This is the "instance-resolution gap" the audit row itself names as the alternative; fixing it is an upstream change. The attempt was reverted. |
| `Lib/Topology/Sheaves/SheafificationLocal.lean` | Mathlib has the two facts the file *cites* (`Presheaf.isLocallySurjective_toSheafify`, `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, both `#check`ed) but not the three it *proves* on top of them — `exists_local_representative`, `germ_unit_eq_iff`, `exists_restriction_eq_of_germ_unit_eq`. Four `Lib` modules (`Leray/SheafificationStalkCompatibility`, `Leray/SheafificationNeighborhoodGerm`, `Leray/CanonicalPositiveNeighborhoodSection`, `SingularCochainSheaf/GlobalSections`) use `sheaf`/`unit`/`exists_local_representative`. Deleting the file means restating and reproving those three — a real proof change. The audit row agrees: it asks to *keep* `exists_local_representative` and drop only `sheaf`/`unit`, which is a refactor, not this task. |
| `Lib/GroupTheory/SplitExtension.lean` | Mathlib's `GroupExtension.Splitting.semidirectProductMulEquiv` is `N ⋊[s.conjAct] G ≃* E` — the action is *fixed* to the splitting's `conjAct`. The consumer, `Hopf/Proof/LCP/BoundaryTopology.lean` (`PeriodFamily.Data.semidirectFundamentalGroupEquiv` plus the two `_symm_inclusion`/`_symm_section` simp lemmas), needs `N ⋊[φ] H ≃* E` for an independently given `φ = D.fundamentalGroupAction hq b`. Those are different types. A reroute is possible in principle — bundle `GroupExtension`/`Splitting` from the eight hypotheses, prove `φ = s.conjAct` from `hconj` and injectivity of `i`, and transport with `SemidirectProduct.congr` — but that is a genuine new proof of several dozen lines plus reproving the two simp lemmas, not the one-line wrapper the plan allows. The audit's own claim that a sibling already uses the Mathlib version refers to `Lib/GroupTheory/GroupExtension/Abelianization.lean`, which works with a bundled `Splitting` and therefore does not face this mismatch. Unused import `Lib.GroupTheory.SplitExtension` in `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` left in place (stock-preamble cleanup is finding 2, not this task). |
| `MorseCancellation.hasDerivAt_tanh`, `MorseCancellation.contDiffAt_artanh` | Not in this Mathlib. `grep` over `Mathlib/` finds no `hasDerivAt_tanh`/`deriv_tanh`, no `HasDerivAt Real.tanh`, and no `ContDiff` lemma for `tanh` or `artanh`; `Analysis/SpecialFunctions/Artanh.lean` stops at `tanh_bijOn`, `tanh_injective`, `artanh_tanh`, `tanh_artanh` and the monotonicity lemmas. The audit entry says the same ("missing pieces should go there"), so these two are upstream candidates, not duplicates. |

## Piece C — the thirteen modules `Lib.lean` did not import

Added in `dd6d4154`, each at the end of its existing directory run so the file's grouping is kept;
`Lib.Topology.Gluing.OverBase`, which has no sibling run, went immediately before
`Lib.Geometry.Manifold.Gluing.OverBase`, the module that imports it.

`VanKampen/{Basic,PathValue}`, `Hurewicz/SphereGenerator`,
`Sites/Leray/FibreStalkEvaluation/{Stalk,Neighborhood,ConstantPointFibre,CanonicalPositive}`,
`Geometry/Manifold/LocalDiffeomorph`, `Topology/Gluing/OverBase`,
`Topology/Homotopy/{BasedDiskLifting,RelativeDiskLifting}`,
`Topology/Sheaves/PrincipalCoverLocalSystem{,/Stalk}`.

After the change every `Lib/**.lean` other than `Lib/AxiomAudit.lean` is imported exactly once and no
import lacks a file: 443 imports, 443 modules, 0 duplicates, 0 orphans.

## Piece D — the `Hopf/` half of the twelve mixed commits

Ten commits for twelve originals. Two deviations from one-commit-per-original, both forced by the
branch:

* `380ddd11` (`Hopf/LCP/LocalModels.lean`, the `MappingTorus.*` block) is **already applied** on this
  branch. Its path does not exist (`Hopf/LCP/LocalModels.lean` became `Hopf/Proof/LCP/LocalModels.lean`
  in the stock/proof split) and none of its 22 declarations is under `Hopf/` any more — they live only
  in `Lib/Topology/MappingTorus/Basic.lean`, which the files that need it already import. Nothing to do.
* `7416076` and `240fe7dd` are **one commit** (`77af0c88`). In `center-solution` they deleted from two
  different files; on this branch both are `Hopf/Proof/LCP/GlobalAssembly.lean`, and the first commit's
  hunk alone leaves the second's seven declarations duplicating the `Lib` module that the first
  commit's own new import brings in — the intermediate tree fails to compile with seven
  "has already been declared". Both hunks are in `77af0c88`.

Conflicts: two, both in `77af0c88`, both resolved by hand. The first was the import block (kept the
branch's long list, added the patch's new `Lib.Geometry.Manifold.Gluing.OverBase`, dropped the patch's
stale `Hopf.LCP.AnalyticFillings` in favour of the branch's `Hopf.Proof.LCP.AnalyticFillings`); the
second was context-only around the seven-declaration block (took the patch side, i.e. deleted). The
other nine commits applied with `git apply -3 --index` cleanly, and every forward already named the
Lib declaration this branch has, so no forward needed adjusting.

Side effect worth recording: `77af0c88` removes the duplicate that made a single environment holding
both `Solution` and `Lib` impossible. At the base, `SpecialPeriods.Threefold.Star.Input` was declared
in both `Hopf.Proof.LCP.GlobalAssembly` and `Lib.Topology.Gluing.OverBase`, so
`dump Solution Lib` aborted with *"environment already contains
'SpecialPeriods.Threefold.Star.Input.ctorIdx'"*. The base dump was therefore taken as two dumps
(`dump Lib --modules Lib` and `dump Solution --modules Hopf,Lib`) merged and deduplicated, and the
after dump the same way, so the two tables are comparable.

### Per commit: deleted Hopf declarations and the Lib declaration that replaces each

| commit | deleted from `Hopf/` | replaced by |
|---|---|---|
| `77af0c88` | `ThreefoldGluing.Data` and its 22 members (`transition_map_source`, `transition_inter`, `gluingCore`, `gluing`, `Space`, `inclusion`, `inclusion_openEmbedding`, `inclusion_jointly_surjective`, `inclusion_eq_iff`, `representative`, `inclusion_representative`, `parametrization`, `parametrization_target`, `parametrization_transition`, `parametrization_symm_inclusion`, `gluedChart`, `gluedChart_symm`, `gluedChart_inclusion`, `gluedChart_inclusion_mem_source`, `chartedSpace`, `gluedChart_mem_atlas`, `gluedChart_transition_apply`); `SpecialPeriods.Threefold.Star.Input` and its 17 members (`transition`, `transition_none_none`, `transition_none_some`, `transition_some_none`, `transition_some_self`, `transition_some_some_of_ne`, `transition_self`, `transition_symm`, `overlap_symm_preserves_base`, `toBase_preimage_own`, `filling_preimage_eq_empty`, `transition_some_some_source_eq_empty`, `transition_source_eq`, `transition_preserves_base`, `eq_or_eq_or_eq_of_common_base`, `transition_cocycle`, `toData`); plus `ThreefoldGluing.Data.{projection, projection_inclusion, projection_continuous, inclusion_range, localProjection, patchHomeomorph, patchHomeomorph_projection}` | every one of them under **the same name** in `Lib/Topology/Gluing/OverBase.lean` (the eight chart declarations via `Lib/Geometry/Manifold/Gluing/OverBase.lean`) |
| `2ff989ba` | proof body of `BasedDiskLifting.exists_based_disk_lift` (no declaration removed) | `BasedDiskLifting.exists_based_disk_lift_of_surjective`, `Lib/Topology/Homotopy/BasedDiskLifting.lean` |
| `af087836` | proof body of `TopCellLifting.exists_top_disk_lift` (no declaration removed) | `TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic`, `Lib/Topology/Homotopy/BasedDiskLifting.lean` |
| `089a3b4c` | proof body of `LowCellLifting.relativeDiskLifting_five` (no declaration removed) | `LowCellLifting.relativeDiskLifting_of_pi_vanishing`, `Lib/Topology/Homotopy/RelativeDiskLifting.lean` |
| `549aaf81` | proof body of `TopCellLifting.sphereMap_relativeDiskLifting_six` (no declaration removed) | `TopCellLifting.relativeDiskLifting_of_pi_vanishing_of_surjective`, `Lib/Topology/Homotopy/RelativeDiskLifting.lean` |
| `38b31474` | proof body of `sphereMap_piSix_bijective` (no declaration removed) | `SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective`, `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` |
| `b5730f83` | `ThreefoldHomologyTopDegreeAlgebra.kernelEquivOfColumnIso`; private `ThreefoldHomologyTopDegreeAlgebra.kernelProjectionAddEquiv_mo1973_30150` | `LinearMap.kerEquivOfColumnIso`, `Lib/LinearAlgebra/ColumnKernel.lean` (the private helper is folded into it) |
| `be90840b` | `ThreefoldHomologyTopDegreeAlgebra.surjective_of_columnIso` | `LinearMap.surjective_of_columnIso`, `Lib/LinearAlgebra/ColumnKernel.lean` |
| `2049e70e` | `ThreefoldHomology.FifthDegree.signed_residual_coordinate_zero` | `Int.signed_residual_coordinate_zero`, `Lib/Data/Int/SignedResidual.lean` |
| `697f3cca` | proof body of `ThreefoldHomology.CapElimination.starLeft_surjective_of_nativeCapKernel` (no declaration removed) | `AddMonoidHom.surjective_signed_prod_of_surjective_ker`, `Lib/Algebra/Group/Prod.lean` |

## Builds, axioms, census

| check | result |
|---|---|
| `lake build Lib` | green, 9,150 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,189 jobs |
| `lake build Lib.AxiomAudit` | green, 9,150 jobs; 3,352 probes, every one `[propext, Classical.choice, Quot.sound]` or a subset; 0 occurrences of `sorryAx` |
| `python3 scripts/lib_stock_census.py --check` | `ratchet PASS: 123 <= baseline 1648` |

3,352 probes against integration 6's 3,361: exactly the nine pairs the two deleted files owned
(two for `DegreeZero`, seven for `Contragredient`). `Challenge.lean` still reports its one
pre-existing `sorry` at l.42 — the open challenge statement, unchanged from `46c22597`.

## Environment diff

`lean-agent-ide dump` at `46c22597` and at `697f3cca`, each as the two-root merge described above,
`envdiff.py` with the rename map applied to the base table (the tool maps `old new`, so the map
belongs on the side that still spells the old names; on the after environment it is a no-op).
Machine receipt: `envdiff.json` next to this file.

```
constants before 39160 after 39003 (keys 38535 38488)
lost 184 added 27  of which source declarations: 86 6
names with changed type 16, of which source: 10 — all ten classified PROOF-NAMING
auxiliary lost/added/changed (not judged): 98 21 6
module moves (source declarations, 1-to-1): none
ambiguous module changes: 70   (the duplicate removals below)
VERDICT FAIL
```

The verdict is FAIL by construction: this round deletes declarations on purpose and `envdiff` never
accepts a loss. The judgment is the table below — every lost source name with its replacement.

**No unexplained type change.** All ten source names whose type hash moved are `PROOF-NAMING`, i.e.
`envdiff` found their `uses` sets identical before and after; they are the dependents of the six
renamed `def`s of Piece A, whose types now spell the new name
(`Hurewicz.DegreeTwo.SimplyConnected.{continuous_gluedBoundaryFunction, gluedBoundaryFunction_bottom,
gluedBoundaryFunction_side}`, `Hurewicz.flatCoordinateSum_succ_ne_zero`,
`LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius`,
`MappingTorusHomology.Covering.{coverSmallCycle_productCover_class, coverSmallCycle_productCover_eq}`,
`PeriodTorusHigherHomology.{biprodElement_boundary, biprodElement_desc, biprod_lift_eq_boundary}`).
No statement changed.

**No source name was lost to Piece A or Piece C.** The rename is a clean bijection under the map, and
adding imports only adds.

### Lost source declarations (86)

| n | group | module lost from | replacement |
|---:|---|---|---|
| 2 | Piece B, `DegreeZero` deleted | `Lib.CategoryTheory.Sites.Leray.DegreeZero` | `(pushforward f).rightDerivedZeroIsoSelf` and its `.app F` (Mathlib `Functor.rightDerivedZeroIsoSelf`) |
| 2 | Piece B, `Contragredient` deleted | `Lib.LinearAlgebra.Dual.Contragredient` | `Representation.dual` / `Representation.dual_apply` (`contragredient`, `contragredient_apply`) |
| 5 | Piece B, `Contragredient` deleted | `Lib.LinearAlgebra.Dual.Contragredient` | no replacement: `ofMultiplicativeEquiv`, `ofMultiplicativeEquiv_apply`, `ofMultiplicative`, `ofMultiplicative_apply`, `freeGroup_invariant_iff` — unused tag-removal and free-group helpers with no consumer anywhere in the tree, which the audit row asks to restate elsewhere rather than keep in this shape |
| 1 | Piece B, tanh | `Lib.Geometry.Manifold.Morse.Cubic` | `MorseCancellation.range_tanh` → `Set.image_univ ▸ Real.tanh_bijOn.image_eq` |
| 4 | Piece D, `b5730f83` / `be90840b` / `2049e70e` | `Hopf.Proof.LCP.IntegralHomology` | `kernelEquivOfColumnIso` and its private helper → `LinearMap.kerEquivOfColumnIso`; `surjective_of_columnIso` → `LinearMap.surjective_of_columnIso`; `signed_residual_coordinate_zero` → `Int.signed_residual_coordinate_zero` |
| 70 | Piece D, `77af0c88` | `Hopf.Proof.LCP.GlobalAssembly` (count 2 → 1) | the identical declaration in `Lib.Topology.Gluing.OverBase` (62) or `Lib.Geometry.Manifold.Gluing.OverBase` (8), same name, same type hash — only the `Hopf/` copy of a duplicate went away |
| 2 | Piece D, `77af0c88` | `Hopf.Proof.LCP.GlobalAssembly` (count 1 → 0) | `SpecialPeriods.Threefold.Star.Input.disjoint` and `.mk`. Both still exist, from `Lib.Topology.Gluing.OverBase`, before and after (checked row by row in the two tables); the `Hopf/` copy carried a different type hash for the structure's `disjoint` field, so its key fell to zero while the Lib key stayed at one. The two `structure` blocks are byte-identical. Nothing is gone. |

Summing: 2 + 7 + 1 + 4 + 70 + 2 = 86, the whole lost-source list. 72 of the 86 are one side of a
duplicate that the branch has been carrying since integration 6, 12 are the Piece B deletions and the
four Piece D extractions with a named Lib replacement, and 5 (`LinearRepresentation.*` minus the two
`contragredient` ones) are unused code deleted with its file.

### Added source declarations (6)

`BasedDiskLifting.exists_based_disk_lift_of_surjective`,
`TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic`,
`LowCellLifting.relativeDiskLifting_of_pi_vanishing`,
`TopCellLifting.relativeDiskLifting_of_pi_vanishing_of_surjective`,
`SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective`,
`SixthHurewicz.exists_sphereMap_of_homologySixEquiv`.

These are not new mathematics: they are `Lib` declarations that already existed in the tree at
`46c22597` but were in none of the three modules any root reached, because `Lib.lean` did not import
`Topology/Homotopy/{BasedDiskLifting,RelativeDiskLifting}` or `Hurewicz/SphereGenerator` (Piece C) and
no `Hopf/` file imported them either (Piece D's forwards now do).

### Module moves

None. `envdiff` reports no 1-to-1 source move; the 70 "ambiguous" entries are the duplicate removals
of `77af0c88` (a key losing its `Hopf.Proof.LCP.GlobalAssembly` copy and gaining nothing), and the 40
auxiliary module changes are their equation lemmas and `_proof_n` abstractions.
