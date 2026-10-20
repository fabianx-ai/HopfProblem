# Freed `PeriodTorusHigherHomology` rows: move receipt (NEXT_STEPS.md item 5, integration 4)

Worktree `lib/next-circle`, 2026-09-14. Source of the row list: `Lib/reports/proof-split/FREED.md`,
section "PeriodTorusHigherHomology (102)", the 40 rows whose "now in" column is under `Hopf/Proof/`.

## Where the rows actually live

`NEXT_STEPS.md` item 5 (and this seat's brief) place the 40 rows under `Hopf/Proof/LCP/CuspFilling.lean`.
The FREED.md `file:line` column places all 40 in `Hopf/Proof/LCP/Specialization.lean`, and that is
where they are at `304a0fea` (every line number in FREED.md matched the declaration line, verified by
`scratch/move.py` before the move). `CuspFilling.lean` holds none of them. The move was therefore made
from `Hopf/Proof/LCP/Specialization.lean`; no other `Hopf/` file was touched.

## Dependency rule and outcome

A row may move only if every name it uses is in `Lib/` or in a row moved earlier. FREED.md's "pure
move" classification allowed dependencies on the *stock* `Hopf/LCP/*.lean` files as well; under the
stricter Lib-only rule 16 rows move and 24 stay. Every blocked row uses at least one name still in the
stock files `Hopf/LCP/CuspFilling.lean` (`coordinateProjection`, `coordinatePeriodLoop`) or
`Hopf/LCP/Specialization.lean` (`torusTailMap*`, `omitHeadMatrix`, `takeHeadMatrix`,
`coordinateTorusMap*`, `coordinateTorusMatrix*`, `coordinateTorusMapAlong`, `homeomorph_symm_add_of_add`,
`PeriodTorusHigherHomologyPontryagin.product_natural`, `positiveCircleCross_pointClass`); they unblock
as soon as those clusters reach `Lib/`.

## Destination

`Lib/AlgebraicTopology/SingularHomology/Torus.lean`, not `CirclePaths.lean`: the subject of all 16 rows is
the product torus `ProductTorus n` (integer-matrix self-maps of the torus, the coordinate circle maps
into the torus, the successor step of the top class), which `Torus.lean` names and defines;
`CirclePaths.lean` does not import `Torus.lean` and has no `ProductTorus`. One import line was added
to `Torus.lean`: `public import Lib.AlgebraicTopology.SingularHomology.CirclePaths`
(`productTorusTopClass_succ_cross` uses `positiveCircleCross` and
`circleProductHomologyEquiv_positiveCircleCross`). No file in `Lib/` imported `Torus.lean`, so no
cycle. The blocks are appended in source order, inside the file's `@[expose] public noncomputable section`.

## Moved (16)

Source lines are at `304a0fea` (before deletion); destination lines are after the commit.

| declaration | from | to | retarget |
|---|---|---|---|
| `PeriodTorusHigherHomology.torusMatrixLinearMap` | `Hopf/Proof/LCP/Specialization.lean:2539-2554` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:292-307` |  |
| `PeriodTorusHigherHomology.torusMatrixLinearMap_continuous` | `Hopf/Proof/LCP/Specialization.lean:2556-2561` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:309-314` |  |
| `PeriodTorusHigherHomology.torusMatrixMap` | `Hopf/Proof/LCP/Specialization.lean:2563-2565` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:316-318` |  |
| `PeriodTorusHigherHomology.torusMatrixMap_apply` | `Hopf/Proof/LCP/Specialization.lean:2567-2570` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:320-323` |  |
| `PeriodTorusHigherHomology.torusMatrixMap_one` | `Hopf/Proof/LCP/Specialization.lean:2586-2592` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:325-331` |  |
| `PeriodTorusHigherHomology.torusMatrixMap_mul` | `Hopf/Proof/LCP/Specialization.lean:2594-2602` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:333-341` |  |
| `PeriodTorusHigherHomology.coordinateCircleMap` | `Hopf/Proof/LCP/Specialization.lean:3233-3237` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:343-347` | `(PeriodTorusHigherHomology.CircleTopology.Circle)` -> `(CircleTopology.Circle)` |
| `PeriodTorusHigherHomology.coordinateCircleMap_apply` | `Hopf/Proof/LCP/Specialization.lean:3239-3243` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:349-353` | `(PeriodTorusHigherHomology.CircleTopology.Circle)` -> `(CircleTopology.Circle)` |
| `PeriodTorusHigherHomology.coordinateCircleMap_zero` | `Hopf/Proof/LCP/Specialization.lean:3245-3249` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:355-359` |  |
| `PeriodTorusHigherHomology.coordinateCircleMap_add` | `Hopf/Proof/LCP/Specialization.lean:3251-3255` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:361-365` | `(PeriodTorusHigherHomology.CircleTopology.Circle)` -> `(CircleTopology.Circle)` |
| `PeriodTorusHigherHomology.torusMatrixMap_zero` | `Hopf/Proof/LCP/Specialization.lean:3293-3296` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:367-370` |  |
| `PeriodTorusHigherHomology.torusHeadCircleMap` | `Hopf/Proof/LCP/Specialization.lean:3314-3316` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:372-374` | `(PeriodTorusHigherHomology.CircleTopology.Circle)` -> `(CircleTopology.Circle)` |
| `PeriodTorusHigherHomology.torusHeadCircleMap_apply` | `Hopf/Proof/LCP/Specialization.lean:3318-3325` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:376-383` | `(PeriodTorusHigherHomology.CircleTopology.Circle)` -> `(CircleTopology.Circle)` |
| `PeriodTorusHigherHomology.productTorusTopClass_succ_cross` | `Hopf/Proof/LCP/Specialization.lean:3363-3376` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:385-398` |  |
| `PeriodTorusHigherHomology.torusMatrixMap_zero_source` | `Hopf/Proof/LCP/Specialization.lean:3614-3620` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:400-406` |  |
| `PeriodTorusHigherHomology.torusMatrixMap_add` | `Hopf/Proof/LCP/Specialization.lean:3701-3704` | `Lib/AlgebraicTopology/SingularHomology/Torus.lean:408-411` |  |

Text check: the 105 non-blank lines deleted from the source equal the 105 non-blank lines appended to
the destination modulo the 5 retargeted lines (`git diff -U0` of both files compared line by line);
no line was added to the source, none removed from the destination. Retarget:
`PeriodTorusHigherHomology.CircleTopology.Circle` is the `Hopf/LibShims.lean:44` export of
`SingularHomology.CircleTopology.Circle`; in `Torus.lean` the same constant is reached as
`CircleTopology.Circle` through the file's `open SingularHomology`. No statement, attribute, or proof
changed. No `private` widening was needed. The `lean-agent-ide dump` envdiff was not run; the
verbatim-text comparison above is the check that was made.

## Blocked (24), still in `Hopf/Proof/LCP/Specialization.lean`

Line numbers are those of FREED.md (at `304a0fea`, before the deletion above shifted later lines).

| declaration | line | blocking names (outside `Lib/` and outside the 40) |
|---|---|---|
| `PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection` | 2572 | `coordinateProjection` (`Hopf/LCP/CuspFilling.lean:265`) |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop_apply` | 3257 | `coordinatePeriodLoop` (`Hopf/LCP/CuspFilling.lean:306`), `coordinatePeriodLoop_apply` (`:314`) |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop` | 3268 | `coordinatePeriodLoop` (`Hopf/LCP/CuspFilling.lean:306`) |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology` | 3276 | `coordinatePeriodLoop` (`Hopf/LCP/CuspFilling.lean:306`) |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop_apply` | 3284 | `coordinatePeriodLoop`, `coordinatePeriodLoop_eq_projection` (`Hopf/LCP/Specialization.lean:228`), blocked row `torusMatrixMap_coordinateProjection` |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop` | 3298 | `coordinatePeriodLoop` (`Hopf/LCP/CuspFilling.lean:306`) |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology` | 3306 | `coordinatePeriodLoop` (`Hopf/LCP/CuspFilling.lean:306`) |
| `PeriodTorusHigherHomology.productTorusSucc_inverse_eq_add` | 3328 | `torusTailMap` (`Hopf/LCP/Specialization.lean:235`), `torusTailMap_apply` (`:240`) |
| `PeriodTorusHigherHomology.torusSplit_positiveCircleCross` | 3341 | `torusTailMap` (`Hopf/LCP/Specialization.lean:235`), blocked row `productTorusSucc_inverse_eq_add` |
| `PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology` | 3357 | `coordinatePeriodLoop`, blocked row `coordinateCircleMap_positiveHomology` |
| `PeriodTorusHigherHomology.productTorusTopClass_succ_product` | 3378 | `torusTailMap`, `coordinatePeriodLoop`, blocked rows `torusSplit_positiveCircleCross`, `torusHeadCircleMap_positiveHomology` |
| `PeriodTorusHigherHomology.productTorusTopClass_one` | 3387 | `coordinatePeriodLoop`, blocked row `torusHeadCircleMap_positiveHomology` |
| `PeriodTorusHigherHomology.productTorusTopClass_two` | 3405 | `coordinatePeriodLoop`, `torusTailMap_coordinatePeriodHomology` (`Hopf/LCP/Specialization.lean:269`) |
| `PeriodTorusHigherHomology.productTorusTopClass_three` | 3415 | `coordinatePeriodLoop`, `torusTailMap_add` (`Hopf/LCP/Specialization.lean:244`), `PeriodTorusHigherHomologyPontryagin.product_natural` (`Hopf/LCP/Specialization.lean:156`) |
| `PeriodTorusHigherHomology.productTorusTopClass_two_is_product` | 3548 | `coordinatePeriodLoop`, `torusTailMap`, blocked row `productTorusTopClass_succ_product` |
| `PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct` | 3557 | `coordinatePeriodLoop`, `torusTailMap`, `product_natural`, blocked row `productTorusTopClass_two_is_product` |
| `PeriodTorusHigherHomology.torusMatrixMap_omitHeadMatrix` | 3593 | `omitHeadMatrix` (`Hopf/LCP/Specialization.lean:390`) |
| `PeriodTorusHigherHomology.torusMatrixMap_takeHeadMatrix` | 3604 | `takeHeadMatrix` (`Hopf/LCP/Specialization.lean:394`) |
| `PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap` | 3623 | `coordinateTorusMap` (`Hopf/LCP/Specialization.lean:398`), `coordinateTorusMatrix` (`:474`), `coordinateTorusMap_degree_zero` (`:420`), `coordinateTorusMap_omit_apply` (`:424`), `coordinateTorusMap_take_apply` (`:432`), `coordinateTorusMatrix_omit` (`:485`), `coordinateTorusMatrix_take` (`:492`), blocked rows `torusMatrixMap_omitHeadMatrix`, `torusMatrixMap_takeHeadMatrix` |
| `PeriodTorusHigherHomology.coordinateTorusMap_add` | 3706 | `coordinateTorusMap`, blocked row `coordinateTorusMap_eq_torusMatrixMap` |
| `PeriodTorusHigherHomology.coordinateTorusMapAlong_add` | 3714 | `coordinateTorusMapAlong` (`Hopf/LCP/Specialization.lean:640`), `homeomorph_symm_add_of_add` (`:693`), blocked row `coordinateTorusMap_add` |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop` | 5508 | `positiveCircleCross_pointClass` (`Hopf/LCP/Specialization.lean:727`) |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one` | 5515 | blocked row `circleHomologyOneEquiv_positiveLoop` |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int` | 5521 | blocked row `circleHomologyOneEquiv_positiveLoop` |

## Build and census

Full chain, `lake build Lib && lake build Solution S6Shortcuts S6 Challenge`, `scratch/build.log`:

```
Build completed successfully (8817 jobs).
...
✔ [8854/8856] Built Hopf.Proof.Final (4.1s)
ℹ [8855/8856] Built Solution (3.0s)
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8856 jobs).
```

No `error:` line, no warning on `Torus.lean` or `Specialization.lean`.

`python3 scripts/lib_stock_census.py --check`: `ratchet PASS: 1586 <= baseline 1648` (unchanged:
`Hopf/Proof/` is not census-counted).
