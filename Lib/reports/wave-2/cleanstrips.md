# Wave 2: `Lib/Geometry/Manifold/Whitney/CleanStrips.lean` (cleanstrips)

Agent: Claude Opus 5.5 (`claude-opus-5-5`), second agent on this assignment (the first was stopped
while reading and left no commits). Start 2026-10-01 18:42 CEST, end 2026-10-01 19:21 CEST.
Worktree `/home/goblin/hopf-w2-cleanstrips`, branch `wave2/cleanstrips`, base `3760f829`.
Commits `446b1e36..` this receipt (`git log --oneline 3760f829..wave2/cleanstrips`).

Judgement entry: `Lib/reports/round-7/judgement/monoliths.md`, verdict C. At the base the module
docstring and the 140 declaration docstrings had already been rewritten (commits `f88440bf`,
`af11d3a2`, `28c0db0b`, including the corrected docstring of
`exists_clean_bigon_boundary_neighborhood`, kept verbatim), and the `maxSynthPendingDepth`,
kitchen-sink `open scoped` and `universe` lines were already gone. What remained: one file of eleven
families, the `native` names, `Whitney` depending on `Morse/CircleGluing`, undocumented structure
fields.

## The cut

`split_module.py` was run ten times on the original source (`dump_head.jsonl` ranges), each time
with stay = all constants except one piece, `--move-out` = the piece, `--keep-out` discarded. The
ten receipts are in `cleanstrips/split-<Piece>.receipt.json`, the plan in `cleanstrips/plan.json`.
The ten moved sets partition the 140 units; each moved unit's text was checked to occur verbatim in
its piece (140/140). The pieces' module docstrings and the facade were written by hand (context
lines only). Lines are those of the original file (ranges include docstrings).

| piece (`Lib/Geometry/Manifold/Whitney/CleanStrips/…`) | lines moved | units / constants | topic |
|---|---|---|---|
| `CrossingChart.lean` | 63–660 | 21 / 21 | simultaneous and clean charts at a transverse crossing; transverse intersections of complementary dimension are discrete, finite when compact (Guillemin–Pollack §1.5, §2.3) |
| `SphereNormal.lean` | 662–874 | 16 / 16 | defining function of the unit sphere; adapted normal frame `ℝ x ⊕ TₓSⁿ`; normal Jacobian (Milnor h-cob. §6) |
| `BeltIntersection.lean` | 876–1035 | 9 / 9 | local signs, finiteness and algebraic count of intersections of a sphere with the belt sphere of a Morse surgery (Milnor h-cob. §6) |
| `NormalCoordinate.lean` | 1037–1121, 1537–1592 | 8 / 8 | normal coordinate `Prod.snd ∘ Φ⁻¹` of a product chart; its kernel along the zero section (cf. Guillemin–Pollack §1.4) |
| `StripModel.lean` | 1123–1259, 1277–1435, 2278–2352 | 29 / 29 | linear model `(ℝ × A) × B` of a strip chart: flat model, blending, injectivity criteria, transverse inclusion, detector |
| `StripNormalData.lean` | 1261–1275, 1437–1535, 1594–1871 | 21 / 27 | strip charts along a sheet (`StripNormalData`), normal frames and sheet transitions |
| `CornerPatch.lean` | 1873–2054 | 10 / 21 | corner slices at a crossing; `CleanCornerPatch`, `swap` |
| `BigonStripCoordinates.lean` | 2354–2497, 2640–2708 | 11 / 11 | planar Whitney bigon: strip charts are immersions, frontier = two edges, interior → open strip |
| `StripPatch.lean` | 2056–2079, 2499–2558, 2710–2721 | 5 / 21 | `CleanStripPatch`: centre arc injective, avoids sheets, coincidences, immersion criterion |
| `BigonBoundary.lean` | 2081–2276, 2560–2638, 2723–2892 | 10 / 30 | gluing to a clean embedded neighbourhood of the bigon boundary; `CleanBigonBoundary` (Milnor h-cob. §§5–6) |

Total 140 units, 193 ranged constants (structure fields and constructors included). The facade
`CleanStrips.lean` keeps its header, imports the ten pieces, and has a module docstring listing
them; consumers and `Lib.lean` are unchanged.

## `Hopf/Proof` moves and closure

None. Closure over `dump_head.jsonl` (constants of the module reachable backwards from constants of
other `Lib` modules): every unit except `normalJacobian_ne_zero`, `beltNormalReference`,
`beltIntersectionCount`, `beltIntersectionJacobian_ne_zero`, `beltIntersectionSign_unit`,
`sheetTransverseInclusion_apply`, `cornerLinear_apply` and some structure fields is needed by
`Lib`. Those seven are general-dimension statements (any `m`, any `n`; no `finrank = 6`, no
`Hemisphere.Sphere 2`, no `mo1973`), i.e. library material, so they stay.

## Renames (`cleanstrips/rename.txt`, `<new> <old>`)

| new | old |
|---|---|
| `StripNormalData.mfderiv_eq_comp_fderiv_coordinateMap` | `StripNormalData.native_derivative_factor` |
| `injective_mfderiv_of_eqOn_cleanStripPatch_comp` | `injective_nativeDerivative_of_strip_germ` |
| `injective_mfderiv_of_mem_frontier_bigon` | `injective_nativeDerivative_bigon_boundary` |

All consumers are inside the pieces (`grep -rn` over `Lib Hopf Solution.lean S6.lean
S6Shortcuts.lean Challenge.lean` found no other use). No `mo1973` names in this file.

## Universe lifts

None (every binder is already `Type*`).

## Imports

The pieces no longer import `Morse/CircleGluing` except `BeltIntersection` (Morse surgery data);
each base piece imports `Mathlib` plus the `Lib` modules whose constants it uses (dump `uses`):
CrossingChart → `Collar`, `Morse.Existence`, `Transversality.Basic`, `WhitneyEmbedding`;
SphereNormal → `Morse.Handle`; NormalCoordinate → `Morse.Existence`; StripModel, StripPatch →
`Whitney.BigonModel`; BigonBoundary → `Immersion.Relative.ImmersionLocus`. Pieces importing a
sibling drop what the sibling provides.

## Docstrings

Computed over `dump_after.jsonl` (ranged constants of the ten pieces, constructors excluded):
189 of 189 carry a docstring; at the base 140 of 189 did. The 49 added are structure-field
docstrings (`StripNormalData` 5, `CleanCornerPatch` 10, `CleanStripPatch` 15,
`CleanBigonBoundary` 19), commit `8836e670`. No existing docstring was rewritten.

## Builds (verbatim)

* `lake build Lib.Geometry.Manifold.Whitney.CleanStrips` (facade and all ten pieces):
  `Build completed successfully (8849 jobs).`
* `lake build Lib`: `Build completed successfully (9288 jobs).`
* `lake build Solution S6Shortcuts S6 Challenge`: `Build completed successfully (9347 jobs).`
* `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit`: `Build completed successfully (9290 jobs).`;
  3302 axiom reports, union of axiom sets `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`.
* `python3 scripts/lib_stock_census.py --check`: `stock declarations under Hopf/: 123 (prefixes:
  222, prefixes now absent from Hopf/: 194)` … `ratchet PASS: 123 <= baseline 1648`.
* `grep -rn '^import Hopf' Lib/ --include=*.lean`: empty (the unrestricted grep hits only `.md`
  and `.txt` files under `Lib/docs/`, unchanged).

## envdiff (`cleanstrips/envdiff.txt`, `cleanstrips/envdiff.json`)

Dump after the last Lean edit with `--rename cleanstrips/rename.txt`: 38302 constants against 38301.

```
lost 0 added 1 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 1 0
```
Module moves: 9, 30, 11, 21, 21, 8, 16, 29, 27, 21 source declarations from `CleanStrips` to
BeltIntersection, BigonBoundary, BigonStripCoordinates, CornerPatch, CrossingChart,
NormalCoordinate, SphereNormal, StripModel, StripNormalData, StripPatch — exactly `plan.json`.
`VERDICT PASS`.

The one added constant is the auxiliary `StripCoordinates.sheetTransverseInclusion._proof_1`
(StripModel). At the base the value of `sheetTransverseInclusion` reused the identical auxiliary
proof `SphereNormalCoordinates.normalFrame._proof_4` of the same file; `StripModel` does not import
`SphereNormal`, so Lean generated its own. The type of `sheetTransverseInclusion` is unchanged.

## Left

1. `exists_native_clean_corner_of_parametrizations` keeps its name: its consumer is
   `Lib/Geometry/Manifold/Whitney/EmbeddedArcs.lean`, a monolith split concurrently by another
   agent. `grep -rn exists_native_clean_corner_of_parametrizations Lib --include=*.lean`
2. `NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates*` (8 constants) live in a namespace
   whose structures are defined in `WhitneyEmbedding.lean` and `Collar.lean`; statements also use
   `NativeParametrization.centered` and `NativeTransversality.At` from `Transversality/Basic.lean`
   (another batch-2 monolith). Renaming the namespaces is outside this file.
   `grep -n 'Native' Lib/Geometry/Manifold/Whitney/CleanStrips/*.lean`
3. `BeltIntersection` (Morse-surgery belt intersection numbers) belongs under `Morse/` per the
   judgement; this wave keeps pieces under `CleanStrips/`.
   `grep -n '^def\|^theorem' Lib/Geometry/Manifold/Whitney/CleanStrips/BeltIntersection.lean`
4. Project-flavoured namespaces kept: `TransverseCoordinates.*`, `SphereBoundary.*`,
   `StripCoordinates.ker_comp_eq_range_of_injective` (pure linear algebra under a strip namespace).
   `grep -n 'theorem TransverseCoordinates\|SphereBoundary\.\|ker_comp_eq_range_of_injective' Lib/Geometry/Manifold/Whitney/CleanStrips/*.lean`
5. The `StripCoordinates`/`StripNormalData` toolkit is general in `A`, `B`, but its only `Lib`
   consumers go through `WhitneyPairModel` (`BigonModel.lean`); unchanged.
   `grep -rln 'StripNormalData' Lib --include=*.lean`
