# Wave 1 receipt — morse-d: `Morse/OrderedCancellation.lean` and `Morse/SurgeryCollapse.lean`

Seat: Claude Fable 5.1, 2026-09-27/28. Base `lib/integration` at `e669bc93`, branch `wave1/morse-d`,
worktree `/home/goblin/hopf-w1-morse-d`. Judgement entries: `Lib/reports/round-7/judgement/monoliths.md`
(both verdict D, "moved verbatim from `Hopf/SphereTopology.lean`"). Tooling: `lean-agent-ide`
`split_module.py` (one run per piece from the original source, stay = everything else; receipts in
`Lib/reports/wave-1/morse-d/receipts/`), `dump`, `envdiff.py`.

Commit range: `cd6689b1..HEAD` — four cut commits (`cd6689b1` OC pieces + facade, `01c6893b` OC
Hopf/Proof piece + consumer imports, `e9bf5d70` SC pieces + facade, `0a2c13b6` SC Hopf/Proof pieces +
consumer imports), 25 docstring commits (one per Lib piece), then this receipt. The four cut commits
hold the tool output unchanged (every moved unit's text has the SHA-256 of the receipt, checked against
`git show e669bc93:<file>`); the docstring commits only add `/-- … -/` blocks.

## The cut

Both originals are facades now (module docstring listing the pieces, `import`s, nothing else).
`Lib.lean` is unchanged; consumers need no change. Declarations, names, namespaces and statements are
unchanged (envdiff below).

| piece | class | lines moved | declarations | textbook topic |
|---|---|---|---|---|
| `OrderedCancellation/TwoSphereDegree` | Lib | 29 | 3 | a homology isomorphism of `S²` acts by `±1` (Hatcher §2.2) |
| `OrderedCancellation/BeltTube` | Lib | 207 | 15 | tubular neighbourhood of a belt sphere and its meridians (Milnor h-cob. §5) |
| `OrderedCancellation/PrescribedFlow` | Lib | 209 | 5 | adapted windows with a prescribed gradient-like flow (Milnor h-cob. §3) |
| `OrderedCancellation/CircleParametrization` | Lib | 23 | 4 | the diffeomorphism `S¹ ≃ Circle` |
| `OrderedCancellation/ValueExchange` | Lib | 353 | 9 | exchanging consecutive critical values (Milnor h-cob. Thm 4.1) |
| `OrderedCancellation/PairCancellation` | Lib | 354 | 8 | first cancellation theorem (Milnor h-cob. Thm 5.4) |
| `OrderedCancellation/PathComponents` | Lib | 129 | 12 | `H₀` detects path components (Hatcher Prop 2.7) |
| `OrderedCancellation/Negation` | Lib | 67 | 6 | the Morse function `-f`, index `n - λ` (Milnor, Morse Theory §2) |
| `OrderedCancellation/MinimalSystem` | Lib | 65 | 3 | Morse functions with the least number of critical points (Milnor h-cob. §8) |
| `OrderedCancellation/IndexCounts` | Lib | 215 | 9 | counting critical points by index |
| `OrderedCancellation/BirthPreservation` | Lib | 145 | 7 | what a birth of a critical pair preserves below (Milnor h-cob. §8) |
| `Hopf/Proof/…/OrderedCancellation/MiddleIndexBlocks` | Hopf/Proof | 139 | 5 | dimension 6, indices 2/3 (project) |
| `SurgeryCollapse/PuncturedBall` | Lib | 34 | 3 | punctured ball retracts onto a sphere (Hatcher Ex. 0.2) |
| `SurgeryCollapse/BeltTubeMeridian` | Lib | 102 | 4 | loops in the belt tube are homotopic to meridians |
| `SurgeryCollapse/LevelTransport` | Lib | 441 | 8 | transport of embedded spheres between regular levels (Milnor h-cob. §4) |
| `SurgeryCollapse/CellExactSequence` | Lib | 370 | 18 | long exact sequence of an attached cell (Hatcher Ex. 2.43 / Prop 2.22) |
| `SurgeryCollapse/HandleExactSequence` | Lib | 349 | 23 | homology exact sequence of passing a critical point (Milnor, Morse Theory Thm 3.2) |
| `SurgeryCollapse/MinimumReduction` | Lib | 226 | 6 | minimal Morse function has one minimum and one maximum (Milnor h-cob. Thm 8.1) |
| `SurgeryCollapse/IndexOrdering` | Lib | 212 | 4 | rearrangement by index (Milnor h-cob. Thm 4.4, 4.8) |
| `SurgeryCollapse/DiskFilling` | Lib | 186 | 7 | filling a null-homotopic circle by an embedded disk (Milnor h-cob. Thm 6.6) |
| `SurgeryCollapse/LevelIsotopy` | Lib | 318 | 4 | realising an isotopy of a regular level by a flow (Milnor h-cob. Lemma 4.7) |
| `SurgeryCollapse/OnePointCover` | Lib | 95 | 14 | two-patch cover of `OnePoint N`, suspension isomorphism (Hatcher Ex. 2.2) |
| `SurgeryCollapse/DiskCollapse` | Lib | 232 | 25 | collapsing the complement of an attached cell (Hatcher Prop 2.22) |
| `SurgeryCollapse/LocalDegreeConnecting` | Lib | 389 | 22 | point connecting map and its naturality (Hatcher §2.2, local degree) |
| `SurgeryCollapse/SphereOrientation` | Lib | 527 | 32 | orientation sign of the point connecting map (Hatcher §2.2) |
| `SurgeryCollapse/HandleCollapse` | Lib | 434 | 31 | collapsing the lower sublevel set of a Morse surgery (Milnor h-cob. §7) |
| `Hopf/Proof/…/SurgeryCollapse/MiddleFamilies` | Hopf/Proof | 417 | 6 | dimension 6, `Hemisphere.Sphere 2` families (project) |
| `Hopf/Proof/…/SurgeryCollapse/BeltIntersections` | Hopf/Proof | 468 | 7 | dimension 6, index-2 Whitney trick (project) |
| `Hopf/Proof/…/SurgeryCollapse/OuterIndexMinimal` | Hopf/Proof | 59 | 1 | counts `c₁ + c₅` (project) |
| `Hopf/Proof/…/SurgeryCollapse/MiddlePresentation` | Hopf/Proof | 253 | 16 | index-2 basis, index-3 presentation of `H₂` (project) |

Totals: OrderedCancellation 86 declarations (81 Lib, 5 Hopf/Proof), SurgeryCollapse 231 (201 Lib,
30 Hopf/Proof); 317 units, each moved exactly once (`receipts/*.json`; the unit structure is the same
in every run, no unit fell on both sides, no standalone `attribute`/`#` command in either file).

Placement: every Lib piece is `Lib/Geometry/Manifold/Morse/<FileStem>/<Topic>.lean` as the rules
prescribe. Natural eventual homes, for the facade-dissolving step: `PathComponents` beside
`Lib/AlgebraicTopology/SingularHomology/` (it is Hatcher 2.7, nothing Morse in it), `PuncturedBall`
beside `PuncturedRadial` (`Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean`),
`OnePointCover` beside `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean`, `Negation` in
`Morse/Index.lean`, as the auditors suggested; not done here because no existing module holds the
matching declarations and a new module elsewhere is outside the rule.

Imports: each piece imports `Mathlib` plus exactly the `Lib` modules that define a constant its
declarations use (dump `uses` field over the base, `plan_resolved.json`), plus the sibling pieces it
uses. The duplicate `import Lib.Algebra.Module.IntegerPresentation` of `SurgeryCollapse.lean` is gone
with the old list. `set_option maxSynthPendingDepth`, `open scoped … Modular …` and `universe u v`
were not present at the base (the auditors read an older revision). Context copied to every piece:
`open Set Function Filter Manifold Topology`, `open scoped ContDiff ContinuousMap`,
`noncomputable section … end`.

## Moves to `Hopf/Proof` and the closure argument

Moved (35 declarations, `git show 01c6893b 0a2c13b6`): everything carrying
`Module.finrank ℝ E = 6`, a `Hemisphere.Sphere 2` family, the index-2/3 machinery, or the count
`c₁ + c₅`:

- `OrderedCancellation/MiddleIndexBlocks`: `nativeIndexThreeAttachingSphere`,
  `IsNativeMiddleBasinFamily`, `outer_index_minimality_neg`, `exists_middle_index_blocks`,
  `nativeMiddleBlockPoint`.
- `SurgeryCollapse/MiddleFamilies`: `AdaptedWindows.exists_middle_family_descent`,
  `exists_middle_family_step`, `exists_regular_band_middle_basin_family`
  (general dimension, but its statement is an `IsNativeMiddleBasinFamily`),
  `exists_middle_basin_family_step`, `exists_middle_block_realization`, `exists_ordered_middle_family`.
- `SurgeryCollapse/BeltIntersections`: `SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices`,
  `MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices`,
  `MorseSurgeryData.exists_finite_belt_cancellation_step`, `exists_finite_belt_reduction`,
  `exists_minimal_signed_belt_sphere`, `exists_single_belt_intersection_of_unit_count`,
  `AdaptedWindows.exists_transverse_middle_belt_loop`.
- `SurgeryCollapse/OuterIndexMinimal`: `exists_outer_index_minimal_ordered_morse_system` (stated for
  general `E`, `M`, but its secondary minimality is of `nativeMorseCount 1 + nativeMorseCount 5`).
- `SurgeryCollapse/MiddlePresentation`: `MorseSurgeryData.indexTwoCollapseCoordinate`,
  `indexTwoCoordinate_surjective`, `indexTwoCoordinate_kernel`, `lowerRealization_two_injective`,
  `exists_indexTwoHomology_split`, `exists_indexTwoBasis_extension`, `SurgeryWindows.indexTwoBasis_step`,
  `indexTwoBasis`, `MorseSurgeryData.indexThreeAttachingClass`, `coreBoundary_two_eq_smul`,
  `coreBoundary_two_range`, `indexThree_lowerRealization_surjective`,
  `indexThree_lowerRealization_kernel`, `indexThreePresentation`, `SurgeryWindows.middlePresentation`,
  `middleMatrix`.

Closure (`check_plan.py` over `dump_head.jsonl`): the set of constants of the two modules reachable
backwards through `uses` from any constant of another `Lib` module has 6 declarations —
`IntLinearAutomorphism.apply_eq_mul`, `apply_one_eq_one_or_neg_one`,
`MorseCancellation.two_sphere_map_unit_of_homology_bijective` (used by
`Morse/EqualRangeHomology.lean`), `exists_morseSurgeryData_of_field_germ_lt`,
`exists_adapted_windows_with_prescribed_flow_lt`, `unitSphere_isEmpty_of_finrank_zero` (used by
`Morse/AdaptedWindows.lean`) — all in Lib pieces; `SurgeryCollapse` has no `Lib` consumer at all.
No Lib piece uses a Hopf/Proof declaration (checked on direct `uses`; the build of `Lib` confirms).
`two_sphere_map_unit_of_homology_bijective` mentions `Hemisphere.Sphere 2` and stays for that reason.

Hopf consumers of moved declarations (from the dump): `Hopf.SphereTopology`, `Hopf.Recognition`,
`Hopf.Proof.Recognition`, `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks`. `Hopf/SphereTopology.lean`
imports the two facades directly and got the `import Hopf.Proof.…` lines right after them; the other
three import the facades only transitively and got the lines after the import that provides them
(`Hopf.LCP.IntegralHomology`, `Hopf.Recognition`, `Lib.Geometry.Manifold.Morse.AdaptedWindows`).
`Lib/AxiomAudit.lean` and `Hopf/Proof/AxiomAudit.lean` probe none of the 317 names; nothing moved there.

## Renames and lifts

None. No `mo1973` name exists in either file at the base (`grep -n mo1973` on `e669bc93` is empty; the
auditors' `_mo1973_5327/5719/5731` were renamed before integration). `rename.txt` is therefore a
comment only. No universe lift was attempted (see Left).

## Docstrings

281, computed: `grep -c '^/--'` over the 25 Lib pieces sums to 281 = number of non-private planned
declarations (282 minus the `private def OnePointCover.spherePunctureHomeomorph`). Each states the
binders, hypotheses and conclusion; theorem numbers are cited only where the module docstring's twin is
certain (Milnor h-cobordism 4.1, 4.4, 4.7, 4.8, 5.4, 6.6, 8.1; Morse Theory 3.2; Hatcher 0.2, 2.7, 2.22,
2.43), otherwise a section or "cf.".

## Checks (verbatim from `build1.log`, `build2.log`)

```
lake build <30 pieces + 2 facades>          Build completed successfully (8815 jobs).
lake build Lib                              Build completed successfully (9171 jobs).   exit Lib 0
lake build Solution S6Shortcuts S6 Challenge   Build completed successfully (9228 jobs).   exit Solution 0
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit   Build completed successfully (9173 jobs).   exit AxiomAudit 0
python3 scripts/lib_stock_census.py --check    ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf' Lib/ --include=*.lean   (empty)
```

Axiom audit: 3302 `depends on axioms` lines in `build2.log`, every list within
`[propext, Classical.choice, Quot.sound]`, no `sorryAx` (checked by script over the wrapped lines).
`lake build` was run pinned to three cores (`taskset -c 18,19,0`; this Lake has no `-j`).

## envdiff

`dump_after.jsonl` of the tip (`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib`, 38254
constants) against `dump_head.jsonl` (38248), `envdiff.py` → `Lib/reports/wave-1/morse-d/envdiff.{txt,json}`:

```
constants before 38248 after 38254 (keys 38146 38152 )
lost 2 added 8 of which source declarations: 0 0 ; names with changed type 2 of which source: 0
auxiliary lost/added/changed (not judged): 2 8 2
module moves (source declarations, 1-to-1): 30 pairs, 317 declarations, exactly the plan
  (5/15/7/4/9/3/6/8/12/5/3/9 out of OrderedCancellation, 7/6/16/1/4/18/25/7/31/23/4/4/8/22/6/14/3/32 out of SurgeryCollapse)
ambiguous module changes: 0
auxiliary constants that changed module: 198
VERDICT PASS
```

Every planned constant is in its planned module (`plan_resolved.json` against `dump_after.jsonl`:
317 planned, 0 missing, 0 in a wrong module). The auxiliary differences, name by name: Lean abstracts
an identical proof term once per module, so the shared `_proof_1` (hash 2096436044) of the old
`SurgeryCollapse` is now realized once in each of the five pieces that use it —
`OnePointCover.sphereConnecting._proof_1`, `MorseSurgeryData.morseConnectingMap._proof_1`,
`SpherePoint.sourceCountMark._proof_1`, `LocalDegree.NativeNeighborhood.sphereConnecting._proof_1`,
`MorseSurgeryData.indexTwoCollapseCoordinate._proof_1` — and the former `_proof_1` of the last two
became `_proof_2` (the two "lost" and two "changed type" names are those renumberings); the eighth
addition is `SpherePoint.targetCountMark._proof_1` (a newly abstracted proof). All eight are
`_proof_n` constants of unchanged declarations; no source declaration is lost, added or changed.

## Left

- Duplicate: `OnePointCover.spherePunctureHomeomorph` (private, `SurgeryCollapse/OnePointCover.lean`)
  and `SpherePoint.punctureHomeomorph` (`SurgeryCollapse/SphereOrientation.lean`) are the same
  stereographic construction, the first on `EuclideanSpace ℝ (Fin (n+1))`, the second on any `V` with
  `Fact (finrank ℝ V = n + 1)`; nothing deleted this wave.
  `grep -rn 'stereographic'\'' n' Lib/Geometry/Manifold/Morse/SurgeryCollapse/`
- Universe pins `{… : Type}` in Lib pieces (statement pinned at `Type`, not lifted): 173 binder groups in
  `SurgeryCollapse/{HandleExactSequence 23, HandleCollapse 16, LocalDegreeConnecting 27, SphereOrientation 31,
  CellExactSequence 18, DiskCollapse 8, MinimumReduction 6, BeltTubeMeridian 5, OnePointCover 4,
  LevelTransport 3}` and `OrderedCancellation/{BeltTube 16, PathComponents 12, IndexCounts 3, TwoSphereDegree 1}`
  (counts of `: Type}` binder groups; several are forced by `Type`-pinned structures such as
  `EmbeddedCellAttachment`, `SurgeryWindows.BandData`, `LocalDegree.NeighborhoodData`).
  `grep -c ': Type}' Lib/Geometry/Manifold/Morse/OrderedCancellation/*.lean Lib/Geometry/Manifold/Morse/SurgeryCollapse/*.lean`
- Project vocabulary kept: `native*` / `Native*` names (`nativeBeltTube*`, `nativeMorseIndex`,
  `nativeMorseCount`, `nativeIndexDisorder`, `native_lower_*`, `IsNativeMiddleBasinFamily`,
  `LocalDegree.NativeNeighborhood`, `NativeTransversality`) — 466 occurrences (lines) in the Lib pieces; the
  definitions live in other modules (`CubicFlow`, `Cancellation`, `LocalDegreeNeighborhoods`), so a
  rename is not local to this wave. `grep -rn 'native\|Native' Lib/Geometry/Manifold/Morse/OrderedCancellation/ Lib/Geometry/Manifold/Morse/SurgeryCollapse/ | wc -l`
- `attribute [local instance 100] Classical.propDecidable in` / `attribute [local instance] … in`
  repeated per declaration instead of one section (verbatim move).
  `grep -rc '^attribute \[local instance' Lib/Geometry/Manifold/Morse/SurgeryCollapse/HandleCollapse.lean`
- `MorseCancellation.two_sphere_map_unit_of_homology_bijective` (Lib, `TwoSphereDegree`) is stated on
  `Hemisphere.Sphere 2`; it stays because `Morse/EqualRangeHomology.lean` uses it; a general-`n` form
  is a later generalisation. `grep -rn two_sphere_map_unit_of_homology_bijective Lib/`
- Eventual homes of `PathComponents`, `PuncturedBall`, `OnePointCover`, `Negation` (see Placement).
- Two `OnePointCover.instLocal1` / `SpherePoint.instLocal1` `Fact` helpers remain theorem-shaped local
  instances (verbatim); `SpherePoint.instLocal2/3` live in `SingularHomology/OnePointCover.lean`.
