# Wave 2 receipt: `Lib/Geometry/Manifold/Morse/Existence.lean`

- Agent: Claude Opus 5.5 (`claude-opus-5-5`). Second agent on this assignment: the first was
  stopped while still reading and left no commits.
- Wall clock: start 2026-10-01 17:00 CEST, end 2026-10-01 18:45 CEST.
- Worktree `/home/goblin/hopf-w2-existence`, branch `wave2/existence`, base `3760f829`.
- Commits: `13444eb4` (split), `069798c8` (field docstrings), `e07cc702` (import trims),
  `86fde3fb` (docstring corrections, comment only), followed by this receipt.
- Judgement entry: verdict C, "three subjects" (`Lib/reports/round-7/judgement/monoliths.md`).

## The cut

`tools/split_module.py` was run once per piece against the unchanged base source
(sha256 `cafc53a546de…`). Each run used stay = every ranged constant not in the piece, so the
ten receipts in `existence/split_*.json` refer to the same source line numbers. All 117 units
(126 ranged constants: 117 declarations, plus 1 structure constructor and 8 fields of
`MapSmoothingPatch`) were moved, and none stayed. The old module is now a facade: copyright,
`module`, ten `public import`s and a rewritten module docstring.

| piece (`Lib/Geometry/Manifold/Morse/Existence/…`) | base lines moved | ranged constants | textbook topic |
|---|---|---|---|
| `AttachingUnion` | 46–293, 551–626 (318) | 8 | sublevel set across an isolated critical level = lower sublevel set ∪ handle, with flow-line control (cf. Milnor, *Morse theory* §3; h-cobordism §3) |
| `RegularLocus` | 297–367 (68) | 4 | openness of the regular locus of a smooth family; stability of the critical set |
| `DistinctCriticalValues` | 371–549 (173) | 7 | Morse functions with distinct critical values (cf. Milnor, h-cobordism §2) |
| `LevelSurgery` | 630–770 (136) | 6 | the two level sets across a handle as a `SurgeryBoundaryPair` |
| `PartialChart` | 930–983 (51) | 4 | restrictions of `PartialDiffeomorph`, bijective derivative |
| `BeltCore` | 772–794, 798–926, 985–1157 (314) | 14 | attaching and belt spheres as smooth closed embeddings with injective differential |
| `HomotopyCollars` | 1161–1206, 1210–1235, 2182–2206 (87) | 13 | reparametrising a homotopy to be stationary near both ends |
| `HomotopicRelWithin` | 1800–1848 (44) | 6 | relative homotopy that keeps `K` inside `O` |
| `ChartPerturbation` | 1239–1796, 1850–1896 (567) | 40 | perturbing a map within a chart of the target; the local step of Whitney approximation (cf. Hirsch §2.2; Lee Ch. 6) |
| `SmoothApproximation` | 1900–2099, 2103–2180, 2208–2236 (295) | 24 (15 units) | every continuous map from a compact manifold to a boundaryless manifold is homotopic (rel. a closed set) to a smooth one; smooth homotopies stationary near the ends |

Pieces import each other along the real dependencies: `DistinctCriticalValues` → `RegularLocus`;
`BeltCore` → `LevelSurgery`, `PartialChart`; `ChartPerturbation` → `HomotopicRelWithin`;
`SmoothApproximation` → `HomotopicRelWithin`, `PartialChart`, `HomotopyCollars`,
`ChartPerturbation`. The facade imports all ten.

I kept all pieces under `Existence/` and did not use the auditor's targets:
- `Morse/HandleAttachment.lean` already exists and is not one of my files.
- `Geometry/Manifold/SmoothApproximation.lean` is not an existing module.
Both moves are listed under "Left".

Verbatim check: the tool succeeded on every run, so I did not split anything by hand. In
addition, the text of each moved unit, taken from the base file at its receipt line range, was
found as a substring of its piece (117/117).

Tool quirk: `--move-imports` lines were inserted at line 1 because the tool looks for `^import`
and this file has `public import`. My post-processing script (scratch `run/post.py`) moved them
below the existing imports. The same script replaced the copied module docstring with the
piece's own, and dropped `/-! ### … -/` section headings that had no declaration under them in
the piece. It touched only context lines, never a unit.

## `Hopf/Proof` moves: none

Closure argument, from `dump_head.jsonl`: take every constant of another `Lib` module that uses
a constant of `Lib.Geometry.Manifold.Morse.Existence`, then close backwards under `uses` inside
the module. The result covers 125 of the 126 ranged constants. The only one outside it is
`ManifoldSmoothing.continuous_flattenTime`, a generic lemma (continuity of a clamp) and not
project material. Nothing in the file mentions `mo1973`, dimension 6, `Hemisphere` or `native*`.
So nothing moves, and no `Hopf` consumer or `AxiomAudit` probe changes.

## Renames: none

`rename.txt` contains only a comment.

## Universe lifts: none

Every statement was already `Type*`. `grep -n 'Type}\|\.{0}\|universe'` over the pieces and the
facade is empty.

## Docstrings

I counted docstrings over the after dump: 125 ranged non-constructor constants in the ten
pieces (117 declarations + 8 structure fields), 125 with a docstring, 0 missing.
- Added (`069798c8`): 8, the fields `chart`, `cutoff`, `outer`, `smooth`, `outer_smooth`,
  `compact`, `outer_compact`, `nested` of `ManifoldSmoothing.MapSmoothingPatch`.
- Rewritten because they were wrong (`86fde3fb`, comment only): 9.
  - `exists_isolating_radius`: talked about balls; the statement is about values in
    `[f p - ρ², f p + ρ²]`.
  - `exists_separating_critical_value`: claimed "a regular level between two critical levels".
  - `exists_distinct_critical_values` and `exists_morse_function_with_distinct_critical_values`:
    cited Milnor Thm 2.5 / Hatcher.
  - `isOpen_regularPoint`: cited Hatcher.
  - `eventually_criticalPoints_eq`
  - `ChartMapPerturbation.exists_radius_valid`: "avoid a finite set of target points".
  - `ChartMapPerturbation.exists_smooth_coordinate_approximation`: "avoiding finite sets".
  - `ManifoldSmoothing.exists_finite_patch_smoothing_within_target`: "piecewise-defined
    function, Milnor 2.5".
- Theorem numbers I could not confirm were replaced by section or chapter references
  ("cf. Milnor, h-cobordism §2", "Morse theory §3", "Hirsch §2.2", "Lee Ch. 6"):
  - in the module docstrings I first wrote;
  - in the auditor's suggestions (Milnor Thm 2.7, Hirsch Thm 2.2.6, Lee Thm 6.26).
- Module docstrings: 10 new, plus the rewritten facade.

## Import trims (`e07cc702`)

Each piece's imports were chosen from the modules its constants `use` in the dump:
- `PartialChart`, `HomotopyCollars`, `HomotopicRelWithin` and `ChartPerturbation` import only
  `Mathlib` (plus intra-piece imports).
- `RegularLocus` and `DistinctCriticalValues` import `MorseLemma`.
- `SmoothApproximation` imports `Flow.Compact`.
- `AttachingUnion` and `LevelSurgery` import `MorseLemma`, `Morse.Handle`,
  `Morse.HandleAttachment` and `Flow.HeightTranslating`.
- `BeltCore` imports those four plus `RegularLevel`.

Every original import (including `MorseLemma` and `HeightTranslating`, imported as their
facades) is still imported by at least one piece, so the facade's transitive import set is
unchanged for its 37 consumers. `Mathlib` itself was not narrowed. The file had no
`maxSynthPendingDepth`, kitchen-sink `open scoped` or `universe` left to drop.

## Checks (all run after the last source edit `86fde3fb`, from `run/final.log`)

```
=== lake build Lib
exit 0
✔ [9287/9288] Built Lib (2.5s)
Build completed successfully (9288 jobs).
=== lake build Solution S6Shortcuts S6 Challenge
exit 0
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9347 jobs).
=== lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
exit 0
info: Lib/AxiomAudit.lean:7438:0: 'DeterminingFamily.commute_all_of_lattice_image_eq_zpow' depends on axioms: [propext, Quot.sound]
Build completed successfully (9290 jobs).
```

- Facade and pieces: `lake build Lib.Geometry.Manifold.Morse.Existence` →
  `Build completed successfully (8723 jobs).` (also covers every module created or edited).
- Axiom audit log: 3302 `depends on axioms` lines; 0 axioms outside
  {propext, Classical.choice, Quot.sound}; 0 `sorryAx`. The only `sorry` warning in the
  Solution build is `Challenge.lean:42:8`, the open challenge statement, unchanged from base.
- `python3 scripts/lib_stock_census.py --check`:
  `stock declarations under Hopf/: 123 …` and `ratchet PASS: 123 <= baseline 1648`.
- `grep -rn --include=*.lean '^import Hopf\|^public import Hopf' Lib/`: empty. Without
  `--include` it matches only pre-existing `.md`/`.txt` logs under `Lib/docs/`.

## envdiff (`existence/envdiff.txt`, dump after `86fde3fb`)

```
constants before 38301 after 38304 (keys 38199 38202 )
lost 3 added 6 of which source declarations: 0 0 ; names with changed type 3 of which source: 0
auxiliary lost/added/changed (not judged): 3 6 3
module moves: 8/14/40/7/6/13/6/4/4/24 → AttachingUnion/BeltCore/ChartPerturbation/
  DistinctCriticalValues/HomotopicRelWithin/HomotopyCollars/LevelSurgery/PartialChart/
  RegularLocus/SmoothApproximation (126 = the plan)
ambiguous module changes: 0
VERDICT PASS
```

The 3/6/3 auxiliaries come from one shared auxiliary proof. In the base, the abstracted proof
`ManifoldMorse.SignedMorseChart.FollowsModelBoundaryOrbits._proof_1` (typeHashPublic
2547959801) was reused by `beltCoreMap`, `boundaryLevelHomeomorph` and
`homotopyCollarNeighborhood`. After the split these three live in other modules, and each
module re-creates the proof under its own name:
- `beltCoreMap._proof_1`, which shifts the old `_proof_1`/`_proof_2` to `_proof_2`/`_proof_3`;
- `boundaryLevelHomeomorph._proof_2`, which shifts the old `_proof_2` to `_proof_3`;
- `homotopyCollarNeighborhood._proof_1`.
These are renumberings of `_proof_n` auxiliaries only. No source declaration was lost, added
or changed type.

## Left

1. **Final homes.** The pieces stay under `Morse/Existence/`. The auditor suggests:
   - handle geometry (`AttachingUnion`, `LevelSurgery`, `BeltCore`) → `Morse/HandleAttachment`;
   - the smoothing pieces → `Geometry/Manifold/SmoothApproximation/`;
   - `PartialChart` → beside Mathlib's `PartialDiffeomorph`.

   Do this when the facades are dissolved. Reproduce: `ls Lib/Geometry/Manifold/Morse/Existence/`.
2. **`HomotopicRelWithin` name.** It is in the root namespace; Mathlib style would be
   `ContinuousMap.HomotopicRelWithin`. Not renamed, because its consumers are in the monolith
   `Immersion/Relative`, which another agent is splitting now. Reproduce:
   `grep -rln --include=*.lean 'HomotopicRelWithin' Lib Hopf | grep -v /Existence`.
3. **`PartialChart.*` names.** These are `PartialDiffeomorph` lemmas under a project namespace.
   Not renamed (31 consumer files). Reproduce:
   `grep -rln --include=*.lean 'PartialChart\.' Lib Hopf | grep -v /Existence/ | wc -l`.
   The namespaces `ManifoldMorse`, `ManifoldSmoothing`, `ChartMapPerturbation` and
   `ClosedCover` are also project vocabulary and were left as they are.
4. **Hard-coded constants.** `flattenTime` and the collars use `1/3, 2/3, 1/4, 3/4` in the
   statements (auditor finding). Reproduce:
   `grep -n '1 / 3\|2 / 3\|1 / 4\|3 / 4' Lib/Geometry/Manifold/Morse/Existence/HomotopyCollars.lean`
   (8 lines).
5. **Generic lemma in a Morse file.** `ManifoldMorse.exists_isolating_radius` is a statement
   about a finite set and a real function, not Morse theory, and sits in `AttachingUnion`.
   Reproduce: `grep -n 'exists_isolating_radius' Lib/Geometry/Manifold/Morse/Existence/AttachingUnion.lean`.
6. **Vague docstrings.** These are vague but not wrong ("A closed product block inside a
   prescribed set exists.") and were not rewritten, which the rules permit. 99 one-line
   docstrings are under 60 characters:
   `grep -hE '^/-- .{0,60} -/$' Lib/Geometry/Manifold/Morse/Existence/*.lean | wc -l`.
7. **Tool.** `split_module.py --move-imports` does not recognise `public import` (see "The
   cut"). Reproduce: run it with `--move-imports` on any `module` file; the lines land at line 1.
