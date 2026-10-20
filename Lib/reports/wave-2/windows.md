# Wave 2 — `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` (agent `windows`)

Agent: Claude Opus 5.5 (model ID `claude-opus-5-5`). Start 2026-10-01 17:00 CEST, end 2026-10-01
17:58 CEST. Worktree `/home/goblin/hopf-w2-windows`, branch `wave2/windows`, base `3760f829`.
Commits `315a31d4..` this receipt commit (base exclusive). Judgement entry:
`Lib/reports/round-7/judgement/monoliths.md`, verdict C.

## The cut

`split_module.py` was run **once per piece, always from the original source** (stay set = the
complement of the piece; the keep output was discarded), so every unit was cut by the base dump's
ranges. The receipts are `windows/split_<Piece>.json`. All 119 units and 157 ranged constants were
written exactly once; each unit's text (receipt SHA-256 re-checked against the original) occurs
verbatim in its piece. The context lines copied into every piece (the old module docstring, the
eleven `/-! ### … -/` section headers) were then replaced by a per-piece header (imports and
module docstring). `open Set Function Filter Manifold Topology`, `open scoped ContDiff ENNReal` and
`@[expose] public noncomputable section` were kept unchanged in every piece. The original module is
now a facade that imports the eleven pieces and nothing else.

Pieces under `Lib/Geometry/Manifold/Morse/SurgeryWindows/`:

| piece | units / constants | lines moved (original line span) | declarations | textbook topic |
|---|---|---|---|---|
| `HausdorffDimension` | 8 / 8 | 167 (66–134, 1076–1179) | `GeneralPosition.dimH_image_chart_le`, `…dimH_image_manifold_le`, `…dense_compl_manifold_image`; root `dimH_image_le_of_contDiffOn_isOpen`, `dimH_image_chart_le`, `dimH_image_manifold_le`, `dense_compl_manifold_image`, `not_surjective_contMDiff_of_dim_lt` | Hausdorff dimension of smooth images; easy Sard (cf. Milnor, *Topology from the differentiable viewpoint*, §2–3); Mathlib `dimH_image_le_of_locally_lipschitzOn` |
| `Avoidance` | 10 / 16 | 287 (136–433) | `exists_small_localized_image_avoidance`, `ChartMapPerturbation.exists_small_avoiding_parameter`, `GeneralPosition.MapAvoidancePatch` (+`Compatible`), `exists_patch_step`, `exists_finite_patch_avoidance`, `exists_avoidance_of_finite_patches`, `exists_avoidance_patch_at`, `exists_disjoint_smooth_map_homotopicRel(_of_isClosed_range)` | general position, cf. Hirsch Ch. 3, Guillemin–Pollack Ch. 2 |
| `DiskDouble` | 8 / 8 | 50 (537–593) | `DiskDouble.*` | twisted double of a disk, Alexander trick |
| `Hemisphere` | 18 / 18 | 111 (597–724) | `Hemisphere.*` | the sphere as two hemisphere graphs over the ball |
| `ImageComplement` | 6 / 6 | 132 (437–533, 728–766) | `ImageComplement.domain`, `inclusion`, `exists_smooth_homotopy_of_ambient_homotopic`, `homotopic_of_ambient_homotopic`, `nullhomotopic_of_ambient_nullhomotopic`, `circle_nullhomotopies` | homotopies in the complement of a low-dimensional image (Hirsch Ch. 3) |
| `NewInterior` | 10 / 10 | 84 (899–991) | `PuncturedHandle.OpenUnitBall`, `SurgeryBoundaryPair.NewInterior` and 8 lemmas/defs | interior of the new piece of a surgery (Milnor, h-cobordism §3) |
| `OpenHomotopyExtension` | 5 / 5 | 76 (995–1074) | `OpenHomotopyExtension.*` | pasting lemma; extension of a homotopy stationary off a closed set |
| `ZeroAvoidanceCutoff` | 17 / 17 | 165 (1181–1363) | `exists_smooth_nonzero_approx`, `RealIntervalProgress.*`, `ZeroAvoidanceCutoff.*`, `exists_nonzero_homotopy_small` | nonvanishing approximation in higher codimension |
| `BeltComplement` | 9 / 9 | 276 (768–895, 1367–1521) | `SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_*`, `exists_belt_avoiding_circle`, `circle_nullhomotopies_of_beltComplement`, `newBoundary_circle_nullhomotopies`; `ManifoldMorse.SignedMorseChart.attachingSphere_eq_attachingCoreMap`, `contMDiff_surgeryAttachingSphere`, `surgery_beltComplement_circle_nullhomotopies`, `surgery_newBoundary_circle_nullhomotopies` | simple connectivity across a surgery of index ≥ 2 (Milnor, h-cobordism §3) |
| `SurgeryData` | 18 / 35 | 292 (1525–1835) | `ManifoldMorse.MorseSurgeryData` (+ fields) and its API, `exists_morseSurgeryData_lt`, `SphereCoordinates.standardParametrization`, `transportedAttachingSphere*`, `exists_smoothBandBridge` | handle attachment (Milnor, *Morse Theory*, Thm 3.1–3.2) |
| `Windows` | 10 / 25 | 123 (1837–1968) | `ManifoldMorse.SurgeryWindows` (+ fields) and its API, `nonempty_surgeryWindows`, `AdaptedWindows` (unchanged) | surgery windows of a Morse function (Milnor, h-cobordism §3–4) |

Total: 119 units, 157 constants, 1,763 lines. Import DAG: `HausdorffDimension → Avoidance`,
`DiskDouble → Hemisphere`, `{Avoidance, Hemisphere} → ImageComplement`,
`HausdorffDimension → ZeroAvoidanceCutoff`,
`{ImageComplement, NewInterior, OpenHomotopyExtension, ZeroAvoidanceCutoff} → BeltComplement →
SurgeryData → Windows`. Each piece imports `Mathlib`, its sibling pieces, and only the `Lib`
modules whose constants its declarations use (computed from the `uses` field of the base dump);
the facade's four `Lib` imports (`Morse.Existence`, `RegularLevel`, `WhitneyEmbedding`, `Collar`)
were replaced by these. No further trimming was attempted; the whole `Mathlib` import was kept as
in the original. The judgement's `set_option maxSynthPendingDepth`, kitchen-sink `open scoped`,
`universe u v` and local notations were already absent at the base.

`AdaptedWindows` is byte-identical to the base (docstring, `attribute … in` prefix and fields).

## `Hopf/Proof` moves: none

Closure over `dump_head.jsonl`: the constants of the module reachable backwards from any constant
of another `Lib` module are 120 of the 157 ranged ones. The 37 others are general mathematics
(the `OpenHomotopyExtension`, `RealIntervalProgress` and `ZeroAvoidanceCutoff` APIs with
`exists_smooth_nonzero_approx`, `exists_nonzero_homotopy_small` and the root `dense_compl_manifold_image`, three
`Hemisphere` simp lemmas, `PuncturedHandle.OpenUnitBall` and the three `newInteriorHomeomorph` declarations, two structure fields, and the
new-boundary loop chain ending in `MorseSurgeryData.upper_circle_nullhomotopies`, which only
`Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.BeltIntersections` uses). None is project
material (no dimension 6, no `Hemisphere.Sphere 2`, no `mo1973`, no fixed index), so nothing
moved. `lake build Lib` is green and no `.lean` file under `Lib/` imports `Hopf`.

## Renames, lifts

None. `rename.txt` is empty (no `mo1973` names in the file). No universe lifts: every statement
was already over `Type*`.

## Docstrings (computed)

Over the dump at the tip, the ranged constants of the eleven pieces, excluding constructors and
`to…` parent projections, are 152 (119 declarations + 33 structure fields); 145 have a docstring,
the 7 without are the `AdaptedWindows` fields (kept exactly as instructed). At the base all 119 declarations had docstrings and no
structure field had one. This branch adds 26 field docstrings (`MapAvoidancePatch` 5,
`MorseSurgeryData` 16, `SurgeryWindows` 5) in three commits, and rewrites 44 vague or wrong
declaration docstrings in one comment-only commit (`0469912d`; Avoidance 4, BeltComplement 8,
HausdorffDimension 2, ImageComplement 1, NewInterior 4, OpenHomotopyExtension 4, SurgeryData 6,
Windows 7, ZeroAvoidanceCutoff 8). The wrong ones included `ZeroAvoidanceCutoff.blend_small` and
`blend_large`, whose cases were swapped; `newPiece_mem_newInterior_iff`;
`ImageComplement.circle_nullhomotopies`; and `ManifoldMorse.SurgeryWindows`, which was described
as "a pair of windows around a critical point". The facade's stale "`NoExotic` dimension cluster"
outline item is gone.

## Checks (tip `0469912d` plus this receipt, which changes only `.md`/`.json`/`.txt`)

```
lake build Lib.Geometry.Manifold.Morse.SurgeryWindows   Build completed successfully (8762 jobs).
lake build Lib                                          Build completed successfully (9289 jobs).
lake build Solution S6Shortcuts S6 Challenge            Build completed successfully (9348 jobs).
  info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit         Build completed successfully (9291 jobs).
  3302 "depends on axioms" lines; union of axioms = {propext, Classical.choice, Quot.sound}; sorryAx: 0
python3 scripts/lib_stock_census.py --check
  stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
  ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf\|^public import Hopf' Lib/ --include=*.lean   (empty)
```
(The rules' unfiltered `grep -rn '^import Hopf' Lib/` hits only `.txt`/`.md` logs under
`Lib/docs/`, which are identical at the base.) The build logs show no warning in a `SurgeryWindows`
file.

## envdiff (`windows/envdiff.txt`, `windows/envdiff.json`)

`dump Solution Lib --modules Hopf,Lib` gave 38,302 constants (base 38,301). Verdict **PASS**:
source declarations lost/added/changed type 0/0/0. Module moves: 157 source constants, 1-to-1,
`Lib.Geometry.Manifold.Morse.SurgeryWindows → ….SurgeryWindows.<Piece>`, with these counts:
Avoidance 16, BeltComplement 9, DiskDouble 8, HausdorffDimension 8, Hemisphere 18,
ImageComplement 6, NewInterior 10, OpenHomotopyExtension 5, SurgeryData 35, Windows 25,
ZeroAvoidanceCutoff 17. These are exactly the plan (`names_<Piece>.txt`). Ambiguous: 0.

Auxiliary lost 2 / added 3 (not judged): `ZeroAvoidanceCutoff.weight._proof_1` and
`ZeroAvoidanceCutoff.weight.eq_1`. At the base, the body of `weight` reused the abstracted proof
`Hemisphere.vector._proof_1` from the same module. Now that `Hemisphere` is a separate module,
Lean abstracts the proof locally as `weight._proof_1`/`_proof_2`, and `weight.eq_1` changes with
it. The types of `weight` and its lemmas are unchanged.

## Left

1. **Duplicate Hausdorff-dimension lemmas** (deleting is out of scope this wave). The root
   `dimH_image_manifold_le` and `dense_compl_manifold_image` have the same conclusions as
   `GeneralPosition.dimH_image_manifold_le` and `GeneralPosition.dense_compl_manifold_image` under
   the extra `[I.Boundaryless]`, so they are special cases of them. Root `dimH_image_chart_le` is
   the same bound for `modelChartPartialDiffeomorph` instead of `extChartAt`.
   `grep -n '^theorem \(GeneralPosition\.\)\?\(dimH_image_chart_le\|dimH_image_manifold_le\|dense_compl_manifold_image\)' Lib/Geometry/Manifold/Morse/SurgeryWindows/HausdorffDimension.lean`
2. **Loop nullhomotopy spelled ad hoc.** `∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (const c)`
   is used instead of `SimplyConnectedSpace X` (together with path-connectedness). Changing it
   changes statements, which this wave does not allow.
   `grep -rn 'Hemisphere.Sphere 1, ' Lib/Geometry/Manifold/Morse/SurgeryWindows/ | wc -l` → 21
3. **`Hemisphere.Sphere n`** is an `abbrev` for Mathlib's `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`
   under a project namespace, and it reaches every downstream file. Renaming it is a separate step.
   `grep -rln 'Hemisphere\.' Lib Hopf --include=*.lean | wc -l` → 32
4. **`AdaptedWindows` fields have no docstrings.** The structure was kept exactly as instructed.
   `grep -n -A16 '^structure AdaptedWindows' Lib/Geometry/Manifold/Morse/SurgeryWindows/Windows.lean`
5. **Project-style namespaces kept**: `GeneralPosition`, `ChartMapPerturbation`, `ImageComplement`,
   `OpenHomotopyExtension`, `RealIntervalProgress`, `ZeroAvoidanceCutoff`, `DiskDouble`,
   `Hemisphere`, `SphereCoordinates`. There are many consumers and no single Mathlib-style target
   name is evident.
   `grep -rhoE '^(theorem|def|abbrev|structure) [A-Za-z]+\.' Lib/Geometry/Manifold/Morse/SurgeryWindows/ | sort | uniq -c`
6. **Better homes** for the general pieces, once the facade is dissolved:
   - `HausdorffDimension` and `Avoidance` → a `Geometry/Manifold/GeneralPosition` module
   - `OpenHomotopyExtension` → `Topology/Homotopy`
   - `RealIntervalProgress.progress` → a `Set.projIcc` ramp in `Topology/Order`
   - `DiskDouble` and `Hemisphere` → `Topology`

   `ls Lib/Geometry/Manifold/Morse/SurgeryWindows/`
7. **Import trims not tried.** Every piece still imports all of `Mathlib` and keeps the
   original `open`/`open scoped` lines, which may be unused in some pieces.
   `grep -n '^public import Mathlib$\|^open' Lib/Geometry/Manifold/Morse/SurgeryWindows/*.lean`
