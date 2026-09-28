# Wave 1 — `Lib/Geometry/Manifold/Morse/Rearrangement.lean` (NAME = rearrangement)

Base `lib/integration` at `e669bc93`; branch `wave1/rearrangement`; worktree
`/home/goblin/hopf-w1-rearrangement`. Judgement entry: `Lib/reports/round-7/judgement/monoliths.md`
(verdict C, four subjects). Tooling: `split_module.py` run twelve times on the original source, one
piece per run (stay set = the piece; every unit written exactly once, verified by SHA-256 of each
unit against the receipts and by substring search in the piece files); ranges from a module-restricted
`dump` of the base (`dump_mine.jsonl`, same sources as `dump_head.jsonl`, whose full table finished
later and was used for the closure argument and `envdiff`). Receipts:
`Lib/reports/wave-1/rearrangement/split_<piece>.json`.

## The cut

Line numbers refer to the base file (2777 lines, 116 declarations = 153 ranged constants with the
structure fields). "Lines moved" is the sum of the unit line spans; the file length includes the
header, module docstring and section headers.

| piece | lines moved | declarations | textbook topic |
|---|---|---|---|
| `Lib/…/Rearrangement/TransverseChart.lean` | 193 (l.62–364, minus `exists_sheet_arc_tube`) | 10: `MorseCancellation.linearTransverseChart` … `exists_tube_support_box` | linear transverse corrections of tube charts, clean tube restrictions (Whitney trick chart bookkeeping; Milnor, h-cobordism §6) |
| `Lib/…/Rearrangement/HeightCoordinates.lean` | 122 (l.368–502) | 14: `RegularHeightCoordinates.heightMap` … `longitudinalDiffeomorph` | height map `(t, z) ↦ (F (t, z), z)` and the longitudinal diffeomorphism (Milnor, h-cobordism §4, Thm 4.1) |
| `Lib/…/Rearrangement/IntervalTranslation.lean` | 176 (l.506–699) | 17: `MorseRearrangement.IntervalTranslation` … `exists_increasing_interval_translation_with_exterior_germs`, `blendHeight` … `hasDerivAt_blended_height` | supported increasing diffeomorphisms of `ℝ`, convex blend of heights (Milnor, h-cobordism §4) |
| `Lib/…/Rearrangement/LongitudinalBlend.lean` | 96 (l.703–806) | 9: `MorseCancellation.longitudinalBlendDisplacement` … `longitudinalBlend_slices` | the model isotopy along a tube axis (Milnor, h-cobordism §4, §6) |
| `Lib/…/Rearrangement/SmoothTransition.lean` | 63 (l.808–873) | 4: `expNegInvGlue.hasDerivAt`, `Real.smoothTransition.deriv_pos`, `.strictMonoOn`, `.exists_unique_eq_of_mem_Ioo` (renamed, see below) | derivative positivity of Mathlib's `Real.smoothTransition` (upstream gap) |
| `Lib/…/Rearrangement/TubeMotion.lean` | 403 (l.877–1290) | 12: `MorseCancellation.LongitudinalTubeMotion` (+25 fields) … `LongitudinalTubeMotion.whole_sheet_transverse` | supported isotopy moving a point along a tube; single transverse sheet crossing (Whitney trick local model, Milnor §6) |
| `Lib/…/Rearrangement/LevelTime.lean` | 253 (l.1624–1688, 2073–2270) | 8: `FlowCancellation.native_flow_eq_on_{positive,negative}_halfline`, `exists_level_crossing_of_endpoint_limits`, `SmoothODE.scalar_partial_invertible`, `exists_smooth_scalar_time_germ`, `FlowCancellation.exists_native_smooth_time_germ`, `smooth_signed_level_time`, `exists_native_level_flow_cylinder` | flow-line agreement, implicit-function germ of a scalar time, flow-out of a regular level (cf. Lee, Smooth Manifolds, ch. 9; Milnor, Morse Theory §3) |
| `Lib/…/Rearrangement/BasinImages.lean` | 451 (l.1424–1621, 1690–1956) | 19: `AdaptedWindows.exists_forward_basin_smooth_images` … `exists_low_backward_obstruction_images` | basins as countable unions of smooth ball images; endpoint obstruction = complement of a level basin (stable/unstable disks, Milnor §4) |
| `Lib/…/Rearrangement/LevelConnectedness.lean` | 192 (l.1960–2068, 2274–2361) | 8: `MorseCancellation.contMDiff_discrete_family` … `AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions` | joining in sublevels/basins; regular level path connected under index bounds (general position, cf. Milnor §4) |
| `Lib/…/Rearrangement/AmbientTransversality.lean` | 362 (l.2405–2776) | 11: `MorseRearrangement.native_transverse_dimension_bound`, `NativeTransversality.Patch` (+12 fields) … `exists_ambient_disjoint_diffeomorph_of_dimension` | transversality/disjointness by an ambient isotopy (Guillemin–Pollack ch. 2 §3) |
| `Hopf/Proof/…/Rearrangement/SheetArc.lean` | 229 (l.168–266, 1292–1420) | 2: `MorseCancellation.exists_sheet_arc_tube`, `exists_clean_two_sheet_arc_avoiding` | dimension 5, 2-sheets (project) |
| `Hopf/Proof/…/Rearrangement/MiddleLevel.lean` | 38 (l.2363–2401) | 2: `AdaptedWindows.pathConnectedSpace_middle_level`, `pathConnectedSpace_index_three_upper_level` | dimension 6, index 3 (project) |

Facade: `Lib/Geometry/Manifold/Morse/Rearrangement.lean` keeps its module docstring (rewritten: the
pieces, and the correction that the Rearrangement Theorem itself lives in `RearrangementTheorem`) and
`public import`s the ten Lib pieces, nothing else. `Lib.lean` untouched; the 39 consumers unchanged
(three Hopf consumers gained an `import Hopf.Proof.…` line, see below).

Imports of the pieces: every piece keeps the original nine project imports as `public import`
(so the facade's transitive imports are those of the base file and no consumer can lose an import)
plus the earlier pieces it uses (`LongitudinalBlend` ← `HeightCoordinates`, `IntervalTranslation`;
`TubeMotion` ← `TransverseChart`, `IntervalTranslation`, `LongitudinalBlend`, `SmoothTransition`;
`BasinImages` ← `LevelTime`; `LevelConnectedness` ← `LevelTime`, `BasinImages`). Not trimmed (a build
trial per piece was not quick; listed in "Left"). The subsumed line
`public import Mathlib.Geometry.Manifold.LocalDiffeomorph` was dropped. The base file had no
`set_option maxSynthPendingDepth`, no kitchen-sink `open scoped`, no `universe` (already trimmed).
Context edits by hand: the piece headers, six renamed/added `/-! ### … -/` section headers.

## Moves to `Hopf/Proof` and the closure argument

* `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/SheetArc.lean` (commit 2b1157f7):
  `MorseCancellation.exists_sheet_arc_tube` (`finrank E = 5`, sheets
  `EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)`), `exists_clean_two_sheet_arc_avoiding`
  (same, `𝓡 2` sheets).
* `Hopf/Proof/Geometry/Manifold/Morse/Rearrangement/MiddleLevel.lean` (commit 7747b4d3):
  `AdaptedWindows.pathConnectedSpace_middle_level` (`finrank E = 6`, index bounds `3`),
  `pathConnectedSpace_index_three_upper_level` (index `3`).

Closure (`closure.py` over `dump_head.jsonl`, `uses` edges, `_proof_n` included): the set of
constants reachable backwards from the four moved names contains 41 constants, all in
`Hopf.Recognition` (14), `Hopf.SphereTopology` (12), `Hopf.Proof.Final` (5), `Hopf.Proof.Recognition`
(5), `Hopf.Proof.Geometry.Manifold.Morse.CutTransport` (3), `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks`
(2) — none in a `Lib` module. Conversely, the 96 constants of the module used (transitively) by
other `Lib` modules contain none of the four. Direct users (a moved name in `uses`):
`Hopf.Recognition` (`AdaptedWindows.exists_higher_family_prescribed_passage`), `Hopf.SphereTopology`
(`MorseCancellation.exists_native_middle_level_circle_isotopy`), `Hopf.Proof.….CutTransport`
(`exists_sheet_arc_tube_with_normal_change`, `exists_relative_sheet_passages_with_normal_change`);
these three files got `import Hopf.Proof.Geometry.Manifold.Morse.Rearrangement.{MiddleLevel,SheetArc}`
immediately after their `import Lib.Geometry.Manifold.Morse.Rearrangement` line. Confirmed by
`lake build Lib` (green). No `Lib/AxiomAudit.lean` probe names a moved declaration (the only probe
into this area is `MorseRearrangement.exists_morse_rearrangement_of_no_connection`, which lives in
`RearrangementTheorem`).

## Renames (commit 1e1bd903; `rename.txt`, lines `<new> <old>`)

No `mo1973` names in the module. Four real-analysis facts filed under `MorseCancellation` were
renamed beside Mathlib's `Real.smoothTransition.contDiff` / `pos_of_pos`:

| new | old |
|---|---|
| `expNegInvGlue.hasDerivAt` | `MorseCancellation.expNegInvGlue_hasDerivAt` |
| `Real.smoothTransition.deriv_pos` | `MorseCancellation.smoothTransition_deriv_pos` |
| `Real.smoothTransition.strictMonoOn` | `MorseCancellation.smoothTransition_strictMonoOn` |
| `Real.smoothTransition.exists_unique_eq_of_mem_Ioo` | `MorseCancellation.exists_unique_smoothTransition_time` |

Statements unchanged; the only consumer outside the piece is
`MorseCancellation.nonempty_longitudinalTubeMotion` (`TubeMotion`), updated; grep over
`Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean Lib/AxiomAudit.lean` finds no other
use of the old names. One proof line was re-wrapped at 100 columns.

## Universe lifts

None: every declaration already uses `Type*`; no `Type`/`.{0}` pins in the module.

## Docstrings

Computed over the twelve pieces (declaration lines matching
`^(theorem|def|abbrev|structure|instance)`): 116 declarations, 116 with a docstring (112 in the ten
`Lib` pieces, 4 in the two `Hopf/Proof` pieces); 0 added (the judgement's "0 missing" holds). Every
piece has a module docstring stating the mathematics and the textbook item or section.

## Checks (all under nohup; Lake 5.0.0 rejects `-j3` — `error: unknown short option '-j'` — so
## the builds were pinned to three cores with `taskset -c 15,16,17` instead)

`build2.log` at 1e1bd903:

```
=== lake build (pieces, facade, Hopf/Proof pieces, edited consumers)
Build completed successfully (8870 jobs).
=== lake build Lib
Build completed successfully (9156 jobs).
=== lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9210 jobs).
=== lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9158 jobs).          (axiomaudit.log)
=== census
stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
ratchet PASS: 123 <= baseline 1648
=== grep -rn '^import Hopf' Lib/
Lib/docs/logs/devin/modconv-batch3/gate/ProbeAxioms.lean.txt:1:import Hopf.Recognition
```

Axiom audit (`axiomaudit.log`, 23544 lines): `sorryAx` occurs 0 times; the axiom sets are
`[propext, Classical.choice, Quot.sound]` (1692), `[propext, Quot.sound]` (111), `[propext]` (10), and
12 "does not depend on any axioms". The one `grep '^import Hopf'` hit is a `.txt` build log under
`Lib/docs/logs/` present at the base, not a Lean source; over `Lib/**/*.lean` the grep is empty (the
census script's own guard, which checks `.lean` files, passed).

## Dump and envdiff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib --rename rename.txt` at 1e1bd903
(`dump_after.jsonl`, 38248 constants; the base table `dump_head.jsonl` has 38248) and
`envdiff.py dump_head.jsonl dump_after.jsonl --receipt envdiff.json` (`envdiff.txt`, verbatim):

```
constants before 38248 after 38248 (keys 38146 38146 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
       2  Lib.Geometry.Manifold.Morse.Rearrangement -> Hopf.Proof.Geometry.Manifold.Morse.Rearrangement.MiddleLevel
       2  Lib.Geometry.Manifold.Morse.Rearrangement -> Hopf.Proof.Geometry.Manifold.Morse.Rearrangement.SheetArc
      23  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality
      19  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.BasinImages
      14  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates
      17  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation
       8  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness
       8  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime
       9  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.LongitudinalBlend
       4  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition
      10  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart
      37  Lib.Geometry.Manifold.Morse.Rearrangement -> Lib.Geometry.Manifold.Morse.Rearrangement.TubeMotion
ambiguous module changes: 0
auxiliary constants that changed module: 49
VERDICT PASS
```

Reconciliation: lost 0, added 0, changed types 0 — "moves only". The 153 moved source
declarations are the 116 declarations plus the 25 fields and constructor of
`MorseCancellation.LongitudinalTubeMotion` (37 in `TubeMotion`) and the 12 of
`NativeTransversality.Patch` (23 in `AmbientTransversality`); every count equals the plan
(`plan.tsv` in the receipt directory). The four renamed lemmas appear under their old names through
the rename map and are counted in `SmoothTransition` (4). The 49 auxiliary constants that changed
module are `_proof_n` / `match_n` / equation-lemma constants realised where first used (not judged).


## Left

1. `native*` vocabulary kept (consumers live in monoliths other agents are splitting now, so the
   consumer edits would collide): `FlowCancellation.native_flow_eq_on_{positive,negative}_halfline`
   (used by `Lib/…/Morse/Connection.lean`, `Hopf/Proof/…/CutTransport.lean`),
   `FlowCancellation.exists_native_level_flow_cylinder` (`BeltCancellation`, `CircleGluing`,
   `Connection`, `RearrangementTheorem`, `Hopf/SphereTopology`),
   `MorseRearrangement.{native_transverse_dimension_bound, disjoint_ranges_of_native_transverse_dimension,
   native_transverse_of_ignored_factor}` (`RearrangementAmbient`),
   `LongitudinalTubeMotion.{native_axis, native_germ}` (`Hopf/Proof/…/CutTransport.lean:785`),
   `FlowCancellation.exists_native_smooth_time_germ`, `MorseCancellation.native_coordinate_plane_trace_transverse`
   (no external consumer; could be renamed `exists_smooth_level_time_germ`,
   `coordinate_plane_trace_transverse` in a later pass), and the `NativeTransversality` namespace
   (defined in `Lib/Geometry/Manifold/Transversality/Basic.lean`, not mine).
   Reproduce: `grep -rnE 'native_flow_eq_on|exists_native_level_flow_cylinder|native_transverse|native_axis|native_germ|exists_native_smooth_time_germ|native_coordinate_plane' --include=*.lean Lib Hopf`.
2. Better homes suggested by the judgement, not taken because no such module exists (rule 1 allows
   only an *existing* better home): `Rearrangement/SmoothTransition.lean` →
   `Lib/Analysis/SpecialFunctions/SmoothTransition.lean` (and upstream to Mathlib);
   `Rearrangement/AmbientTransversality.lean` → `Lib/Geometry/Manifold/Transversality/AmbientIsotopy.lean`.
   Reproduce: `ls Lib/Analysis/SpecialFunctions Lib/Geometry/Manifold/Transversality`.
3. Import lists of the pieces not trimmed: each piece carries the base file's nine `public import`
   lines. Reproduce: `grep -c '^public import Lib' Lib/Geometry/Manifold/Morse/Rearrangement/*.lean`.
4. `MorseCancellation.exists_compatible_sheet_endpoint_orientation` (general, `TransverseChart`) is now
   used only by the moved `Hopf/Proof` lemma `exists_sheet_arc_tube`; kept in `Lib` as general
   mathematics. Reproduce: `grep -rn exists_compatible_sheet_endpoint_orientation --include=*.lean Lib Hopf`.
5. Thirteen lines over 100 columns in `TubeMotion.lean`, verbatim from the base (not reformatted:
   the split moves text unchanged). Reproduce:
   `awk 'length>100' Lib/Geometry/Manifold/Morse/Rearrangement/TubeMotion.lean | wc -l`.
6. `grep -rn '^import Hopf' Lib/` is not empty because of the base's
   `Lib/docs/logs/devin/modconv-batch3/gate/ProbeAxioms.lean.txt` (a `.txt` log); empty over `*.lean`.
   Reproduce: `grep -rn '^import Hopf' Lib/ ; grep -rn --include=*.lean '^import Hopf' Lib/`.
7. Lake 5.0.0 (Lean 4.33.0) has no `-j` option; all builds ran as `taskset -c 15,16,17 lake build …`.

