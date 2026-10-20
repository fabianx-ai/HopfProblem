# Monolith wave 2 (batch 2) — merge receipt (2026-10-01)

Base `3760f829` (`lib/integration` after wave 1). The 13 remaining monoliths, one worktree and branch
`wave2/<name>` each; rules `RULES.md` beside this file (wave 1's rules plus: the progress file, the
permission to rewrite vague or wrong docstrings in a comment-only commit, model and wall-clock lines in the
receipt). Owner's instruction of 2026-10-01: at most three seats at a time, merge, then the next three; and
a model comparison. Four batches of three; per-seat receipts `<name>.md` and artefacts `<name>/` beside this
file. Merged `--no-ff` in arrival order, zero conflicts:

| # | branch | merge | model | file(s) | Lib pieces | `Hopf/Proof` | commits | renames | docstring work |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `wave2/collar` | `609c2ac9` | Fable 5.1 | `Geometry/Manifold/Collar` 2,541 lines | 8 | 0 | 2 | 0 | — |
| 2 | `wave2/riemann` | `870df138` | Opus 5.5 | `Analysis/Complex/RiemannMapping` 2,400 | 9 | 2 (43 declarations) | 5 | 0 | 85 rewritten |
| 3 | `wave2/morselemma` | `5b1b6a18` | Opus 5.5 | `Analysis/Calculus/MorseLemma` 2,469 | 16 | 0 | 4 | 0 | 8 added |
| 4 | `wave2/windows` | `9380c3de` | Opus 5.5 | `Morse/SurgeryWindows` 1,969 | 11 | 0 | 6 | 0 | 26 fields added, 44 rewritten (2 wrong) |
| 5 | `wave2/height` | `2d82a8ab` | Fable 5.1 | `Flow/HeightTranslating` 1,824 | 7 | 0 | 5 | 0 | 47 restated (3 wrong) |
| 6 | `wave2/existence` | `415f0a34` | Opus 5.5 | `Morse/Existence` 2,236 | 10 | 0 | 5 | 0 | 8 fields added, 9 wrong ones rewritten |
| 7 | `wave2/cleanstrips` | `9aabbbe0` | Opus 5.5 | `Whitney/CleanStrips` 2,894 | 10 | 0 | 5 | 3 | 49 fields added |
| 8 | `wave2/cubic` | `1399ede8` | Fable 5.1 | `Morse/Cubic` 2,689 | 13 | 0 | 4 | 5 (`MorseCancellation.*tanh*` → `Real.*`) | 85 rewritten (4 wrong) |
| 9 | `wave2/transversality` | `3152a177` | Opus 5.5 | `Transversality/Basic` 3,220 | 13 (beside `Basic.lean`, no `Basic/`) | 0 | 3 | 0 | — |
| 10 | `wave2/cube3` | `0f3daa87` | Opus 5.5 | `Topology/Dimension/CubeBoundaryThreeCells` 2,338 | 7 | 0 | 6 | 0 | 94 comments → docstrings, 19 rewritten |
| 11 | `wave2/rank3` | `dc55b6c9` | Opus 5.5 | `Whitney/RankThreeModel` 3,100 | 12 | 0 | 3 | 0 | — |
| 12 | `wave2/whitney` | `63337fee` | Opus 5.5 | `Whitney/FrameField` 2,774, `Whitney/EmbeddedArcs` 3,463 | 25 | 0 | 5 | 9 (`NativeSheetCoordinates.*` → `SliceChart.*`, `…_dim_two` → `…_of_two_le_finrank`) | 1 |

53 non-merge commits, 373 files. 141 new `Lib` modules and 2 under `Hopf/Proof` (corrected 2026-10-02 after the
review `Lib/reviews/REVIEW-WAVES.md`: this said 151; the table column sums to 141); 2,072 ranged declarations
changed module over 143 module pairs (envdiff prints 2,035 over 142 because it leaves out the 37 hash-changed
names and with them the piece `MorseLemma/Congruence`), 43 of them to `Hopf/Proof` (the triangle normalisation and sector roots of
`RiemannMapping`). Nothing deleted, no statement changed, 17 renames (`rename_all.txt`). With wave 1 all 24
monoliths are split: no file under `Lib/` exceeds 1,800 lines except `Lib/AxiomAudit.lean` (the probe list);
20 files exceed 1,000 lines (list in the final-check log, largest `Hurewicz/CubeGluing.lean` 1,686).

## Checks on the merged head `63337fee` (run by one Opus 5.5 seat, read-only)

| check | result |
|---|---|
| `lake build Lib` | green, 9,419 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,480 jobs; `mathoverflow_1973` on `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` | green; 3,298 + 4 probes (+ 12 axiom-free), only `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` 0 |
| `scripts/lib_stock_census.py --check` | 123, ratchet PASS |
| `grep -rnE '^(public )?import Hopf' Lib/ --include=*.lean` | empty |
| `.{0}` in `Lib/**/*.lean` | 278, unchanged (268 in source + the two wave-1 lift-check scratch files) |
| facades | all 24 contain only `module`, imports and a module docstring |
| environment diff (`envdiff.{json,txt}` here; base dump of `8eba3d72`, after dump of `63337fee` under `rename_all.txt`, 17 lines) | 38,301 → 38,373 constants; lost 0 / added 0 source; 2,035 source declarations moved 1-to-1 over 142 module pairs (2 pairs, 43 declarations, into `Hopf.Proof.Analysis.Complex.RiemannMapping.*`); 0 ambiguous; 37 source types changed, all classed `PROOF-NAMING` by the tool and exactly the union of the branch receipts: 2 `DiskFraming.*` (`collar.md`) and 35 `SmoothMorseLemma.*` (`morselemma.md`). Corrected 2026-10-02 after the review: the 2 `DiskFraming` changes are NOT proof naming but an instance-path change caused by `wave2/collar` dropping `set_option maxSynthPendingDepth 3` (old and new statements are definitionally equal, proved by the reviewer; restored by the fix round); the 35 come from `MorsePerturbation.coordinateGradient._proof_1..3` being re-abstracted as `SmoothMorseLemma.Bilinear._proof_1..3` in the new module, not from the `symmetricForms` obligations. Verdict PASS |

## Things a reviewer should look at

- **Visibility widened in `CubeBoundaryThreeCells`.** The file is a Lean `module` (declarations private by
  default); splitting it made 34 declarations `public` and 11 definitions `@[expose]` (names in the
  final-check log and `cube3.md`). No statement changed, but this is the wave's only API widening.
- **36 dead private lemmas** in the same file (`cube3/notneed.txt`): used by nothing in `Lib`, `Hopf`,
  `Solution`. Deletion candidates; nothing deleted.
- **289 docstrings rewritten** across six branches (85 + 44 + 47 + 9 + 85 + 19, comment-only commits; this said
  322, a figure derivable from nothing — corrected 2026-10-02). The seats report 9 + 4 + 3 + 2
  that were factually wrong before. A sample against the statements is due.
- **Deviations from the judgement packet, with reasons in the receipts**: `riemann.md` keeps the
  `logHalfStrip`/`onePointDomain`/`halfStripExp` lemmas in `Lib` (general in `D`, `a`, `c`) and says
  `RectanglePrimitive` is not a Mathlib duplicate; `cubic.md` moved nothing to `Hopf/Proof`.
- **A coordinator error, corrected by the seat**: the `cubic` brief said the file had zero consumers. The
  count behind it matched only plain `import` lines and missed `public import`; the file has seven direct
  importers and 27 `Lib` modules use its constants. The consumer counts quoted in the wave-1 and wave-2
  briefs have the same blind spot; no move rested on them (every seat ran the dump closure first).

## Model comparison (owner's request)

Same task shape, files of 1,800–3,500 lines, identical rules.

| | Fable 5.1 (3 seats) | Opus 5.5 (9 seats, 10 files) |
|---|---|---|
| all checks green, envdiff PASS, clean merge | 3 / 3 | 9 / 9 |
| tokens per seat | 170k, 218k, 243k | 181k–261k (median 219k) |
| tool calls per seat | 10, 14, 25 | 50–119 |
| re-runs checks after last edit | sometimes | always |
| docstrings rewritten when permitted | yes (47, 85) | yes (up to 85) |
| corrected a premise of the brief or judgement | 1 (cubic) | 2 (riemann), self-corrected a commit message (morselemma) |

Equal correctness at equal token counts. The owner's cost model (Fable tokens count double against usage
and cost more per token) makes Opus 5.5 the default for work seats; Fable for review and coordination.

## Left by the seats (cross-cutting; each receipt carries the greps)

- **`native*`/`Native*` and project namespaces** kept wherever consumers are many: `NativeTransversality.At`
  (82 references in 23 files), `NativeSubmersion.*`, `NativeParametrization.*`, `NativeEuclideanEmbedding.*`,
  `MorseCancellation`, `FlowConstruction` (478 uses in 49 files), `ManifoldMorse`, `DiskFraming`,
  `Hemisphere.Sphere` (32 files), `PartialChart.*` (31 files), `RiemannMapping.`/`RiemannBoundary.` prefixes
  on general lemmas. The rename wave after facade dissolution.
- **Better homes** (facade-dissolution step): `MorseBelt` → `Morse/`; `HandleCoordinates`, `DescentModel`,
  `AttachingUnion` → `Morse/HandleAttachment`; seven `MorseLemma` manifold pieces → `Geometry/Manifold/Morse/`;
  `ModulusOneReflection` → beside `SchwarzReflection`; `BeltIntersection` → `Morse/`; `Tanh` → Mathlib
  `Artanh`; `SublevelFlow` → `Dynamics/Flow`; `SmoothApproximation`, `LocalReplacement` → `Geometry/Manifold`;
  `SphereCoordinates.ofLinearIsometry` → `SurgeryWindows`; tube lemmas (`isOpen_forall_mem_compact`,
  `DiskFraming.exists_pos_prod_closedBall_subset`) → topology.
- **Twins, nothing deleted**: `MorsePerturbation.hessianEquiv` vs `SmoothMorseLemma.hessianEquiv`; three
  Hausdorff-dimension lemmas in `SurgeryWindows`; `PlanarFrame.area`/`determinant` vs `Matrix.det_fin_two`;
  `det_of_zero_lower_left` vs `Matrix.det_fromBlocks_zero₂₁`; `RiemannMapping.unitDisc` vs
  `Complex.UnitDisc`; `Diffeomorph.toPartialDiffeomorph'` vs Mathlib's (deliberate); `SymmetricForm` vs
  `LinearMap.BilinForm.IsSymm`.
- **Statement-level items**: tubular/collar theorems need `[CompactSpace M]` (13 occurrences); the
  "every loop is nullhomotopic" predicate (21 times) instead of `SimplyConnectedSpace`; rank fixed at three in
  `RankThreeModel`; `CubeBoundaryThreeCells` is `Fin 3` only; 12–13-hypothesis theorems in `HeightTranslating`;
  fixed constants 1/3, 2/3 in `flattenTime`.
- **Project material that must stay in `Lib` until its consumers move**: the dimension-6 belt statements
  (`EmbeddedArcs/BeltBigon`), `FrameField/RankThreeFrame`, `RankThreeCorners`; two consumer-less
  `TubularBigon.*Chart` structures.
- **Hygiene**: `import Mathlib` in most pieces; `maxSynthPendingDepth 3` in three `MorseLemma` pieces
  (needed); `import all …LocalDiffeomorph` in eleven pieces; `attribute [local instance] … in` repeated;
  ~170 terse docstrings not rewritten; `closure.py`-style `uses` checks miss names used only inside
  `simpa only […]` (`NativeParametrization.line_apply`, `whitney.md` item 3).
- **Tool** (`~/lean-agent-ide`): `split_module.py --move-imports` inserts at line 1 when the source uses
  `public import` (three seats fixed headers by hand); `envdiff.txt` prints only the first 20 changed-type
  names; a legend for lost/added rows is still missing.
