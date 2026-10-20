# Integration review 5 — the parallel Claude-agent round (2026-09-14, 00:30–02:00 CEST)

Coordinator: Claude Fable 5.1 (this seat). Base: `304a0fea` (the hand-off head after integration 4 and
the owner's decision that the remainder is done by Claude agents). Ten agents ran in parallel, one per
work package of `NEXT_STEPS.md`, each in its own worktree and branch with a seeded `.lake`; two more ran
a second pass once the first-pass blockers had moved. Every agent built the full chain in its worktree
before committing; the coordinator merged the branches in arrival order and rebuilt the merged head.

## 1. What merged

| branch | package | result |
|---|---|---|
| `lib/next-docs` | items 1–4, record fixes | 4 commits, docs only: the Wang scripts brought in-tree under `Lib/docs/logs/glm/`, the wrapper prose in `Lib/README.md`/`EXTRACTION_PLAN.md`, the two C-19 retargets and the 35 count, RECEIPTS provenance of the S-path rows, the E2 review command text |
| `lib/next-circle` | item 5, 40 freed `PeriodTorusHigherHomology` rows | 16 moved to `SingularHomology/Torus.lean` (they were in `Hopf/Proof/LCP/Specialization.lean`, not CuspFilling as `FREED.md`'s header said; its `file:line` column was right); 24 blocked on stock rows of `Hopf/LCP/*` that the `lcp` branch moved in the same round |
| `lib/next-wang` | item 5, 73 freed `MappingTorusHomology.Covering` rows | 73 of 73 to `Wang.lean` (now 1,152 lines); 36 shim-alias retargets disclosed; `sum_range_shift_of_endpoints_mo1973_27356` renamed `sum_range_shift_of_endpoints_eq` |
| `lib/next-recognition` | `Hopf/Recognition.lean` stock | 87 of 213 rows to new `Hurewicz/DegreeSix.lean` (21), `SingularHomology/LocalContributionsNaturality.lean` (7), `Morse/CutTransport.lean` (59); dependencies from a `lean-agent-ide dump` |
| `lib/next-lcp` | the six small stock files | 94 of 94 rows: new `SingularHomology/TorusCoordinates.lean` (54), new `SingularHomology/FirstHurewicz.lean` (16, as `SingularChains.*`), `Pontryagin.lean` (15), `Quotient/Atlas.lean` (5), `Quotient/LocalOrbit.lean` (1), `Wang.lean` (1), `Morse/Cancellation.lean` (1), `Immersion/Relative.lean` (1); an `export` alias block for `FirstHurewicz.*` left in `Hopf/LCP/CuspFilling.lean` for three Proof consumers |
| `lib/next-singhom` | `Hopf/SingularHomology.lean` stock | 685 of 687 rows plus one `Hopf/DifferentialTopology.lean` row into seven new modules `Morse/CircleGluing`, `Whitney/CleanStrips`, `Whitney/AnnularExtension`, `Whitney/FrameField`, `Whitney/EmbeddedArcs`, `Whitney/RankThreeModel`, `Morse/BeltCancellation`; no retargets; the two CHARGED rows stay |
| `lib/next-spheretop` | `Hopf/SphereTopology.lean` stock | 331 of 585 rows into six new modules `SingularHomology/LocalDegreeNeighborhoods`, `Morse/RearrangementAmbient`, `SingularHomology/OnePointCover`, `Morse/SurgeryHomology`, `Morse/OrderedCancellation`, `Morse/AdaptedWindows`; 49 retargets, two `private` widenings |
| `lib/next-hurewicz` | item 6 and the LibShims export | four `Sphere.piN_subsingleton` theorems to `Hopf/Proof/Hurewicz.lean`; the three `SixSphereCube` data stay because stock `Hopf/Recognition.lean` uses them; the root `export HandleCoreAttachment (...)` deleted |
| `lib/next-e1` | item 9, layout split | `Morse/ConnectionCancellation.lean` + `Morse/Cancellation.lean` (601 declarations) split into `Cubic` (143, `module`), `CubicFlow` (91, `module`), `Connection` (231), `Cancellation` (136); order `Cubic -> CubicFlow -> Rearrangement -> Connection -> Cancellation`, 0 backward edges; block multiset verified 601 = 601 |
| `lib/next-importall` | item 10 | `import all` removed from `Collar`, `Flow/Compact`, `WhitneyEmbedding`, `Morse/Rearrangement` via new `Lib/Geometry/Manifold/LocalDiffeomorph.lean` (public-API constructor/destructor for `IsLocalDiffeomorphAt`, transparent `toPartialDiffeomorphUniv`, `diffeomorphOfBijective'`); `RegularLevel` (2, needs a transparent implicit-function datum), `SmoothFlow`, `MorseLemma` left with the concrete steps recorded; `Cubic`/`CubicFlow` inherit the old Cancellation line |
| `lib/next-spheretop2` | second pass | 231 of the 254 remaining rows into new `Morse/SurgeryCollapse.lean` (one module, source order); 23 CHARGED rows stay; retargets disclosed, including `SixSphereCube.X -> OnePointCollapse.X` on the four `DiskOnePointCollapse.collapse*` rows (see `NEXT_STEPS.md` §1) |
| `lib/next-recognition2` | second pass | 31 of the 126 remaining rows into new `Morse/MiddleBlocks.lean`; 34 CHARGED stay; 61 blocked by SphereTopology rows that the other second pass moved at the same time (movable next) |

Merge conflicts and coordinator fixes (all recorded in the merge commit messages):
`Lib.lean` import lists (kept both) three times; `Wang.lean` (lcp's row placed before wang's 73);
`Hopf/DifferentialTopology.lean` (a row moved by both `lcp` and `singhom`; the `lcp` destination kept,
`FrameField.isInvertible_coprod_of_bijective` removed from `Whitney/FrameField.lean`, which imports
`Immersion/Relative.lean` transitively); `Morse/Cancellation.lean` (e1's rewrite kept, lcp's appended row
re-appended); eight modules created this round imported the removed `Morse.ConnectionCancellation`,
rewritten to `Morse.Connection`.

## 2. Checks on the merged head

All checks ran on the fully merged head `60595af8` (and, before the two second passes merged, on the
first-pass head `b78cfee8`; those receipts are kept alongside). Receipts: `Lib/reports/integration-5/`.

| check | result |
|---|---|
| full chain (`lake build Lib`, then `lake build Solution S6Shortcuts S6 Challenge`) | green at `60595af8`, 8,840 + 8,879 jobs, 01:58–02:05 CEST (`build-60595af8.log`); green at `b78cfee8`, 8,838 + 8,877 jobs (`build-b78cfee8.log`) |
| axiom probes (`lake build Lib.AxiomAudit`) | 71 of 71 report only `propext`, `Classical.choice`, `Quot.sound`; the probe output at `60595af8` is line-for-line identical to `b78cfee8` (`axioms-60595af8.log`, `axioms-b78cfee8.log`) |
| statement scan (`int5_stmt_compare.py`, declaration blocks of every `Hopf/*.lean` except `LibShims.lean` at `60595af8` against `304a0fea`, wrapper and `_mo1973_n` suffixes normalised) | 11,637 declarations remain under `Hopf/`; 0 changed statements; 4 changed proofs with the same statement (one each in `Hurewicz`, `Proof/Hurewicz`, `SingularHomology`, `SphereTopology`, the shim-retarget edits); 4 new (the `Sphere.piN_subsingleton` copies in `Proof/Hurewicz.lean`); 1,552 deleted, of which 1,542 found under `Lib/` by full name, 4 moved within `Hopf/` (the same four theorems), 6 found by hand where the scan's name regex failed (four `_mo1973_n`-suffixed names, two names containing `ι`); none missing |
| stock census (`scripts/lib_stock_census.py --check`) | 123 (baseline 1,648; 1,586 at `304a0fea`): Recognition 95, SphereTopology 23, SingularHomology 2, Hurewicz 3 |
| environment diff (`lean-agent-ide envdiff`, dump of `47940380` renamed as in integration 4 against the dump of `60595af8` renamed under the same map plus the 17 additions of `rename-additions.txt`; `--accept` on the four new `LocalDiffeomorph.lean` declarations) | PASS (`envdiff-60595af8.json`, full text `envdiff-60595af8.txt`): constants 31,465 -> 31,524; 0 source declarations lost; 0 added beyond the 4 accepted; 3 source names with a changed type hash, all by the proof-naming rule (`exists_belt_whitney_cancellation_of_opposite_signs`, `exists_signed_belt_cancellation_step`, `last_index_two_collapse_is_primitive`: the type names a different shared `_proof_n` auxiliary); 37 one-to-one module moves covering 2,379 source declarations: 1,755 from `Hopf.*` into `Lib.*` or `Hopf.Proof.*`, 624 within `Lib.Geometry.Manifold.Morse` (the `Cancellation`/`ConnectionCancellation` split); 0 ambiguous; auxiliary constants 77 lost, 134 added, 69 changed, 1,209 moved (not judged). The first-pass receipt `envdiff-b78cfee8.json` is also PASS |

The 17 rename additions are the `FirstHurewicz.* -> SingularChains.*` block of the `lcp` branch and one
helper renamed by the `wang` branch; the rest of the map is the integration-4 map regenerated by
`Lib/reports/integration-4/int4_rename_map.py`.

## 3. Process notes

- Agents that launched a build with `nohup` and ended their turn "waiting for the notification" had to be
  resumed by the coordinator; the second-pass prompts say explicitly that no notification comes.
- The `spheretop` agent, killing its own stale build by command-line pattern, killed three `lake build`
  processes of other worktrees (the `singhom` and `e1` agents relaunched theirs; both ended green). The
  second-pass prompts forbid pattern kills. The coordinator hit the same trap twice on its own shell
  (`pgrep -f` matching the caller); use an anchored pattern or `/proc/<pid>/cwd`.
- `FREED.md`'s header put the 40 `PeriodTorusHigherHomology` rows in the wrong file; the table was right.
- No fresh-context reviewer ran on the moves in this round; the receipts, the statement scan and the
  environment diff stand in. A review pass is the first item of the next round.

## 4. What remains

`NEXT_STEPS.md` (rewritten): a review pass over this round's receipts first; the 123 stock rows still
under `Hopf/` (95 Recognition, 23 + 2 + 3 residue); the 24 blocked `FREED.md` rows; the de-shim pass;
6 `import all` lines; the module conversion of the 13 new non-`module` files; then the lanes and the
300 generalisations.

## 5. Review findings

Empty until the review pass of the next round runs; see `NEXT_STEPS.md` §1.
