# Integration review 3 — `lib/A-7-linear-sphere`, `lib/C-14-integrated-receipt`, `lib/textbook-extraction-devin-2`

Reviewer: Claude Fable 5.1 (coordinator seat). Date: 2026-09-13. Base: `97c1d21e`
(`lib/textbook-extraction` after integration review 2 plus the E1 boundary note). All three
branches fork from `37fc1de8`, one documentation commit behind the base.

## 1. What was integrated

Merged in this order onto `97c1d21e`, each as a merge commit:

1. `lib/C-14-integrated-receipt` (Kimi seat, run by Devin; 7 commits): refreshed C receipt,
   C13 instantiations in `Hopf/Recognition.lean`, C14 `Hurewicz/Naturality.lean`, C15
   `Topology/Homeomorph/DiskCube.lean` (dimension-independent), C16 rename
   `SecondHurewicz.* -> Hurewicz.DegreeTwo.*` with compatibility exports in `Hopf/LibShims.lean`,
   an archived same-family independent review.
2. `lib/textbook-extraction-devin-2` (Muse seat / Devin; 7 commits): E2 and G ledger repairs
   with two further Devin-subagent reviews each, `module`/`public` conversion of 25 provider
   files, J naturality moves into `CircleProduct.lean`/`CrossProduct.lean`, F2 bigon model
   (`Whitney/BigonModel.lean`, 52 declarations), G1 (`Morse/MinimalSystem.lean`).
3. `lib/A-7-linear-sphere` (GLM seat, run by Devin/Astra; 87 commits): E1 probe closure
   (368 declarations into `Morse/ConnectionCancellation.lean`, `Morse/RearrangementTheorem.lean`,
   `Morse/Birth.lean`), the B open-cover probe, D1 Reeb (`Morse/Reeb.lean`), D2 finite-cell
   probe, lane I quotient charts (`Covering/Quotient.lean`), `LinearSphereAction.lean` made
   Lib-only, the rename `Suspension.topSus -> Suspension`, five family-name confirmations
   against the pinned Mathlib, a 70-file documentation wave, record fixes.

Conflicts: seven files, all additive (import lines in `Hopf/LCP/CuspFilling.lean`,
`Hopf/SingularHomology.lean`, `Lib.lean`; Devin's new declarations beside GLM's docstrings in
`Analysis/Calculus/MorseLemma.lean` and `Geometry/Manifold/WhitneyEmbedding.lean`; the probe
lists in `Lib/AxiomAudit.lean`; the census baseline). Both sides kept everywhere; the baseline
was recomputed on the merged tree.

## 2. Checks on the merged head

| Check | Result |
|---|---|
| `sorry` / `axiom` in changed `.lean` files | 0 |
| `git diff --check` against the base | clean |
| `Lib.lean` | 107 modules imported; 108 `.lean` files under `Lib/` (`AxiomAudit.lean` is run, not imported) |
| Statement scan over `Hopf/` (13,309 declarations, `LibShims.lean` excluded) | 0 new, 0 changed statements, 10 changed proofs (all in `Hopf/Recognition.lean`: the C13 instantiations `SixthHurewicz.{homotopyMap, cubeChain_natural, cubeCycle_natural, cubeHomologyClass_natural, hurewiczFunction_natural, hurewiczMap_natural, hurewiczLinearEquiv_natural}`, `TopCellLifting.sphereMap_relativeDiskLifting_six`, `sphere_homotopicRel_of_topClass_eq`, `Sphere.homotopic_id_of_topClass`) |
| Declarations deleted from `Hopf/` | 551 (SingularHomology 351, SphereTopology 152, CuspFilling 24, Hurewicz 13, Recognition 6, DifferentialTopology 5); by branch: GLM 465, Devin 74, Kimi seat 12 |
| Deleted declarations present in `Lib/` under the same full name | 551 of 551 |
| Moved blocks byte-identical modulo whitespace, docstrings, `public`/`@[expose]`, a file-level `attribute [local instance] ... in` prefix, and the name maps `HigherHurewicz. -> Hurewicz.`, `FirstHurewicz. -> SingularChains.`, `PeriodTorusHigherHomology.CircleTopology -> SingularHomology.CircleTopology` | 530 |
| Moved blocks identical under the additional rename `Suspension.topSus -> Suspension` | 9 (`LinearSphereAction.lean`) |
| Moved blocks with an unchanged statement and a changed proof | 12: `DiskCube.{target, target_compact, target_convex, target_interior_nonempty, homeomorph, boundary_iff}` (C15, generalised to any dimension), `TransverseCoordinates.surjective_coprod_swap`, `PeriodTorusHigherHomology.{circleProductHomologyEquiv_symm_naturality, crossProductHomology_snd}`, `MorseCells.built_of_compact_smooth_manifold`, `SuspensionReflection.{reflect_north, reflect_south}`, `SphereReflection.sphereMap_homology`, `LinearSphereAction.{homology_of_det_pos, homology_of_det_neg}`, `homotopySixSphere_homology_subsingleton` |
| Stock census (`scripts/lib_stock_census.py`) | 2,663 -> 2,113; prefix list unchanged; ratchet PASS |
| Full chain `lake build Lib` then `Solution S6Shortcuts S6 Challenge` (worktree `lib/integration`, seeded `.lake`) | green: 8,843 jobs, `lib-exit 0`, `consumers-exit 0`, 16:49–17:03 CEST 2026-09-13 (`int3_build.log`) |
| `Lib/AxiomAudit.lean` (72 probes, includes the three E1 probes, the B, D2 and H probes, C14/C15) | 71 probes, 71 results, every axiom set within {`propext`, `Classical.choice`, `Quot.sound`} (`int3_axioms.out`) |
| Comparator (`lake exe comparator comparator/config.json`) | not run: `landrun` is not installed on this machine either; see §5 |
| Lean `module` system | 42 -> 67 `Lib/` files carry `module`; 10 `import all` lines (9 on `Mathlib.Geometry.Manifold.LocalDiffeomorph`, 1 on `Mathlib.Analysis.Calculus.Implicit`) |

Scripts: `int3_stmt_compare.py` and the block-comparison snippets in the coordinator's session
directory; the declaration-block splitter is the one used in review 2.

## 3. Findings per branch

### GLM seat (Devin/Astra)

1. **E1 is landed.** `NativeConnectionCancellationData` and its closure are gone from `Hopf/`;
   the three probe theorems are in `Lib/` and in `AxiomAudit.lean`. `E1.md` says so and keeps the
   history. The `Cubic`/`CubicFlow` split of `Cancellation.lean` stays a later layout item.
2. **B, D1, D2 probes landed**; `B.md` still carries the "[corrected] NOT complete" line above
   its new landing section, which now reads as history. One sentence at the top of `B.md`
   would settle it.
3. **`Suspension.topSus -> Suspension` was renamed** (commit `aa5288ae`) although item 1(c) of
   the previous seat file only asked to record the open item; the owner had not chosen. The
   rename follows the Mathlib `OnePoint` layout, the receipt is in `RENAMES.md`, and the old
   spelling survives for `Hopf/` through aliases in `LibShims.lean` (four uses in
   `CuspFilling.lean`). Taken; the owner's confirmation is asked for in §5.
4. **Record fixes done**: no `~/s6-notes` or `/home/` citation remains in `Lib/reports/*.md`
   from this seat.
5. **Wang** (`I.md` §"Wang ownership handoff"): the Hopf-side closure of the remaining
   `MappingTorusHomology`/`PassageHomology` rows is 232 declarations (CuspFilling 71,
   IntegralHomology 103, Specialization 43, SingularHomology 15) and does not reach
   `SpecialPeriods`, so the earlier CHARGED obstruction does not apply to this cut. The seat
   stopped because it read the circle cross-product prerequisites as C/J-owned; those are now
   in `Lib/` (`CircleProduct.lean`, `CrossProduct.lean`). Resolution in `NEXT-STEPS-GLM.md`.
6. **Documentation wave**: 70 files, no proof term changed (the statement scan and the block
   comparison agree). Files without a module docstring after the merge:
   `Hurewicz/Straightening.lean`, `SingularHomology/CrossProduct.lean`,
   `Morse/MinimalSystem.lean`, `Whitney/BigonModel.lean` (the last two are Devin's).

### Kimi seat (Devin)

1. **C13, C14, C15, C16 landed.** The ten Recognition proofs are now instantiations of the
   general theorems; the statements are unchanged. C15 generalises the disk-cube homeomorphism
   to every dimension and deletes the pinned Hopf versions (12 declarations, same names).
2. **Off-tree citations again**: `C-FOLLOWUPS-INDEPENDENT-REVIEW.md` (24 `file:///home/kimi/...`
   and `/home/kimi/s6-notes/` links) and `C-INTERFACE_RECEIPT.md` (2). The previous seat file's
   item 1 asked for exactly the opposite. The archived review is kept verbatim as an archive;
   the links are dead for every other reader.
3. **Independent review** is a fresh `devin --print` session of the same model family; it
   says so, and it counts as independent under the owner's rule above. Verdict: conditional GO for C14–C16, NO-GO for "lane complete". Its two conditions
   are owner gates: (a) the interface probe was written after the implementation, not before
   (`lean-protocol.md` Stage-2 order), to be recorded as an owner-approved exception; (b) the
   Comparator run is blocked on `landrun`. Both are put to the owner in §5.
4. **Authorship**: the seven commits are authored `Fabian Franz <fabian@isomorphic-ai.com>` with
   a Devin trailer; the seat identity asked for in the previous seat file (item 7) was not set.
5. **Gates** were run on the working tree over `f9a24ba` and are not claimed at the committed
   head (`C.md` says so). The full chain build in §2 covers the committed head.

### Muse seat (Devin)

1. **Module conversion**: 25 provider files (Morse, Flow, Collar, RegularLevel, WhitneyEmbedding,
   MorseLemma, SmoothFlow, Transversality, Immersion, CylinderHEP, HandleRetraction,
   LoopSubdivision, SimplyConnectedSphere) now carry `module`; most are lane A/D/E1 files. The
   change is header-level plus `public`/`@[expose]` markers; the block comparison shows no
   proof or statement changed by it. Ten `import all` lines reach into Mathlib internals
   (`LocalDiffeomorph`, `Implicit`); a Mathlib twin would not do that. Follow-up, not a blocker.
2. **Moves**: 74 declarations (BigonModel 52, CircleProduct 9, MinimalSystem 3, CrossProduct 2,
   and 8 spread over Quotient/SimplyConnectedCover/CellStructure by the merge with GLM's
   commits); all present in `Lib/` by name; two changed proofs (§2).
3. **Verification**: the seat built with direct `lean`, not Lake, because the shared `.lake`
   made Lake try to re-clone Mathlib (`RECEIPTS.md`); the Lake build in §2 is the first Lake
   verification of these commits.
4. **Reviews**: `E2-fresh*.md` and `G-fresh*.md` are fresh-context subagents launched by the
   seat (zero context, review only). Owner's rule (2026-09-13): a fresh-context subagent counts
   as an independent reviewer, so reviewer ≠ author is satisfied by them. Their verdicts stand:
   GO on the §§3–5 mathematics and the G ordering, NO-GO / NOT YET on the exact ledgers;
   `G.md` says "pending independent acceptance", `E2.md` says DRAFT. What is missing is the
   closing pass at the current head with a GO line, by a fresh reviewer.
5. **Off-tree citations**: `/home/ox-alpha/...` in the four review files (27 lines),
   `/tmp/sidekick-modconv-batch3-1789272770/` as the evidence directory in `RECEIPTS.md`,
   `~/s6-notes/J-review*.md` in `J.md` and `J-INTERFACE_RECEIPT.md`.
6. `MinimalSystem.lean` and `BigonModel.lean` have no module docstring.

## 4. Census prefix list

Unchanged from review 2 (`scripts/lib_stock_prefixes.txt`); the drop 2,663 -> 2,113 is the
551 deletions minus one declaration outside the list. Remaining stock by family (top):
`MorseCancellation` 251, `PeriodTorusHigherHomology` 243, `ManifoldMorse` 185,
`RiemannMapping` 114, `MappingTorusHomology` 105, `LocalDegree` 61, root-level 169.

## 5. Verdict and owner decisions

**GO.** The merged head builds through the full chain, no `Hopf/` statement changed, every deleted declaration exists in `Lib/` under its name with its statement, every probe has exact standard axioms, the census fell by the moved count. The open items are records and reviews (§3), not mathematics; the Comparator is the one gate not run here.

Owner decisions (asked in chat, recorded here once answered):

1. **Lane C gates.** (a) Accept the recorded exception: the C14–C16 interface probes were
   written after the implementation; the post-implementation review and the full chain build
   stand in for the Stage-2 order this once. (b) Comparator: install `landrun`
   (Go, `github.com/Zouuup/landrun`) on this machine and run
   `lake exe comparator comparator/config.json` once at the integrated head, or run it with the
   package's `scripts/fake-landrun.sh` (kernel check real, sandbox skipped) and record that.
2. **`Suspension.topSus -> Suspension`**: confirm the name; otherwise name the replacement and
   the GLM seat renames again with the same receipt.
3. **`module` + `import all`**: accept the conversion as the house style for `Lib/` (Mathlib is
   moving the same way) and treat the ten `import all` lines as a follow-up for the file owners.
