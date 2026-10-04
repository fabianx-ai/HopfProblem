# Better homes: receipt

Seat: Claude Opus 5.5 (`claude-opus-5-5`), work seat, 2026-10-04/05. Branch `work/homes` from
`lib/integration` at `d370cd8a`; 16 move commits, then this receipt. Source lists: `Lib/reports/wave-1/MERGE.md`
"Better homes not taken", `Lib/reports/wave-2/MERGE.md` "Better homes", with the details of the per-seat
receipts they cite (`wave-1/{cross,hurewicz2,morse-d,rearrangement}.md`, `wave-2/{transversality,height,
morselemma,riemann,cleanstrips,cubic,existence,collar}.md`).

Nothing moved between the four trees; every moved module and declaration stays in `Lib`. No declaration
name, statement, proof, attribute, docstring or `set_option` changed. The only text edits besides `import`
lines are two module-docstring location sentences (below) and the directory `README.md` lists.

## 1. Moves

Kind: **module** = `git mv` of the whole file (content unchanged except `import` lines naming other moved
modules), module name changes accordingly; **group** = declarations moved verbatim into an existing
module, the source module deleted (or kept, for Concatenation).

| # | old | new | kind | commit | importers rerouted |
|---|---|---|---|---|---|
| 1 | `Lib.AlgebraicTopology.SingularHomology.CrossProduct.HomologyDescent` (5 decls) | `Lib.AlgebraicTopology.SingularHomology.ModuleHomology` (appended) | group | `2bc290c9` | 1 + `Lib.lean` (dropped: already imports the target) |
| 2 | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation`: `SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo`, `SingularChains.pointChain_mem_supported` | `Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains` (appended) | group | `09e23059` | 0 (Concatenation sees the targets) |
|   | same: `SingularHomology.zeroSimplexValue_const`, `SingularHomology.crossProductZeroLeft_pointChain` | `Lib.AlgebraicTopology.SingularHomology.CrossProduct.Chain` (appended) | group | `09e23059` | 0 |
|   | same: `SingularChains.inducedChain_pointChain` | `Lib.AlgebraicTopology.SingularHomology.Chains` (appended) | group | `09e23059` | 0 |
| 3 | `Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents` | `Lib.AlgebraicTopology.SingularHomology.PathComponents` | module | `a880c05e` | 3 + `Lib.lean` |
| 4 | `Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall` | `Lib.AlgebraicTopology.SingularHomology.PuncturedBall` | module | `3d3cbe90` | 2 + `Lib.lean` |
| 5 | `Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition` | `Lib.Analysis.SpecialFunctions.SmoothTransition` | module | `f62725ab` | 1 + `Lib.lean` |
| 6 | `Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality` | `Lib.Geometry.Manifold.Transversality.AmbientIsotopy` | module | `6bf1a789` | 1 + `Lib.lean` |
| 7 | `Lib.Geometry.Manifold.Transversality.MorseBelt` | `Lib.Geometry.Manifold.Morse.MorseBelt` | module | `53ec40be` | 1 (not in `Lib.lean` before either) |
| 8 | `Lib.Geometry.Manifold.Whitney.CleanStrips.BeltIntersection` | `Lib.Geometry.Manifold.Morse.BeltIntersection` | module | `9b6d0f98` | 1 + `Lib.lean` |
| 9 | `Lib.Geometry.Manifold.Flow.HeightTranslating.{HandleCoordinates, DescentModel, AttachingUnion}` | `Lib.Geometry.Manifold.Morse.HandleAttachment.{HandleCoordinates, DescentModel, AttachingUnion}` | module ×3 | `afde69d2` | 2 + 1 internal + `Lib.lean` |
| 10 | `Lib.Analysis.Calculus.MorseLemma.{LinearPerturbation, CriticalPoints, SignedMorseChart, SplitChart, DescentField, AdaptedDescentField}` | `Lib.Geometry.Manifold.Morse.<same stem>` | module ×6 | `5faee8f2` | see below |
|   | `Lib.Analysis.Calculus.MorseLemma.Existence` | `Lib.Geometry.Manifold.Morse.Existence.MorseFunction` | module | `5faee8f2` | |
| 11 | `Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection` | `Lib.Analysis.Complex.ModulusOneReflection` | module | `592dc8dc` | 1 + `Lib.lean` |
| 12 | `Lib.Geometry.Manifold.Morse.Cubic.SublevelFlow` | `Lib.Dynamics.Flow.Sublevel` | module | `21d64212` | 1 + `Lib.lean` |
| 13 | `Lib.Geometry.Manifold.Morse.Cubic.LocalReplacement` | `Lib.Geometry.Manifold.LocalReplacement` | module | `ed6bb998` | 2 + `Lib.lean` |
| 14 | `Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation` | `Lib.Geometry.Manifold.SmoothApproximation` | module | `47cdeef9` | 1 + `Lib.lean` |
| 15 | `Lib.Geometry.Manifold.Collar.SphereCoordinates` (`SphereCoordinates.ofLinearIsometry`) | `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData` (inserted before `SphereCoordinates.standardParametrization`) | group | `00872fdc` | 1 + `Lib.lean` (both dropped) |
| 16 | `Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover` (14 decls) | `Lib.AlgebraicTopology.SingularHomology.OnePointCover` (appended) | group | `9c01c17f` | 3 + `Lib.lean` (all dropped: already import the target) |

Move 10 importers: `Flow/Compact`, `Morse/Connection/SignEnumerations`,
`Morse/Existence/{DistinctCriticalValues, RegularLocus}`, `Morse/HandleAttachment/DescentModel`, the moved
pieces' imports of each other, and `Lib.lean`; per-commit file lists: `git show --stat <commit>`.
In total 26 `.lean` files outside the moved ones had an import line rerouted or dropped (all under `Lib/`;
no importer in `Hopf`, `Shared`, `Center`, `Unused`, `S6` or the root files), plus `Lib.lean`; 7 moved files
had imports of moved siblings renamed. List: `git log -p d370cd8a..work/homes -- '*.lean' ':!Lib.lean' | grep -E '^[-+](public )?import'`.

Judgement calls inside the moves:

- **Move 2** (MERGE "six supported-chain lemmas of hurewicz2 → `SingularHomology`"): the receipt names the
  directory, not a module; each lemma went to the module defining its subject (`supportedChainSubmodule` →
  `SmallChains`, `zeroSimplexValue`/`crossProductZeroLeft` → `CrossProduct/Chain`, `pointChain` → `Chains`).
  The sixth lemma, `SingularChains.inducedChain_const` (`CubeChainDecomposition/CubeChain.lean`), stays: it
  uses `Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation` (`Hurewicz/PrismOperator/HurewiczInverse`),
  so a `SingularHomology` home would have to import Hurewicz.
- **Move 9**: placed in a new directory `Morse/HandleAttachment/` next to the module
  `Morse/HandleAttachment.lean` (the receipt: "belong under `Morse/` (with `Morse/HandleAttachment`)"); a
  plain `Morse/AttachingUnion.lean` would sit beside the unrelated `Morse/Existence/AttachingUnion.lean`.
- **Move 10**: `MorseLemma.Existence` cannot become `Lib.Geometry.Manifold.Morse.Existence`: that is the
  name of the dissolved facade, and reusing it would silently give old imports (W4W1 on `center-solution`,
  future replays) a different module. It went into the directory of that name as `MorseFunction` (the
  existence of Morse functions, beside `Existence/DistinctCriticalValues`); the directory README lists it.
  **Unsure**: the stem `MorseFunction` is my choice.
- **Move 12**: the cubic receipt names `Lib/Dynamics/Flow/Sublevel.lean` (Mathlib's `Flow` lives in
  `Mathlib/Dynamics/Flow.lean`); its one dependency, `Flow/HeightTranslating/EntryTime` (also a general
  `Flow ℝ X` file), stays under `Geometry/Manifold/Flow`.
- **Move 16**: the piece imported `Morse.SurgeryCollapse.CellExactSequence`, which imports
  `SingularHomology.OnePointCover`, so that import is not carried (cycle). No constant of it is used
  (dump `uses` over the base: the piece uses only `HomotopyInvariance`, `LinearSphereAction`, `LocalDegree`,
  `MayerVietoris.{Sequence, SingularHomology}`, `OnePointCover`, `Suspension`, all visible in the target).
  The piece's `private def OnePointCover.spherePunctureHomeomorph` keeps its name up to the private
  mangling.

Context carried into group targets: move 1 adds `open scoped BigOperators TensorProduct` before the
appended block (the target opens only `CategoryTheory`; `universe u` and the `@[expose] public noncomputable
section` exist in the target); move 16 carries its own `open …`, `open scoped ContDiff ContinuousMap`,
`noncomputable section … end` after the target's `end`; moves 2 and 15 need nothing beyond the targets'
`open` lines (`Set Function Filter (Manifold) Topology`, `ContDiff`). The deleted modules' docstrings move
with their declarations as `/-! … -/` blocks; location sentences changed: move 1 drops "the natural home is
`…ModuleHomology`, over any ring", move 16 "of `Lib.AlgebraicTopology.SingularHomology.OnePointCover`" →
"above".

Verbatim check of the group commits (multiset of removed vs added lines, `git show -U0`): commit `09e23059`
54/54 identical; `2bc290c9`, `00872fdc`, `9c01c17f` differ only by the deleted files' headers (copyright,
`module`, imports, `universe u`, section line), the rerouted import lines and the two location sentences.
Module moves: `R100` except the renamed sibling imports inside moved files (`git diff c^:old c:new`:
import lines only).

READMEs: in each source directory README the `## Modules` line of the moved piece is removed and its
descriptive bullet (the old facade docstring) gets a `(moved: now …)` line; `Morse/Existence/README.md`
lists `Existence.MorseFunction`. New directories (`Lib/Analysis/SpecialFunctions`, `Lib/Dynamics/Flow`,
`Morse/HandleAttachment/`) have no README.

## 2. Skipped

| item (MERGE) | reason |
|---|---|
| `formalMap_*` → MayerVietoris formal chains | `formalMap_comp` carries `attribute [local instance] SingularHomology.integerLinearMapModule …` (`CrossProduct/Multilinear`), and `Multilinear` imports `MayerVietoris/FormalChains`: verbatim move is an import cycle; `formalMap_prod_swap` uses `formalMap_comp`. Only `formalMap_comp_apply`, `formalMap_id_apply` could move alone; the group was kept together. |
| `SingularChains.inducedChain_const` (sixth supported-chain lemma) | uses Hurewicz's `chainAugmentation` (move 2) |
| `Negation` → `Morse/Index.lean` | cycle: it uses `nativeMorseIndex` (`Morse/CubicFlow`) and `nativeMorseCount` (`Morse/Cancellation/CriticalGerms`), both of which import `Morse/Index` |
| tube lemmas `MorsePerturbation.isOpen_forall_mem_compact`, `DiskFraming.exists_pos_prod_closedBall_subset` → topology | no existing `Lib/Topology` module for compact-product/tube lemmas; the receipts ask for "a topology file under a neutral name" (new module + rename): out of scope |
| `Tanh` → Mathlib `Artanh` | replacement by Mathlib (upstream), out of scope |
| `LogarithmicCutoff` | "has no analysis home" (undecided) |

Not in the two MERGE lists, not attempted (per-seat suggestions only): hurewicz2's
`CubeTriangulation.{sum_face_trichotomy, sum_cubeOrientation_faces}` → `CubeTriangulation.lean` and
`constantSimplexChain`/`correctedSimplexChain`; connection's `Flow/{TimeChange, Suspension,
FieldChartGluing}` and misfiled general lemmas; existence's `AttachingUnion`/`LevelSurgery`/`BeltCore` →
`HandleAttachment`, `PartialChart` → beside `PartialDiffeomorph`, the other smoothing pieces; windows'
`HausdorffDimension`/`Avoidance`/`OpenHomotopyExtension`/`DiskDouble`/`Hemisphere`; whitney's
`FrameField/{BlockDeterminant, Complement, SheetCoordinates}`, `EmbeddedArcs/{FiberRestriction,
SmallPerturbation}`; morselemma's `PartitionOfUnity`/`Cutoff`/`ParametricIntegral`; cubic's
`SurgeryWindowsExistence`; rank3's `SupportedDiffeomorph.*` set lemmas.

## 3. Checks

Head = last move commit `9c01c17f`. Lake `…/leanprover--lean4---v4.33.0/bin/lake`, `taskset -c 0-7`, no `-j`;
logs in the job scratch `…/tmp/homes/final-*.log`.

```
lake build Lib                                   Build completed successfully (9402 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9462 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8867 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9418 jobs).
  probes (grep -cE "^info: <file>.*(depends on axioms|does not depend)"):
    Lib/AxiomAudit.lean 3785   Shared/Proof/AxiomAudit.lean 53   Center/Proof/AxiomAudit.lean 9   Unused/ 34
  every 'depends on axioms' list ⊆ {propext, Classical.choice, Quot.sound}; sorryAx 0; errors 0
lake env lean Lib/reports/wave-1/prism/lift_examples.lean      exit 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root files except Center.lean→Center;
  Center→Hopf): all empty
old module names: grep -rnE '^(public )?(meta )?import (all )?<old>\s*$' over every .lean outside .lake
  (Lib, Hopf, Shared, Center, Unused, S6, root files, Lib/reports): empty for all 23 old names;
  grep -rnwF '<old>' over *.lean and *.md outside reports/reviews: only the README "(moved …)" notes
```

Base (`d370cd8a`): the same chain green (9477 jobs for `Solution Lib Shared Center Unused S6 S6Shortcuts`).
`lake build Lib` has 9402 jobs against 9405 at the facade head: the three deleted modules
(`CrossProduct.HomologyDescent`, `Collar.SphereCoordinates`, `SurgeryCollapse.OnePointCover`).

Per commit (each green before the next; `…/tmp/homes/percommit.log`): `lake build` of every `.lean` file the
commit adds or modifies (moved files, targets, rerouted importers) — rc 0 for the 15 commits up to
`00872fdc`; `9c01c17f` built the same way by hand (target + its three importers, 8945 jobs). `Lib.lean` and
the downstream closure were built only at the head.

## 4. Environment diff

Base dump: `d370cd8a` in this worktree; after: the head `9c01c17f`; both with
`lake env …/lean-agent-ide dump Solution Lib Shared Center Unused S6 S6Shortcuts --modules
Hopf,Lib,Shared,Center,Unused,S6,S6Shortcuts,Solution`. Files: `envdiff.json`, `envdiff.txt` (this directory).

```
constants before 39476 after 39475 (keys 39369 39368 )
lost 2 added 1 of which source declarations: 0 0 ; names with changed type 1 of which source: 0
auxiliary lost/added/changed (not judged): 2 1 1
module moves (source declarations, 1-to-1): 26 rows = exactly the moves of §1 (count per row in envdiff.txt;
  269 source declarations)
ambiguous module changes: 0
auxiliary constants that changed module: 199
VERDICT PASS
```

Source declarations: lost 0, added 0, changed type 0. The auxiliary difference is move 1 only:
`SingularHomology.homologyBoundaries._proof_1` and `SingularHomology.homologyDesc._proof_1` (abstracted
proof terms) are gone and one `homologyDesc._proof_1` with another type is new — in `ModuleHomology` the
abstracted proofs are numbered and shared differently; the five source declarations keep their types. The
199 auxiliary module changes are equation lemmas, `_proof_n`, `match_n` and private `_simp` auxiliaries
travelling with their parents (private mangling normalized by the tool).

Reproduce: `python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_final.jsonl
--receipt envdiff.json` with `<S>` = `/home/goblin/.claude/jobs/06995e68/tmp/homes`.

## 5. Import map for `center-solution`

Appended to `Lib/reports/center-proof/RECEIPT.md` (subsection "Better homes"). Summary: no `W4W1` /
`W4W1.lean` / `W4-W1-Solution.lean` import line on `center-solution` names a moved module (141 `Lib.`
import lines checked); the facade map's replacement list for `Lib.Analysis.Complex.RiemannMapping` names
`Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection`, which is now
`Lib.Analysis.Complex.ModulusOneReflection`. None of the old module paths exists on `center-solution`
(they are pieces of this branch's splits); the material sits there in the monoliths listed in that
subsection, where future replays must reroute.

## 6. Left

- Import lists of moved modules are verbatim, so some new homes import heavier material than their content
  needs: `Analysis/SpecialFunctions/SmoothTransition` imports `Morse.CubicFlow`, `WhitneyEmbedding`, …;
  `SingularHomology/PathComponents` imports `Morse.Handle` (`cell_old_empty_of_empty_boundary` uses
  `MorseHandle.UnitDisk`); `SingularHomology/PuncturedBall` imports `Morse.SublevelSets` (where
  `PuncturedBall.Space`/`toSphere`/`fromSphere` are defined). Trimming is an import-hygiene pass.
  `grep -n '^public import\|^import' Lib/Analysis/SpecialFunctions/SmoothTransition.lean Lib/AlgebraicTopology/SingularHomology/{PathComponents,PuncturedBall}.lean`
- Namespaces still name the old home (`MorseCancellation.*` in `SingularHomology/PathComponents`,
  `FlowCancellation.*` in `Dynamics/Flow/Sublevel`, `LocalFunctionReplacement`, `ManifoldSmoothing`):
  the rename wave. `grep -c '^theorem MorseCancellation' Lib/AlgebraicTopology/SingularHomology/PathComponents.lean`
- The `PuncturedBall.*` definitions themselves stay in `Morse/SublevelSets.lean`; only the piece moved.
  `grep -n 'PuncturedBall\.' Lib/Geometry/Manifold/Morse/SublevelSets.lean | head`
- Skipped items of §2 and the per-seat suggestions not in the MERGE lists.
- `MorseLemma.Existence` → `Morse/Existence/MorseFunction`: stem chosen here (owner may prefer another).
  `ls Lib/Geometry/Manifold/Morse/Existence/`
- NEXT_STEPS item (4) not updated (not this seat's file).
