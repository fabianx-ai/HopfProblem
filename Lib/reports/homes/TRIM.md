# Better homes: import trim — receipt

Seat: Claude Opus 5.5 (`claude-opus-5-5`), work seat, 2026-10-11. Branch `work/trim` from `lib/integration` at
`41b46d37`; 14 trim commits (one per module), then this receipt. Not merged.

Scope: the 26 target modules of `Lib/reports/homes/envdiff.txt` (20 module moves + the 6 group targets
`SH.ModuleHomology`, `SH.MayerVietoris.SmallChains`, `SH.CrossProduct.Chain`, `SH.Chains`,
`GM.Morse.SurgeryWindows.SurgeryData`, `SH.OnePointCover`). Only `import` lines changed: no declaration,
docstring, `open`, `set_option`; `import Mathlib` / `public import Mathlib` / `import all Mathlib.*` lines
kept verbatim (checked: `git diff 41b46d37..work/trim -- '*.lean'` has no `+`/`-` line that is not an import
line). Abbreviations: `SH.` = `Lib.AlgebraicTopology.SingularHomology.`, `GM.` = `Lib.Geometry.Manifold.`,
`MorseLemma.` = `Lib.Analysis.Calculus.MorseLemma.`, other names without the leading `Lib.`.

## 1. Method

Dump of `41b46d37` in this worktree (`lake env …/lean-agent-ide dump Solution Lib Shared Center Unused S6
S6Shortcuts --modules Hopf,Lib,Shared,Center,Unused,S6,S6Shortcuts,Solution`, 39,475 constants). Script
`trim.py` (this directory; plan `trim-plan.json`, applier `trim_apply.py`), the facade seat's method
(`Lib/reports/facades/RECEIPT.md` §2) with the review correction:

- `U(X)` = defining project modules of the constants in the `uses` of X's constants, generated auxiliaries
  (`.eq_n`, `._proof_n`, `.match_n`, …) mapped to their parent; for `#check`/`#print axioms`/`example := @n`
  files the names are read from the text.
- Visibility: X sees its imports plus what they re-export; a `module` file re-exports only its
  `public import`s, a legacy file every import. Non-project modules (Mathlib) are leaves (the dump records
  project constants only; Mathlib imports are not touched). The base satisfies `U(Y) ⊆ visible(Y)` for every
  project `.lean` file except the known realization-order exception (`Lib.Topology.MappingTorus.SquareZeroWinding`
  → an equation lemma recorded in `Hopf.Proof.LCP.LocalModels`), which is ignored.
- Per X, in alphabetical order, cumulative: `need(X)` = `U(X)`; the new project imports are the antichain of
  `need(X)` (a module is dropped when another kept import re-exports it). Then every project file Y that
  (transitively) imports X is checked; a module m that Y uses and now misses, and that Y saw through X before,
  is added to `need(X)` (X keeps re-exporting what its importers rely on); repeat to a fix-point. In module
  files every project import stays `public` (as all were); legacy files keep plain `import`. New lines go
  after the retained project imports, sorted.
- Final: 0 violations over all project files.

## 2. Per module

Import lines counted with `grep -cE '^(public )?(meta )?import'` (Mathlib lines included).
Total over the 26 modules: **132 → 67** import lines; project imports **106 → 41**.
12 modules are unchanged: their import list is already the antichain of what they use.

| module | file | lines before → after | removed | added | commit |
|---|---|---|---|---|---|
| `SH.Chains` | module | 1 → 1 | — | — | unchanged |
| `SH.CrossProduct.Chain` | module | 4 → 3 | `SH.CrossProduct.Multilinear` | — | 798b4646 |
| `SH.MayerVietoris.SmallChains` | module | 2 → 2 | — | — | unchanged |
| `SH.ModuleHomology` | module | 2 → 2 | — | — | unchanged |
| `SH.OnePointCover` | legacy | 39 → 4 | `Algebra.Homology.MayerVietorisShortExact`, `Algebra.Module.IntegerPresentation`, `AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere`, `SH.Chains`, `SH.CircleProduct`, `SH.Coproduct`, `SH.HomotopyInvariance`, `SH.LinearSphereAction`, `SH.LocalContributions`, `SH.LocalDegree`, `SH.ModuleHomology`, `SH.Naturality`, `SH.Sphere`, `SH.SphereHomology`, `SH.Sum`, `SH.Suspension`, `Analysis.ODE.SmoothFlow`, `GM.Flow.Compact`, `GM.Morse.Birth`, `GM.Morse.CellStructure`, `GM.Morse.Handle`, `GM.Morse.HandleAttachment`, `GM.Morse.Index`, `GM.Morse.RearrangementAmbient`, `GM.Morse.RearrangementTheorem`, `GM.Morse.Reeb`, `GM.Morse.SublevelSets`, `GM.RegularLevel`, `GM.Transversality.Basic`, `GM.VectorBundle.ProjectionBundle`, `GM.Whitney.BigonModel`, `GM.WhitneyEmbedding`, `Topology.Homotopy.CellAttachment`, `Topology.Homotopy.HandleRetraction`, `Topology.Homotopy.LoopSubdivision`, `Topology.Homotopy.Suspension`, `Topology.OnePointCollapse` | `SH.LocalDegreeNeighborhoods`, `GM.Transversality.AmbientIsotopy` (re-export for `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks`) | 54990fd0 |
| `SH.PathComponents` | legacy | 7 → 2 | `SH.Chains`, `SH.CircleProduct`, `SH.HomotopyInvariance`, `SH.ModuleHomology`, `GM.Morse.Handle` | — | b12a4f40 |
| `SH.PuncturedBall` | legacy | 4 → 2 | `SH.LinearSphereAction`, `GM.Morse.SublevelSets` | — | c1a66993 |
| `Analysis.Complex.ModulusOneReflection` | legacy | 3 → 3 | — | — | unchanged |
| `Analysis.SpecialFunctions.SmoothTransition` | module | 6 → 1 | `GM.LocalDiffeomorph`, `GM.Morse.CubicFlow`, `GM.RegularLevel`, `GM.Transversality.Basic`, `GM.WhitneyEmbedding` | — | 6b624ad6 |
| `Dynamics.Flow.Sublevel` | module | 2 → 2 | — | — | unchanged |
| `GM.LocalReplacement` | module | 2 → 2 | — | — | unchanged |
| `GM.Morse.AdaptedDescentField` | module | 6 → 3 | `GM.Morse.CriticalPoints`, `GM.Morse.Handle`, `GM.Morse.SignedMorseChart` | — | bdc8b7a5 |
| `GM.Morse.BeltIntersection` | legacy | 3 → 3 | — | — | unchanged |
| `GM.Morse.CriticalPoints` | module | 2 → 2 | — | — | unchanged |
| `GM.Morse.DescentField` | module | 2 → 2 | — | — | unchanged |
| `GM.Morse.Existence.MorseFunction` | module | 5 → 3 | `GM.Morse.Handle`, `GM.Morse.LinearPerturbation` | — | 171528d7 |
| `GM.Morse.HandleAttachment.AttachingUnion` | module | 7 → 4 | `GM.Flow.HeightTranslating.DescentFlow`, `GM.Flow.HeightTranslating.EntryTime`, `GM.Morse.Handle` | — | 17e50981 |
| `GM.Morse.HandleAttachment.DescentModel` | module | 3 → 2 | `GM.Morse.Handle` | — | a69f5b12 |
| `GM.Morse.HandleAttachment.HandleCoordinates` | module | 4 → 2 | `GM.Morse.Handle`, `GM.RegularLevel` | — | 312c969c |
| `GM.Morse.LinearPerturbation` | module | 2 → 2 | — | — | unchanged |
| `GM.Morse.MorseBelt` | module | 2 → 2 | — | — | unchanged |
| `GM.Morse.SignedMorseChart` | module | 4 → 3 | `MorseLemma.PartialDiffeomorph` | — | 50d56452 |
| `GM.Morse.SplitChart` | module | 3 → 3 | — | — | unchanged |
| `GM.Morse.SurgeryWindows.SurgeryData` | module | 5 → 4 | `GM.Morse.Handle` | — | 3b64a75e |
| `GM.SmoothApproximation` | module | 6 → 5 | `GM.Morse.Existence.HomotopicRelWithin` | — | c40b29c2 |
| `GM.Transversality.AmbientIsotopy` | module | 6 → 3 | `GM.LocalDiffeomorph`, `GM.RegularLevel`, `GM.Transversality.Basic`, `GM.WhitneyEmbedding` | `GM.Transversality.Parametric` | 2ee835df |

## 3. Kept heavy: needed, dependency belongs elsewhere

The trim cannot remove these; each is a use of a constant whose home is outside the module's area. Moving
declarations was not this task.

| module | needed module | constants used | remark |
|---|---|---|---|
| `SH.PathComponents` | `GM.Morse.Handle` (reached through `Topology.Homotopy.CellAttachment`, the only import left) | `MorseHandle.UnitDisk` | the receipt's example; a unit disk in a Morse module |
| `SH.PuncturedBall` | `GM.Morse.SublevelSets` (via `SH.LocalDegreeNeighborhoods`) | `PuncturedBall.{Space, toSphere, fromSphere, blendVector, …}` (10) | the `PuncturedBall.*` definitions still live in `Morse/SublevelSets` (homes §6) |
| `SH.PuncturedBall` | `GM.Morse.HandleAttachment` (via `SH.LocalDegreeNeighborhoods`) | `RadialExtension.direction` | radial extension defined in a Morse module |
| `SH.OnePointCover` | `GM.Morse.Handle`, `GM.Morse.CubicFlow`, `GM.Morse.Existence.PartialChart`, `GM.Transversality.{CenteredChart, DiscTheorem}`, `GM.Immersion.Relative.PointMoving` (all via `SH.LocalDegreeNeighborhoods`) | `MorseHandle.UnitDisk`, `SupportedDiffeomorph.IsotopicToIdentity(.trans)`, `PartialChart.bijective_mfderiv`, `NativeParametrization.centered…`, `DiskShrinking.exists_embedded_disk_isotopy_of_same_center`, `MorseCancellation.exists_isotopic_pointMoving_of_path` | the homology file uses manifold isotopy lemmas |
| `SH.OnePointCover` | `GM.Transversality.AmbientIsotopy` (new direct import) | none used by OnePointCover itself | **re-export only**: `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks` uses `AmbientIsotopy` constants and saw them only through OnePointCover's old legacy import `GM.Morse.RearrangementAmbient`; kept per rule (b). A direct import in MiddleBlocks would let it go (Hopf is frozen, not done here). |
| `GM.Transversality.AmbientIsotopy` | `GM.Morse.CubicFlow` | `SupportedDiffeomorph.{IsotopicToIdentity, bumpFamily, …}` (11) | `SupportedDiffeomorph` lives in the cubic-flow module |
| `GM.Transversality.AmbientIsotopy` | `GM.Morse.SurgeryWindows.Hemisphere`, `SH.Sphere`, `MorseLemma.Cutoff` (via `GM.Transversality.Parametric` / `CubicFlow`) | `Hemisphere.{Ambient, Ball, Sphere, point}`, `SphereHomology.unitSphere_compactSpace`, `LineBundleTransport.exists_smooth_cutoff_near_closed` | general lemmas filed in Morse/homology modules |
| `GM.SmoothApproximation` | `GM.Morse.Existence.{ChartPerturbation, HomotopyCollars, PartialChart, HomotopicRelWithin}` | `ChartMapPerturbation.*` (12), `ManifoldSmoothing.*` (12), `PartialChart.restrictSource`, `HomotopicRelWithin*` (5) | the smoothing pieces stayed under `Morse/Existence` (homes §2, not in the MERGE lists) |
| `GM.Morse.Existence.MorseFunction` | `MorseLemma.Cutoff` | `LineBundleTransport.exists_smooth_extension_near_closed` | — |
| `Dynamics.Flow.Sublevel` | `GM.Flow.HeightTranslating.EntryTime` | `FlowConstruction.{forwardInvariant_of_local, interior_entry_of_local}` | general `Flow ℝ X` lemmas still under `Geometry/Manifold/Flow` (homes move 12) |
| `GM.Morse.BeltIntersection` | `GM.Whitney.CleanStrips.{CrossingChart, SphereNormal}` | `finite_transverse_intersections`, `SphereNormalCoordinates.normalJacobian(_ne_zero)` | unchanged list |

`Analysis.SpecialFunctions.SmoothTransition` now imports only `Mathlib` (its project imports were all unused).

## 4. Restorations forced by elaboration

None. Every per-module build was green on the first try with the planned list, and so was the full chain;
no instance, notation, macro or simp set was reached only through a trimmed import (the trimmed modules all
keep `import Mathlib`). Type hashes unchanged (§6), so no elaboration path changed.

## 5. Checks

Head = last trim commit. Lake `…/leanprover--lean4---v4.33.0/bin/lake`, `taskset -c 8-15`, no `-j`; logs in
`/home/goblin/.claude/jobs/06995e68/tmp/trim/final-*.log`. Per commit: `lake build <module>` rc 0 (`step.log`).

```
lake build Lib                                   Build completed successfully (9402 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9462 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8867 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9418 jobs).
  probes (grep -cE "^info: <file>.*(depends on axioms|does not depend)"):
    Lib/AxiomAudit.lean 3785   Shared/Proof/AxiomAudit.lean 53   Center/Proof/AxiomAudit.lean 9   Unused/ 34
  axiom lists (wrapped lines joined): [propext, Classical.choice, Quot.sound] 3724, [propext, Quot.sound] 126,
    [propext] 17, does not depend 14; sorryAx 0; errors 0
lake env lean Lib/reports/wave-1/prism/lift_examples.lean      exit 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root files except Center.lean→Center;
  Center→Hopf): all empty
```

## 6. Environment diff

Base `41b46d37` (`dump_base.jsonl`), after = head (`dump_final.jsonl`), same dump command; file
`trim-envdiff.json` (this directory).

```
constants before 39475 after 39475 (keys 39368 39368 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):            (none)
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

Reproduce: `python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_final.jsonl
--receipt trim-envdiff.json`, `<S>` = `/home/goblin/.claude/jobs/06995e68/tmp/trim`.

## 7. Left

- `SH.OnePointCover` imports `GM.Transversality.AmbientIsotopy` only to re-export it to
  `Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks`; drop it if MiddleBlocks ever imports it directly.
  `grep -n AmbientIsotopy Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean`
- The kept-heavy dependencies of §3 are declaration homes (rename/move wave), not import questions.
- Most dropped lines were redundant (re-exported by another import of the same file, mostly
  `GM.Morse.Handle`), so the transitive `Lib` import closures barely shrink. Closure sizes (project
  modules reachable by imports, before → after): `SmoothTransition` 114 → 0, `AmbientIsotopy` 114 → 103,
  `SH.OnePointCover` 153 → 152; all other trimmed modules unchanged (`SH.PathComponents` 63, `SH.PuncturedBall`
  150, `SurgeryData` 84, …). The heavy closures of the homology files come from what they use (§3), chiefly
  through `SH.LocalDegreeNeighborhoods` and `Topology.Homotopy.CellAttachment`.
  `git diff 41b46d37..work/trim --stat -- '*.lean'`
- Modules outside the homes scope were not trimmed (e.g. `SH.LocalDegreeNeighborhoods` now carries the
  Morse closure into `SH.OnePointCover`/`SH.PuncturedBall`).
