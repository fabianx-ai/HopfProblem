# Wave 2 — `Lib/Geometry/Manifold/Flow/HeightTranslating.lean`

Base `lib/integration` at `3760f829`; branch `wave2/height`; commits `f5118fbf..` (four) plus this
receipt. Model: Fable 5.1 (`claude-fable-5-1`). Wall clock: started 2026-09-28 ~23:55 CEST (reading,
plan, tool runs; cut off shortly after midnight), resumed 2026-10-01 17:00 CEST, envdiff finished
18:29 CEST, receipt written ~18:35 CEST.

Judgement entry: `Lib/reports/round-7/judgement/monoliths.md` (verdict C; twin Milnor, *Morse Theory*,
Thm 3.1, and *Lectures on the h-cobordism theorem* §4). The file (1,824 lines, 106 declarations, 117
ranged constants counting the ten fields and the constructor of `FlowCollarData`) is cut into seven
topic modules under `Lib/Geometry/Manifold/Flow/HeightTranslating/`; the original module is a facade
(its five former imports, the seven piece imports, a module docstring listing the pieces). No
consumer was edited, `Lib.lean` was not edited.

## The cut

Lines refer to the base file. Every unit was moved by `tools/split_module.py` (seven runs on the base
source, one per piece, stay set = all other constants; receipts `height/split_<Piece>.json`). The
tool's context lines were then rewritten by a script: the old module docstring (which named
`exists_heightTranslatingFlow` and `exists_regularSublevelHomeomorph_with_level`, declarations of
`Morse/CubicFlow.lean` and `Morse/Reeb.lean`) replaced by a per-piece docstring, the imports replaced
by the modules whose constants the piece uses (dump `uses`), empty `/-! ### -/` headers removed and
five mislabelled ones renamed. Verbatimness: for each of the 106 moved units the text of the base
file at the receipt's lines (SHA-256 equal to the receipt's) was searched in the piece at commit
`f5118fbf`: 106/106 found, each exactly once.

| piece (`…/Flow/HeightTranslating/…`) | base lines moved | declarations | topic (textbook) |
|---|---|---|---|
| `EntryTime.lean` | 458–504, 649–824, 1184–1220, 1792–1824 | 20: `FlowConstruction.forwardInvariant_of_local`, `forwardInvariant_interior`, `interior_entry_of_local`, `entryTime` … `continuousOn_entryTime` (9), `entryRetraction`, `entryRetraction_inclusion`, `entryDeformation`, `entryHomotopyEquiv`, `entryTime_flow_of_le`, `entryTime_lt_of_flow_mem_interior`, `entryTime_eq_add_of_flow_pos`, `frontier_sublevel_eq_of_strict_flow` | entry time of a flow `Flow ℝ X` into a closed absorbing set, its continuity, the entry retraction and deformation (Milnor, *Morse Theory*, §3, Thm 3.1, the argument for an arbitrary flow) |
| `FlowCollar.lean` | 1224–1731 | 51 (62 constants): `FlowConstruction.FlowCollarData` and `core` … `continuous_shift`, `rescale` … `exists_rescale_eq`, `innerMap`, `innerMap_bijective`, `homeomorph` … `homeomorph_fixed_on_common_frontier` | the homeomorphism `B ≃ₜ A` along the orbits between two nested absorbing sets (Milnor, *Morse Theory*, §3, Thm 3.1) |
| `DescentFlow.lean` | 828–992 | 9: `FlowConstruction.hasDerivAt_comp_integralCurve`, `exists_regularBandField`, `exists_regularBandFlow`, `flow_fixed_of_zero`, `flow_preserves_regular`, `antitone_flow_height`, `strictAnti_flow_height`, `exists_adaptedDescentFlow`, `continuous_mvfderiv_field` | flows along which a function decreases (Milnor, h-cobordism, §3; *Morse Theory*, §3) |
| `AbsorbingSublevel.lean` | 996–1129, 1733–1790 | 6: `FlowConstruction.exists_uniform_negative_speed`, `exists_uniform_residence_bound`, `exists_uniform_criticalNeighborhood_entry`, `exists_uniform_absorbing_entry`, `exists_absorbingSublevelHomotopyEquiv`, `exists_absorbingSublevelHomeomorph_with_boundary_orbits` | uniform entry times; an absorbing set is a deformation retract of, and homeomorphic to, the sublevel (Milnor, *Morse Theory*, §3, Thms 3.1, 3.2) |
| `HandleCoordinates.lean` | 47–233 | 9: `MorseHandle.unitBallHomeomorph`, `ManifoldMorse.SignedMorseChart.handleBallCoordinates`, `normHandleMap`, `range_normHandleMap`, `attachmentBoundaryData`, `attachingCoreMap`, `attachingCoreMap_coe`, `contMDiff_attachingCoreMap_ambient`, `contMDiff_attachingCoreMap` | ball coordinates, boundary data and core attaching map of a Morse handle (cf. Milnor, h-cobordism, §3) |
| `DescentModel.lean` | 237–454 | 7: `MorseHandle.quadratic_descentFlow_lt`, `descentFlow_mem_interior_lower_union_handle`, `FlowConstruction.partialChartField_eq_mfderiv_symm`, `hasMFDerivAt_lift_partialChartCurve`, `SignedMorseChart.eventually_flow_eq_descentModel`, `flow_eqOn_descentModel`, `flow_eq_descentModel_of_mem_uIcc` | a flow agreeing with the model field in a Morse chart is the model flow (cf. Milnor, h-cobordism, §3) |
| `AttachingUnion.lean` | 506–645, 1131–1182 | 4: `SignedMorseChart.exists_local_attachingUnion_entry`, `forwardInvariant_attachingUnion`, `interior_entry_attachingUnion`, `exists_attachingUnionHomotopyEquiv` | sublevel ∪ handle is a deformation retract of the next sublevel (cf. Milnor, *Morse Theory*, §3, Thm 3.2) |

Piece imports (all `public import`, the base file is a `module`): `EntryTime ← Mathlib`;
`FlowCollar ← EntryTime`; `DescentFlow ← MorseLemma, Flow.Compact`;
`AbsorbingSublevel ← MorseLemma, EntryTime, FlowCollar, DescentFlow`;
`HandleCoordinates ← MorseLemma, Morse.Handle, RegularLevel, Morse.HandleAttachment`;
`DescentModel ← MorseLemma, Morse.Handle`;
`AttachingUnion ← MorseLemma, Morse.Handle, Morse.HandleAttachment, EntryTime, DescentFlow, AbsorbingSublevel, DescentModel`;
each also `Mathlib`. Sizes after the cut: facade 57 lines; pieces 219–567 lines.

Why the three handle pieces are under `Flow/HeightTranslating/` and not in `Morse/HandleAttachment`
(the auditors' suggestion): the rule places pieces under `<FileStem>/`; `Morse/HandleAttachment.lean`
is a file of another owner in this wave's surroundings and `AttachingUnion` depends on the flow pieces,
so it could not go below `HandleAttachment` anyway. See Left.

## `Hopf/Proof` moves and the closure argument

None. The module has no project material (no dimension-6 hypotheses, no `Hemisphere.Sphere 2`, no
`mo1973`, no receipts-as-docstrings): `grep -n -i 'mo1973\|native\|Sphere 2\|hemisphere'` over the
base file is empty. Script over `dump_head.jsonl` (`uses`): of the 117 ranged constants, 30 are used
by other `Lib` modules, 0 are used only by `Hopf`, 87 by nothing outside the module.
`Lib/AxiomAudit.lean` has no probe of a name of this module; `Hopf/Proof/AxiomAudit.lean` unchanged.

## Renames

None; `rename.txt` is empty. No `mo1973` name. The namespace `FlowConstruction` was left (see Left).

## Universe lifts

None: every declaration already has `Type*` binders.

## Docstrings

Computed over the seven pieces (heads `theorem|def|structure` at column 0; docstring = `/-- … -/`
immediately above the head or above its `attribute … in` prefix): 106 declarations, 106 docstrings
(base: 106/106); 0 private declarations. 47 existing docstrings were rewritten from binders and
conclusion (commit `2f5ee556`, comment-only; line breaks of six of them fixed in `e9cd0eea`):
20 in `EntryTime`, 27 in `FlowCollar`. Three of them were wrong: `FlowCollarData.duration` ("entry
time into the inner set"; it is the entry time into the core), `FlowCollarData.delay` ("delay before
reaching the core"; it is the entry time into `A` of the origin), `entryTime_eq_zero` ("exactly on
the set"; one implication). The 59 docstrings of the other five pieces are unchanged. Each piece has
a module docstring stating the mathematics; the facade's lists the pieces.

## Checks (all green; `taskset -c 12,13,14`)

Verbatim from `checks.log`:

```
=== lake build Lib.Geometry.Manifold.Flow.HeightTranslating (+pieces)
Build completed successfully (8719 jobs).
pieces 0
=== lake build Lib
Build completed successfully (9285 jobs).
lib 0
=== lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9344 jobs).
sol 0
=== lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
audit 0
Build completed successfully (9287 jobs).
=== census
  extracted (no longer under Hopf/): SphereCone
ratchet PASS: 123 <= baseline 1648
```

Axiom audit (all `depends on axioms: […]` entries of the log, multi-line ones included): 3,172 ×
`{propext, Classical.choice, Quot.sound}`, 120 × `{propext, Quot.sound}`, 10 × `{propext}`, 12 ×
"does not depend on any axioms"; no `sorryAx`. `grep -rn '^import Hopf\|^public import Hopf' Lib/
--include=*.lean`: empty. (`grep -rn '^import Hopf' Lib/` without the filter: 9 hits, all in
`Lib/docs` `.md`/`.txt` logs, the same 9 as `git grep -n '^import Hopf' 3760f829 -- Lib/`.) Build
warnings in the pieces: 0.

## envdiff

`dump_after.jsonl` from `lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` at `e9cd0eea`
(38,301 constants, rename map empty); `height/envdiff.txt`, `height/envdiff.json`:

```
constants before 38301 after 38301 (keys 38199 38199 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
       6  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.AbsorbingSublevel
       4  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.AttachingUnion
       9  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow
       7  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.DescentModel
      20  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime
      62  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.FlowCollar
       9  Lib.Geometry.Manifold.Flow.HeightTranslating -> Lib.Geometry.Manifold.Flow.HeightTranslating.HandleCoordinates
ambiguous module changes: 0
auxiliary constants that changed module: 54
VERDICT PASS
```

Moves only: 117 = 6+4+9+7+20+62+9, the plan (62 = 51 declarations + 10 fields + constructor).

## Left

- Namespace `FlowConstruction` names no object (auditors: `Flow.entryTime`, `Flow.CollarData`). Not
  renamed: the namespace is shared with ten other `Lib` files and the consumer edit is not small.
  `grep -rho 'FlowConstruction\.[A-Za-z_]*' Lib Hopf Solution.lean S6.lean S6Shortcuts.lean
  Challenge.lean --include=*.lean | wc -l` = 478 in 49 files.
- `HandleCoordinates`, `DescentModel`, `AttachingUnion` are Morse-handle material and belong under
  `Lib/Geometry/Manifold/Morse/` (with `Morse/HandleAttachment`) when the facade is dissolved:
  `ls Lib/Geometry/Manifold/Flow/HeightTranslating/`.
- `exists_absorbingSublevelHomotopyEquiv`, `exists_absorbingSublevelHomeomorph_with_boundary_orbits`
  and `SignedMorseChart.exists_attachingUnionHomotopyEquiv` keep their 12–13 explicit hypotheses; a
  "descent flow of `f`" / "absorbing set" structure would need new declarations (not this wave):
  `grep -n 'hforward\|hentry\|htop' Lib/Geometry/Manifold/Flow/HeightTranslating/AbsorbingSublevel.lean`.
- `public import Mathlib` kept in every piece and the facade (8 files):
  `grep -c '^public import Mathlib$' Lib/Geometry/Manifold/Flow/HeightTranslating.lean Lib/Geometry/Manifold/Flow/HeightTranslating/*.lean`.
- The ten fields of `FlowCollarData` have no field docstrings (the structure docstring states them):
  `grep -c '^  [a-z_]* : ' Lib/Geometry/Manifold/Flow/HeightTranslating/FlowCollar.lean` = 10.
- `open Set Function Filter Manifold Topology` / `open scoped ContDiff ContinuousMap` kept in every
  piece as in the base file; not minimised per piece:
  `grep -c '^open' Lib/Geometry/Manifold/Flow/HeightTranslating/*.lean`.
- The file name `HeightTranslating` no longer describes the content (the height-translating flow is
  in `Morse/CubicFlow.lean`); renaming the module is the facade-dissolution step.
- The 59 docstrings of `DescentFlow`, `AbsorbingSublevel`, `HandleCoordinates`, `DescentModel`,
  `AttachingUnion` are short one-liners, not restated from binders.
