# Wave 2 receipt — cubic: `Lib/Geometry/Manifold/Morse/Cubic.lean`

Seat: Claude Fable 5.1 (model ID `claude-fable-5-1`). Start 2026-09-28 23:55 CEST (cut off by the rate
limit after the reading phase, no edits); resumed 2026-10-01 18:42 CEST; end 2026-10-01 19:25 CEST.
Base `lib/integration` at `3760f829`, branch `wave2/cubic`, worktree `/home/goblin/hopf-w2-cubic`.
Judgement entry: `Lib/reports/round-7/judgement/monoliths.md` (verdict C, five unrelated topics).
Commit range: `3760f829..HEAD` — `f2f390c1` (split + facade), `1edaa5d7` (rename), `ab6ac93e`
(docstrings, comment-only), then this receipt.

## Correction of the assignment's premise

The assignment said the file has zero consumers and that project-shaped material could therefore move
whole to `Hopf/Proof`. That is false at the base, and nothing was moved:

* `grep -rlE '^(public )?import Lib.Geometry.Manifold.Morse.Cubic$' Lib Hopf …` lists seven files
  (`OrderedCancellation/{MinimalSystem,ValueExchange,PairCancellation}`,
  `SurgeryCollapse/{MinimumReduction,IndexOrdering}`, `CubicFlow`,
  `Hopf/Proof/…/SurgeryCollapse/OuterIndexMinimal`), and `CubicFlow` `public import`s it for the rest
  of the Morse tree.
* `cubic/closure.py` over `dump_head.jsonl`: 70 constants of the module are used directly by 34 other
  modules (27 of them `Lib.*`: `CubicFlow` 16, `Birth` 18, `Connection.CubicFieldChart` 18,
  `Cancellation.CubicConnection` 11, …); the backward closure through `uses` from constants of other
  `Lib` modules is 166 constants = **all 142 ranged declarations** plus their auxiliaries. By rule 3
  ("only a declaration that no `Lib` file uses, directly or transitively") every declaration stays in `Lib`.

Hence no `Hopf/Proof` module, no consumer import edits, no `AxiomAudit` edit (neither audit file
mentions a `Cubic` name: `grep -n Cubic Lib/AxiomAudit.lean Hopf/Proof/AxiomAudit.lean` is empty).

## The cut

`split_module.py`, one run per piece from the base source (stay = everything else), driven by
`cubic/apply_split.py` with `cubic/plan.py`; receipts `cubic/receipts/split_<piece>.json`. 142 units,
each moved exactly once; every unit's text is checked against the receipt's SHA-256 and as a verbatim
substring of the written piece. By hand (context lines only): the piece headers (copyright, `module`,
imports, module docstring, `open …`, `@[expose] public noncomputable section`) and the removal of the
old `/-! ### … -/` section headers. All pieces are `Lib/Geometry/Manifold/Morse/Cubic/<Topic>.lean`.

| piece | lines moved | declarations | textbook topic |
|---|---|---|---|
| `SurgeryWindowsExistence` | 62 | 1 | existence of gradient-like fields adapted to Morse charts (cf. Milnor, h-cobordism §3) |
| `BasinBlock` | 587 | 15 | stable/unstable discs of a critical point in a Morse block (cf. Milnor, h-cobordism §3–§4) |
| `SublevelFlow` | 118 | 6 | flows crossing a level strictly downwards, on a topological space (cf. Milnor, Morse Theory §3) |
| `LevelOrbit` | 30 | 2 | smoothness of `df(V)`; an orbit meets a transverse level once |
| `Model` | 93 | 13 | the cubic birth–death family `x³/3 + t x + Σ σᵢ yᵢ²` and its critical points (cf. Milnor, h-cobordism §5) |
| `EndpointChart` | 99 | 11 | explicit Morse charts at the two critical points (Milnor, Morse Theory Lemma 2.2) |
| `LocalReplacement` | 111 | 10 | replacing a function inside a chart (cf. Milnor, h-cobordism §2, §4) |
| `DescentField` | 247 | 20 | the model's gradient-like field and its linearisation by a Möbius coordinate |
| `SplitCoordinates` | 423 | 24 | aligning the model with a signed Morse chart (cf. Milnor, h-cobordism §5) |
| `AlignedRays` | 380 | 14 | orbits converging to a critical point lie on the cubic axis |
| `CoreBasins` | 179 | 4 | attaching/belt spheres as level traces of the basins (Milnor's `S_L`, `S_R`, h-cobordism §3) |
| `Tanh` | 31 | 5 | `Real.tanh`/`Real.artanh` calculus (complements `Mathlib/Analysis/SpecialFunctions/Artanh.lean`) |
| `AxisParameter` | 119 | 17 | the connecting orbit `a tanh (a t)` of the model, its clock `artanh (s/a)/a` |

Total 142 declarations, 2479 unit lines. Facade: `Lib/Geometry/Manifold/Morse/Cubic.lean` keeps a
(rewritten) module docstring listing the pieces and `public import`s the thirteen pieces, nothing else;
the history note of the old docstring ("material of the former `Morse/Cancellation.lean`", import
order) is gone. `Lib.lean` unchanged; no consumer import changed.

Imports: the pure pieces import only what they use — `Model`, `Tanh`, `LocalReplacement`: `Mathlib`;
`AxisParameter`: `Mathlib` + siblings; `SublevelFlow`: `Mathlib` + `Flow.HeightTranslating`
(`FlowConstruction.forwardInvariant_of_local`); `EndpointChart`: `Mathlib` + `Morse.Existence`. The
seven chart/flow pieces keep the base's five `public import Lib.…` lines plus the siblings they use
(not trimmed; see Left). `import all Mathlib.Geometry.Manifold.LocalDiffeomorph` is kept in the nine
pieces that mention `PartialDiffeomorph` or the manifold flow and dropped from `Model`, `Tanh`,
`SublevelFlow`, `AxisParameter`. The base had no `set_option maxSynthPendingDepth`, no kitchen-sink
`open scoped`, no `universe` line (the auditors read an older revision).

## Renames (`cubic/rename.txt`, commit `1edaa5d7`)

No `mo1973` name in the file. Five real-analysis facts filed under `MorseCancellation` went to `Real`
(no clash: `grep -rn 'hasDerivAt_tanh\|strictMono_tanh\|tendsto_tanh\|contDiffAt_artanh' .lake/packages/mathlib/Mathlib` is empty):

```
Real.hasDerivAt_tanh      MorseCancellation.hasDerivAt_tanh
Real.strictMono_tanh      MorseCancellation.strictMono_tanh
Real.tendsto_tanh_atTop   MorseCancellation.tendsto_tanh_atTop
Real.tendsto_tanh_atBot   MorseCancellation.tendsto_tanh_atBot
Real.contDiffAt_artanh    MorseCancellation.contDiffAt_artanh
```

Consumers updated: `Cubic/AxisParameter.lean` (4 uses), `Morse/CubicFlow.lean:327`,
`Morse/Connection/CubicFieldChart.lean:461`.

## Lifts

None: every binder is already `Type*` (`grep -n ': Type}' Lib/Geometry/Manifold/Morse/Cubic/*.lean` empty).

## Docstrings

Every one of the 142 declarations already had a docstring at the base; 0 were missing, 0 added
(`grep -c '^/--' Lib/Geometry/Manifold/Morse/Cubic/*.lean` sums to 142). 13 module docstrings and the
facade docstring are new. 85 existing docstrings were rewritten from binders/hypotheses/conclusion in
the comment-only commit `ab6ac93e` (`cubic/docs.py`): `Model` 13, `SublevelFlow` 6, `LevelOrbit` 2,
`SurgeryWindowsExistence` 1, `EndpointChart` 11, `LocalReplacement` 10, `Tanh` 5, `AxisParameter` 17,
`DescentField` 20. Four of the old ones were wrong, not only vague: `cubic` ("`x³ + tx`"),
`critical_iff` ("`3x² + t = 0`"; the condition is `x² + t = 0`), `negative_parameter_critical_iff`
("`±√(−t/3)`"; the points are `(±a, 0)` at `t = −a²`), `forwardInvariant_sublevel_of_boundary`.
The citation "Milnor Thm 4.1" of the old module docstring and of the judgement's twin line was not
kept: the cancellation model belongs to §5 (first cancellation theorem); cited as "cf. §5".

## Checks (verbatim; all at `ab6ac93e`, `taskset -c 5,6,7`, logs `c_*.log` in the scratch)

```
lake build <facade, 13 pieces, CubicFlow, Connection.CubicFieldChart>   Build completed successfully (8801 jobs).   exit pieces 0
lake build Lib                                      Build completed successfully (9291 jobs).   exit Lib 0
lake build Solution S6Shortcuts S6 Challenge        Build completed successfully (9350 jobs).   exit Solution 0
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit     Build completed successfully (9293 jobs).   exit AxiomAudit 0
python3 scripts/lib_stock_census.py --check         stock declarations under Hopf/: 123 … ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf' Lib/ --include=*.lean       (empty)
```

Axioms: 3302 `depends on axioms` lines in the audit log (plus 12 "does not depend on any axioms") and
the one of `Solution`, every list within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
(script over the unwrapped lines).

## envdiff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib --rename rename.txt` at `ab6ac93e`
(38304 constants) against `dump_head.jsonl` (38301); `cubic/envdiff.{txt,json}`:

```
constants before 38301 after 38304 (keys 38199 38202 )
lost 11 added 14 of which source declarations: 0 0 ; names with changed type 4 of which source: 0
auxiliary lost/added/changed (not judged): 11 14 4
module moves (source declarations, 1-to-1): 13 pairs, 142 declarations = the plan
  (14 AlignedRays, 17 AxisParameter, 15 BasinBlock, 4 CoreBasins, 20 DescentField, 11 EndpointChart,
   2 LevelOrbit, 10 LocalReplacement, 13 Model, 24 SplitCoordinates, 6 SublevelFlow,
   1 SurgeryWindowsExistence, 5 Tanh)
ambiguous module changes: 0
auxiliary constants that changed module: 42
VERDICT PASS
```

`plan_resolved.json` against `dump_after.jsonl`: 142 planned, 0 missing, 0 in a wrong module.
Auxiliary differences, name by name (no source declaration among them):

* seven `MorseCancellation.hasDerivAt_tanh._simp_1_{1..7}` lost and seven
  `Real.hasDerivAt_tanh._simp_1_{1..7}` added with identical hashes: the generated simp lemmas of the
  renamed theorem (the rename map covers user-facing names, not their generated children);
* four equation lemmas listed as lost and added (= the four "changed type"):
  `endpointCoordinate.eq_1`, `endpointDomain.eq_1`, `endpointLinearField.eq_1`,
  `splitTransverseChange.eq_1` — realised where first used, now in a piece, with re-abstracted proofs;
* three new abstracted proofs: `endpointCoordinate._proof_1`, `endpointLinearField._proof_1`,
  `selectedMorseFieldEquiv._proof_1` (a proof shared module-wide in the monolith is now realised once
  per piece).

## Left

1. Project vocabulary kept: `native*` names (`exists_native_morse_field_block`,
   `native_attaching_core_flow`, `nativeCubicDescent`, `native_same_level_orbit_points`, …), used by
   ~30 consumer modules, so the rename is not small. `grep -rn 'native' Lib/Geometry/Manifold/Morse/Cubic/ | wc -l` → 59.
   The namespaces `MorseCancellation`, `FlowCancellation`, `LocalFunctionReplacement` likewise.
2. 57 docstrings of `BasinBlock` (15), `SplitCoordinates` (24), `AlignedRays` (14), `CoreBasins` (4)
   are still the base's one-line summaries ("A native Morse field block exists."); the module
   docstrings state the mathematics. `grep -c '^/-- .*\. -/$' Lib/Geometry/Manifold/Morse/Cubic/{BasinBlock,SplitCoordinates,AlignedRays,CoreBasins}.lean`
3. Better homes that do not exist yet (rule 1 allows only an existing module): `Cubic/SublevelFlow` →
   `Lib/Dynamics/Flow/Sublevel.lean`; `Cubic/LocalReplacement` → `Lib/Geometry/Manifold/LocalReplacement.lean`;
   `Cubic/Tanh` → Mathlib `Analysis/SpecialFunctions/Artanh.lean` (upstream patch);
   `Cubic/SurgeryWindowsExistence` → beside `Morse/SurgeryWindows`. `ls Lib/Dynamics Lib/Analysis/SpecialFunctions` (both absent).
4. `MorseCancellation.flow_formula_of_local_shifts` (a general `Flow ℝ X` fact) sits in `AlignedRays`
   with its only user; `exists_negative/positive_core_ray_parameter` (polar coordinates in a normed
   space) sit in `BasinBlock`. `grep -n 'flow_formula_of_local_shifts\|core_ray_parameter' Lib/Geometry/Manifold/Morse/Cubic/*.lean`
5. `splitLinear`/`splitEquiv` over `Option (Fin m) ≃ Fin n` are an ad-hoc reindexing (auditors:
   Mathlib would use `Fin.consEquiv`/`finSuccEquiv`); unchanged. `grep -n 'def MorseCancellation.split' Lib/Geometry/Manifold/Morse/Cubic/SplitCoordinates.lean`
6. Import lists of seven pieces not trimmed below the base's five `Lib` imports; `import all
   Mathlib.Geometry.Manifold.LocalDiffeomorph` kept in nine pieces without a per-piece trial.
   `grep -c '^public import Lib' Lib/Geometry/Manifold/Morse/Cubic/*.lean; grep -l '^import all' Lib/Geometry/Manifold/Morse/Cubic/*.lean | wc -l`
7. `attribute [local instance 100] Classical.propDecidable in` repeated per declaration (verbatim move).
   `grep -rc '^attribute \[local instance' Lib/Geometry/Manifold/Morse/Cubic/ | awk -F: '{s+=$2}END{print s}'` → 37.
8. 28 lines over 100 columns in the pieces (29 at the base, verbatim).
   `awk 'length>100' Lib/Geometry/Manifold/Morse/Cubic/*.lean | wc -l`
9. No duplicate found within the file; nothing deleted.
