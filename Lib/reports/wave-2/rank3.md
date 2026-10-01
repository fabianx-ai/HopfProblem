# Wave 2 receipt: `Lib/Geometry/Manifold/Whitney/RankThreeModel.lean` (NAME = rank3)

Model: Claude Opus 5.5 (`claude-opus-5-5`). Start 2026-10-01 19:59 CEST, end 2026-10-01 20:30 CEST.
Branch `wave2/rank3`, base `3760f829`. Judgement entry: `Lib/reports/round-7/judgement/monoliths.md`,
verdict C (dimension fixed at rank three; its "no docstrings" was stale: 160/160 already had one).

## The cut

`split_module.py` was run once per piece on the original source (stay set = every constant not in
the piece; plan in `rank3/plan.py`, line ranges = `dump_head.jsonl` ranges); twelve move files,
receipts in `rank3/split_module/<Piece>.json`. Only the header (imports, module docstring) of each
move file was replaced. Verbatimness: the tool's per-unit SHA-256 receipts, and the multiset of
non-blank body lines of the twelve pieces equals that of the original (2896 lines). Units: 160
(3+25+34+20+17+5+27+6+9+6+5+3), 269 ranged constants, no unit refused.

Pieces live in `Lib/Geometry/Manifold/Whitney/RankThreeModel/`:

| piece | original lines (base) | declarations | textbook topic |
|---|---|---|---|
| `GraphMotion` | 44–465 | 25 | planar graph motion of the Whitney pair model (push across the disc) |
| `Model` | 466–611, 2490–2511, 2596–2606, 2889–2926 | 34 | rank-three model, its sheets, their intersection |
| `SheetRetiming` | 936–1089, 2233–2262 | 20 | retimed strip transitions (chain rule) |
| `SheetCorrection` | 1192–1361 | 17 | centred correction of a map along two sheets |
| `TangentAdaptedChart` | 728–935, 1090–1191 | 5 | charts adapted to the sheet tangents (opposite-sign condition) |
| `CorrectedCoordinates` | 1362–1974 | 27 | corrected coordinates straightening the sheets |
| `SheetRecognition` | 2173–2232, 2358–2489 | 6 | recognising a sheet in a chart near a compact set |
| `SheetParametrizedChart` | 1975–2172, 2263–2357, 2513–2595 | 9 | charts parametrising both sheets |
| `CompatibleChart` | 2608–2738, 2927–3002 | 6 | standard neighbourhood of the Whitney disc |
| `ModelGraphMotion` | 612–727, 2739–2837 | 5 | rank-three graph motion, transported to the manifold |
| `IntersectionRemoval` | 2838–2888 | 3 | set lemmas: a map supported in `U` removes exactly the intersections in `U` |
| `Cancellation` | 3003–3100 | 3 | Whitney's lemma in the model (`exists_rankThree_relative_cancellation`) |

(Declarations = top-level commands, 160 in all.) Every module docstring states the mathematics and
cites Milnor, *Lectures on the h-cobordism theorem*, §6 (section only; no theorem number cited).
`RankThreeModel.lean` is a facade: rewritten module docstring listing the pieces, twelve imports,
nothing else. Consumers (`Lib.lean`, `Lib/Geometry/Manifold/Morse/BeltCancellation.lean`,
`Hopf/SingularHomology.lean`, `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean`) unchanged.
The `EmbeddedArcs` import is kept as is (in `GraphMotion`, `SheetRetiming`, `SheetRecognition`).

Imports: pieces that import a sibling dropped `import Mathlib` and `import …EmbeddedArcs` (implied);
`IntersectionRemoval` imports `Mathlib` only; `GraphMotion`, `SheetRetiming`, `SheetRecognition` keep
the original two lines (narrowing `import Mathlib` not attempted). The base had no `set_option`,
no kitchen-sink `open scoped`, no `universe` (already removed in round 7).

## `Hopf/Proof` moves: none

Closure (`rank3/closure.py` over `dump_head.jsonl`): the `Lib` module
`Lib.Geometry.Manifold.Morse.BeltCancellation` uses `TubularBigon.exists_rankThree_relative_cancellation`,
`SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal` and
`SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed`; backward closure = 221 of 269 ranged
constants, i.e. the whole rank-three chain must stay in `Lib`. The 48 free constants are fields of
needed structures (inside needed units), three `rfl` value lemmas (`firstSheetDerivative_apply`,
`secondSheetDerivative_apply`, `centerProjection_apply`),
`WhitneyPairModel.GraphMotion.firstSheet_ne_secondSheet`, and the two planar variants
`TubularBigon.TangentAdaptedChart`, `TubularBigon.SheetParametrizedChart` (no consumer anywhere; see
Left). Nothing is moved.

## Renames, lifts, docstrings

- Renames: none (no `mo1973` name); `rank3/rename.txt` is empty.
- Universe lifts: none (all binders are already `Type*`; no `.{0}`).
- Docstrings: 160 top-level declarations, 160 with a docstring before and after (computed by a scan
  of each piece for `def|theorem|lemma|structure|abbrev|instance|class` preceded by `-/`); 0 added,
  0 rewritten. Module docstrings: 12 new, facade rewritten.

## Checks (verbatim tails, all under nohup, `taskset -c 6,7,8`)

- `lake build Lib.Geometry.Manifold.Whitney.RankThreeModel` (after the import trim):
  `✔ [8855/8855] Built Lib.Geometry.Manifold.Whitney.RankThreeModel (2.6s)` /
  `Build completed successfully (8855 jobs).` — no warning from the twelve pieces.
- `lake build Lib`: `✔ [9289/9290] Built Lib (3.3s)` / `Build completed successfully (9290 jobs).`
- `lake build Solution S6Shortcuts S6 Challenge`:
  `info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]` /
  `Build completed successfully (9349 jobs).`
- `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit`: `Build completed successfully (9292 jobs).`;
  3302 `depends on axioms` reports, union of axioms `{propext, Classical.choice, Quot.sound}`, no
  `sorryAx`.
- `python3 scripts/lib_stock_census.py --check`: `ratchet PASS: 123 <= baseline 1648`.
- `grep -rn '^import Hopf' Lib/ --include=*.lean`: empty. (Without `--include` it lists 9 lines in
  `Lib/docs/**` `.md`/`.txt` logs, identical at the base.)
- dump: `dump: 38305 constants from #[Solution, Lib] under #[Hopf, Lib]; rename map: 0 entries`.

## envdiff (`rank3/envdiff.txt`, `rank3/envdiff.json`)

`lost 1 added 5 of which source declarations: 0 0 ; names with changed type 1 of which source: 0`,
`VERDICT PASS`. Module moves 3+15+27+50+3+34+20+17+31+6+20+43 = 269 source constants, each into the
piece of the plan (checked name by name against `plan/assign.json`: 0 mismatches); 0 ambiguous.
Auxiliary only: added `RankThreeWhitneyModel.lowerSheetCoordinates._proof_1`,
`WhitneyPairModel.halfTimeDerivative._proof_1/2/3` (proof terms the base shared with earlier
declarations of the same module, now re-abstracted in their own piece) and
`WhitneyPairModel.sheetTimeCoordinates.eq_1` lost/added with a new hash (equation lemma realized in
the new module); 152 auxiliary constants changed module.

## Left

1. Dimension still fixed at rank three (the judgement's suggestion: general `k + l = n`); the chain
   cannot go to `Hopf/Proof` because `Lib` uses its conclusion:
   `grep -n 'exists_rankThree_relative_cancellation' Lib/Geometry/Manifold/Morse/BeltCancellation.lean`.
2. Unused planar variants `TubularBigon.TangentAdaptedChart` (in `TangentAdaptedChart`) and
   `TubularBigon.SheetParametrizedChart` (in `SheetParametrizedChart`): no consumer in `Lib`, `Hopf`
   or the roots; kept (moving them to `Hopf/Proof` would need an artificial import to stay in the
   build; deleting is out of scope):
   `grep -rnE '\b(TangentAdaptedChart|SheetParametrizedChart)\b' --include=*.lean Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean | grep -v 'RankThree\(TangentAdapted\|SheetParametrized\)Chart'`.
3. Project vocabulary `native*` not renamed (`nativeFirstSheet`, `nativeSecondSheet`,
   `nativeFirstSheet_eq`, `nativeSecondSheet_eq`, `exists_native_cancellation`,
   `exists_supported_native_bigon_cancellation`, `lower_native_parameters`,
   `upper_native_parameters`; e.g. `chartFirstSheet` would fit):
   `grep -rnE '^(theorem|def) \S*[nN]ative' Lib/Geometry/Manifold/Whitney/RankThreeModel/`.
4. Near-twins, not duplicates (different models): `WhitneyPairModel.GraphMotion.firstSheet_ne_secondSheet`
   vs `RankThreeWhitneyModel.GraphMotion.firstSheet_ne_secondSheet`, `WhitneyPairModel.verticalGraph`
   vs `RankThreeWhitneyModel.verticalGraph` (same definition text, same proof pattern):
   `grep -rn 'firstSheet_ne_secondSheet\|def .*verticalGraph' Lib/Geometry/Manifold/Whitney/RankThreeModel/`.
5. `SupportedDiffeomorph.*` set lemmas (`IntersectionRemoval`) are about `X ≃ X` and would fit a
   general `Logic/Equiv` or `Data/Set` home; kept in the Whitney tree so as not to edit another file:
   `grep -n '^theorem' Lib/Geometry/Manifold/Whitney/RankThreeModel/IntersectionRemoval.lean`.
6. `import Mathlib` not narrowed in `GraphMotion`, `SheetRetiming`, `SheetRecognition`,
   `IntersectionRemoval`: `grep -n '^import Mathlib' Lib/Geometry/Manifold/Whitney/RankThreeModel/*.lean`.
