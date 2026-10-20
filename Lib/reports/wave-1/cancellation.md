# Wave 1 — `Lib/Geometry/Manifold/Morse/Cancellation.lean`

Base `lib/integration` at `e669bc93`; branch `wave1/cancellation`. Judgement entry:
`Lib/reports/round-7/judgement/monoliths.md` (verdict C; twin Milnor, *Lectures on the h-cobordism
theorem*, Thm 5.4). The file (3,803 lines, 137 declarations, 170 ranged constants counting the
structure fields) is cut into twelve topic modules under `Lib/Geometry/Manifold/Morse/Cancellation/`;
the original module stays as a facade (module docstring + the twelve imports + its former imports
`Mathlib`, `Morse.Rearrangement`, `Morse.Connection`, kept as instructed). No consumer and no
`Lib.lean` edit.

## The cut

Lines refer to the base file. Every unit was moved by `tools/split_module.py` (twelve runs on the
base source, one per piece, stay set = all other constants, receipts in `cancellation/split_*.json`);
the tool's context lines (copyright header, imports, `open`s, `noncomputable section`/`end`, the
`/-! ### -/` section headers) were then edited by hand: the old module docstring replaced by a
per-piece docstring, empty or mislabelled section headers removed or renamed, runs of blank lines
collapsed. Verbatimness of the declarations: every moved unit's SHA-256 from the receipts (text of
the base file at the recorded lines) was searched verbatim in the final piece file — 170/170 found,
each exactly once (`$S/…` check script, and `envdiff` below).

| piece (`Lib/Geometry/Manifold/Morse/Cancellation/…`) | base lines moved | declarations | topic (textbook) |
|---|---|---|---|
| `CubicModel.lean` | 48–140, 955–1079, 2360–2458 | 22: `cancelledDescent` … `cubicDescent_zero_iff`, `transverseEnergy` … `exists_compact_fieldLyapunov`, `hessian` … `cubic_isMorse`, `NativeCubicCancellation.exists_cutoff` | the cubic local model of the cancelling pair, its cancelled field, Lyapunov function and Hessian (Milnor §5) |
| `LyapunovResidence.lean` | 845–953, 1080–1185, 1346–1428 | 9: `FlowCancellation.exists_native_lyapunov_residence`, `combine_native_residence_bounds`, `exists_perturbed_band_residence`, `MorseCancellation.exists_compact_lyapunov_residence`, `hasDerivAt_partialChart_integralCurve`, `exists_native_compact_lyapunov_residence`, `FlowCancellation.exists_uniform_directed_band_crossing`, `continuousOn_band_entryTime`, `exists_native_flow_band_crossing` | residence bounds for a flow in a compact set where a Lyapunov function decreases; uniform band crossings (Milnor §4–5) |
| `LevelExit.lean` | 213–654 | 11: `exists_backward_morse_quadratic_level_exit` … `eventually_forward_exit_in_attaching_neighborhood` | level exits of the Morse model flow near the belt/attaching spheres (Milnor §3–4) |
| `CriticalGerms.lean` | 655–794, 2459–2497, 3696–3803 | 16: `surgery_pair_band_isolation` … `nativeMorseIndex_le`, `MorseCancellationPreservation.*` (3), `nativeMorseCount` … `nativeMorseCount_adjacent_pair`, `surgery_pair_inner_band_regular` | surviving critical germs, index as germ invariant, Morse count after pair removal (Milnor §5) |
| `LogarithmicCutoff.lean` | 1728–1866 | 7: `FlowCancellation.logarithmicCoordinate` … `weighted_blend_neg` | one-variable cutoffs with `|t χ'(t)|` small |
| `TransverseGerms.lean` | 3011–3077, 3296–3390 | 7: `TransverseGerms.derivative_first_of_time_independent_label` … `exists_native_basin_sheet_factorization` | transversality through sheet factorisations (Milnor §4–5) |
| `BandHeight.lean` | 1559–1727, 1867–2263 | 27: `FlowCancellation.hasDerivAt_comp_native_integralCurve_at` … `smooth_flowBandHeight`, `hasDerivAt_flow_height_zero` … `exists_smooth_band_height_germs` | the smooth band height between two regular levels and its boundary germ corrections (Milnor §4–5) |
| `BandReplacement.lean` | 2264–2359, 2498–2570 | 11: `FlowCancellation.bandReplacement` … `exists_global_band_lyapunov`, `not_critical_of_directional_neg`, `remove_morse_band_pair` | replacing a Morse function on a band, removal of the pair (Milnor Thm 5.4, last step) |
| `CubicConnection.lean` | 141–212, 1186–1345, 1429–1558, 2571–2637 | 8: `exists_native_cubic_field_cancellation_in`, `exists_native_cancelledDescent_residence_bound`, `exists_native_cubic_field_finite_passage`, `native_cubic_axis_flow/orbit`, `native_cubic_closed_axis`, `exists_cubic_connection_finite_passage`, `cancel_unique_native_cubic_connection` | cancellation of a unique connection in the cubic model (Milnor Thm 5.4, core) |
| `ConnectionData.lean` | 795–844, 2638–3010 | 6 (+33 structure constants): `NativeConnectionCancellationData`, `cancel_unique_native_transverse_connection`, `cancel_native_endpoint_slice_data`, `….Transverse`, `….cancel`, `exists_native_connection_cancellation_data` | the cancellation datum, its transversality, its cancellation (hypotheses of Thm 5.4) |
| `BasinSheets.lean` | 3078–3295, 3391–3511 | 11: `….outgoingSheet` … `….cancel_of_transverse_basin_sheets` | stable/unstable sheets of the datum; transversality from maps into the basins |
| `LevelIsotopy.lean` | 3512–3695 | 2: `cancel_unique_connection_of_transverse_basin_sheets`, `cancel_of_transverse_level_isotopy` | the First Cancellation Theorem (Milnor Thm 5.4) |

Piece imports: the three original imports plus, by direct use (checked with the dump's `uses`):
`BandHeight ← LogarithmicCutoff`; `BandReplacement ← BandHeight, CriticalGerms`;
`CubicConnection ← CubicModel, LyapunovResidence, BandReplacement`; `ConnectionData ← CubicConnection`;
`BasinSheets ← ConnectionData, TransverseGerms`; `LevelIsotopy ← ConnectionData, BasinSheets`.
`import Mathlib` is redundant through `Morse.Connection` but was left (see Left). Sizes after the cut:
facade 61 lines; pieces 179–618 lines.

## `Hopf/Proof` moves and the closure argument

None. The module holds no project material (no dimension-6 hypotheses, no `Hemisphere.Sphere 2`, no
`mo1973`, no receipts-as-docstrings); every declaration is general Morse/flow theory. For the record
(script over `dump_head.jsonl`, `uses` field): 25 declarations are used by other `Lib` modules, 3 only
by `Hopf` (`adapted_surgeries_after_pair_removal`, `cancel_of_transverse_level_isotopy`,
`nativeMorseIndex_le`), 142 by nothing outside the module. `Lib/AxiomAudit.lean` keeps its probe of
`MorseCancellation.cancel_of_transverse_level_isotopy`; `Hopf/Proof/AxiomAudit.lean` unchanged.

## Renames

None. `grep -c mo1973 Lib/Geometry/Manifold/Morse/Cancellation.lean` at the base is 0. `rename.txt`
is the empty map. The `native*`/`Native*` vocabulary was left (see Left).

## Universe lifts

None: every declaration already has `{E M : Type*}`; the only concrete carrier is `Model m = ℝ × (Fin m → ℝ)`.

## Docstrings

Computed over the twelve pieces (heads `theorem|def|structure|noncomputable def` at column 0, docstring
= `/-- … -/` immediately above the head or above its `attribute … in` prefix): 137 declarations, 137
docstrings (base: 136; the one added is `MorseCancellation.surgery_pair_inner_band_regular`,
commit b26ee7a1). Private declarations: 0. Each piece has a module docstring stating the mathematics
and citing Milnor by section; the facade's docstring lists the pieces.

## Checks (all green; `lake` pinned to three cores with `taskset -c 9,10,11` since this Lake has no `-j`)

Verbatim summary lines from `$S/build2.log` / `$S/axiomaudit.log`:

```
=== lake build Lib.Geometry.Manifold.Morse.Cancellation (+pieces)
Build completed successfully (8756 jobs).
pieces 0
=== lake build Lib
Build completed successfully (9158 jobs).
lib 0
=== lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9210 jobs).
sol 0
=== lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9160 jobs).
audit 0
```

Axiom audit: distinct axiom sets over all `#print axioms` lines = `{propext}`, `{propext, Quot.sound}`,
`{propext, Classical.choice, Quot.sound}`; no `sorryAx`. `python3 scripts/lib_stock_census.py --check`:
`ratchet PASS: 123 <= baseline 1648`. `grep -rn '^import Hopf' Lib/`: 9 hits, all in
`Lib/docs/**/*.md|*.txt` logs, identical to the base (`git grep -n '^import Hopf' e669bc93 -- Lib/`
gives the same 9); no `.lean` file. Build warnings in the pieces: 0.

## envdiff

`$S/dump_after.jsonl` from `lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` after the
last edit (38,250 constants); `envdiff dump_head.jsonl dump_after.jsonl` (files `cancellation/envdiff.txt`,
`cancellation/envdiff.json`), verbatim summary:

```
constants before 38248 after 38250 (keys 38146 38148 )
lost 0 added 2 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 2 0
module moves (source declarations, 1-to-1):
      27  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.BandHeight
      11  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.BandReplacement
      11  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.BasinSheets
      39  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.ConnectionData
      16  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms
       8  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.CubicConnection
      22  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.CubicModel
      11  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.LevelExit
       2  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy
       7  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.LogarithmicCutoff
       9  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.LyapunovResidence
       7  Lib.Geometry.Manifold.Morse.Cancellation -> Lib.Geometry.Manifold.Morse.Cancellation.TransverseGerms
ambiguous module changes: 0
auxiliary constants that changed module: 82
VERDICT PASS
```

Source declarations: 0 lost, 0 added, 0 changed types; the 170 moves (27+11+11+39+16+8+22+11+2+7+9+7)
are exactly the plan of the table above (the 39 of `ConnectionData` are the 6 declarations plus the 33
constants of the structure `NativeConnectionCancellationData`: fields, `mk`). The two added constants
are auxiliary and not judged: `NativeConnectionCancellationData.Transverse._proof_1` (in
`ConnectionData`) and `NativeConnectionCancellationData.outgoingSheet._proof_1` (in `BasinSheets`) —
abstracted proofs that Lean previously shared with an earlier declaration of the single module and now
materialises once per piece. The 82 auxiliary constants that changed module are the `_proof_n`,
`match_n` and equation lemmas of the moved declarations.

## Left

* `native*`/`Native*` vocabulary (226 occurrences over the pieces; `grep -rn 'native\|Native'
  Lib/Geometry/Manifold/Morse/Cancellation/ | wc -l`): `NativeConnectionCancellationData`,
  `nativeMorseCount`, `exists_native_*`, `NativeCubicCancellation`, `native_cubic_*` … A Mathlib-style
  name for the datum (e.g. `MorseCancellation.CancellationData`) and `ManifoldMorse.count` for
  `nativeMorseCount` need the consumers `Lib/Geometry/Manifold/Morse/{Birth,OrderedCancellation,SurgeryCollapse}.lean`,
  `Hopf/{Recognition,SphereTopology}.lean`, `Hopf/Proof/{Recognition,Geometry/Manifold/Morse/CutTransport,Geometry/Manifold/Morse/MiddleBlocks}.lean`
  (`grep -rln nativeMorseCount Lib Hopf --include=*.lean`); `nativeMorseIndex` itself is defined in
  `Lib/Geometry/Manifold/Morse/CubicFlow.lean` (not this file). Not renamed in this wave.
* The headline `MorseCancellation.cancel_of_transverse_level_isotopy` keeps its ~25 explicit hypotheses
  (judgement finding); a restatement over a hypothesis structure is a new declaration, not a move, and
  is left for the dissolution step. `grep -n 'theorem MorseCancellation.cancel_of_transverse_level_isotopy' Lib/Geometry/Manifold/Morse/Cancellation/LevelIsotopy.lean`.
* `LogarithmicCutoff.lean` is one-variable calculus (judgement: `Analysis/SpecialFunctions`); no
  existing module there matches, so it sits under `Morse/Cancellation/`. `ls Lib/Analysis/SpecialFunctions 2>/dev/null`.
* Twins (cf., not deleted): `FlowCancellation.hasDerivAt_comp_native_integralCurve_at` (BandHeight) vs
  `FlowConstruction.hasDerivAt_comp_integralCurve` (Connection; the former assumes only
  `MDifferentiableAt` at one point); `MorseCancellation.exists_compact_lyapunov_residence`
  (normed space) vs `FlowCancellation.exists_native_lyapunov_residence` (manifold), same argument;
  `FlowCancellation.contMDiffOn_directionalDerivative` vs `MorseCancellation.contMDiff_directionalDerivative`
  (Connection). `grep -rn 'hasDerivAt_comp_native_integralCurve_at\|exists_compact_lyapunov_residence\|contMDiffOn_directionalDerivative' Lib/Geometry/Manifold/Morse/Cancellation/ | wc -l`.
* `import Mathlib` kept in every piece (redundant through `Morse.Connection`, kept with the two
  project imports as instructed): `grep -c '^import Mathlib' Lib/Geometry/Manifold/Morse/Cancellation/*.lean`.
* The facade still imports `Morse.Rearrangement` although `Morse.Connection` imports it (kept as
  instructed while both are being split).
