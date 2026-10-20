# Unused receipt: `cube3` (the dead lemmas of `Lib/Topology/Dimension/CubeBoundaryThreeCells/`)

Agent: Claude Opus 5.5 (model ID `claude-opus-5-5`). Start 2026-10-02 00:37 CEST, end 2026-10-02 00:59 CEST.
Base `lib/integration` at `223b655d`; branch `work/unused`; commits `10504615` … the receipt commit.
Owner decision (2026-10-02): proved declarations that nothing uses are neither deleted nor kept in
`Lib`; they move verbatim to the top-level tree `Unused/` ("neither for Mathlib nor anything else,
it just exists"). This is the first case.

## Commits

| commit | step |
|---|---|
| `10504615` | `lakefile.toml` gets `[[lean_lib]] name = "Unused"` (not in `defaultTargets`); `Unused.lean`; `Unused/README.md` |
| `be34c96f` | the move: 36 declaration blocks into `Unused/Topology/Dimension/CubeBoundaryThreeCells.lean` |
| `87444c54` | visibility of `190d287c` restored for the four declarations widened only for dead code |
| `32343779` | `#print axioms` for the 34 moved theorems, at the end of the `Unused` file |
| receipt commit | this file, `Lib/reports/unused/cube3/`, the dated line in `Lib/reports/wave-2/cube3.md` |

## The dead set

`cube3/deadset.py` over the base dump (`dump_head.jsonl`, head `17ba7739`, same Lean sources as
`223b655d`): the 407 constants of the seven pieces are grouped under their 213 ranged declarations
(`X._proof_n`, `X.eq_n`, `X._simp_…` count as part of `X`, matched after removing the private
mangling, so that e.g. `_private.….square_indices_exhaust._proof_1_9` goes to the public
`square_indices_exhaust`; 0 orphans). Seeds: every ranged declaration used by a constant outside
the pieces; closure backwards inside the pieces. Result (`cube3/deadset.out`): live 177, dead 36 —
exactly the 36 of `Lib/reports/wave-2/cube3/notneed.txt`. `coordinateNonconstant` (a definition) is
dead: its users are `edge_nonconstant_coordinates`, `square_nonconstant_coordinates`,
`coordinate_variation_of_set_eq`, `edge_endpoints_distinct`, all dead.

Grep confirmation (`cube3/grepcheck.py`, output `cube3/grepcheck.out`): `grep -rnw <short name>`
over `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean` for each of the 36; every
hit lies inside the line range of one of the 36 dead declarations:
`names 36 hits outside dead ranges 0`.

After the move the same closure over the after-dump, with `Unused` not counted as a user, finds no
dead declaration left in the pieces: `after: ranged 177 live 177 dead (Unused not counted as user) []`.

## Moved, per source piece (in this order in the `Unused` file)

- `Lattice` (2): `card_lattice`, `mesh_two_of_one`
- `Cells` (20): `coordinateNonconstant`, `edge_coordinate_minima_attained`,
  `square_coordinate_minima_attained`, `edge_presentation_unique`, `edge_nonconstant_coordinates`,
  `square_presentation_unique`, `square_nonconstant_coordinates`, `coordinate_variation_of_set_eq`,
  `coordinate_constant_value_transport`, `increasing_pair_eq_of_direction_set_eq`,
  `edge_endpoints_distinct`, `square_remaining_index_cases`, `square_remaining_intrinsic`,
  `zero_mesh_images`, `zero_mesh_edge_nonunique`, `zero_mesh_square_nonunique`,
  `square_parameter_swap`, `swapped_ordered_pair_ne`, `square_order_suffices`,
  `shared_edge_presentation_identity`
- `Faces` (10): `face_sign_eq_of_mem`, `square_intrinsic_face`, `square_unit_mesh_endpoint_case`,
  `edge_saturated_coordinate_suffices`, `edge_no_other_saturated_forces_moving_neg_one`,
  `edgeMidpoint`, `edgeMidpoint_mem`, `edge_midpoint_all_abs_lt`, `all_abs_lt_not_boundary`,
  `edge_subset_boundary_iff`
- `Coverage` (3): `ambientOfThreeCoordinates_apply_i`, `_apply_j`, `_apply_k`
- `SquareBoundary` (1): `shifted_corner_commutes`

Total 36 (34 theorems, 2 definitions). One file suffices: the pieces are imported in dependency
order, blocks keep their source order within each piece, pieces in import order, each piece
introduced by a `/-! ### From … -/` heading. The file is a `module` in
`namespace TopologicalSpace.CubeBoundaryThree` with the pieces' header (`warningAsError`,
`autoImplicit false`, `open Set`). Imports: `public import` of `…Cells.Coverage` and
`…Cells.SquareBoundary`, `import all` of `Lattice`, `Cells`, `Faces`, `Coverage`, `SquareBoundary`.
`import all` gave every private helper the proofs need: the first build of the moved file was green
(`lake build Unused`, 2385 jobs), with no `Lib` visibility widened. Block boundaries are the dump's
declaration ranges (Lean ranges include docstring and attributes), extracted by `cube3/blocks.py`
(`cube3/blocks_base.json`) and moved by `cube3/move.py`.

`Unused.lean` is a plain (non-`module`) root file like `Lib.lean`: one import, then the module
docstring (Lean requires imports first).

## Visibility restores (`87444c54`)

Recomputed with the dump (`deadset.py`, last section): the declarations of the pieces whose only
users in other pieces are dead. Among the live ones only `square_zero_mem` (used outside `Cells`
only by `square_intrinsic_face`). The other three of W2 finding 2 are themselves dead and moved;
their widening of `099a566a` was for dead code too, so they also return to their `190d287c` form.

| declaration | where now | `099a566a` | now (= `190d287c`) |
|---|---|---|---|
| `square_zero_mem` | `Lib…/Cells.lean` | `public theorem` | `theorem` |
| `mesh_two_of_one` | `Unused` | `public theorem` | `theorem` |
| `coordinateNonconstant` | `Unused` | `@[expose] public def` | `def` |
| `square_nonconstant_coordinates` | `Unused` | `public theorem` | `theorem` |

`lake build Lib Unused` green after the change (9431 jobs): no live user needed any of them.
Not restored: none. The other 30 declarations widened by `099a566a` (10 of them also `@[expose]`) stay (each has a live
user in another piece; see "Left" 1).

## Verbatim and complement checks

`python3 Lib/reports/unused/cube3/verbatim_check.py 223b655d 32343779` (output `cube3/verbatim.out`):

```
visibility only: mesh_two_of_one | public theorem mesh_two_of_one {h : ℝ} (hh : h = 2 / ((1 : ℕ -> theorem mesh_two_of_one {h : ℝ} (hh : h = 2 / ((1 : ℕ) : ℝ))
visibility only: coordinateNonconstant | @[expose] public def coordinateNonconstant (C : Set Ambient) -> def coordinateNonconstant (C : Set Ambient) (r : Fin 3) : Pr
visibility only: square_nonconstant_coordinates | public theorem square_nonconstant_coordinates {h : ℝ} (hh :  -> theorem square_nonconstant_coordinates {h : ℝ} (hh : 0 < h) 
(1) blocks: 36 names, identical 33, visibility-only 3, other differences 0 []; dead names still in Lib pieces at tip: []
(2) complement: removed lines inside moved blocks 360 (block lines total 360), listed blank context lines 9, listed edits 1 ['public theorem square_zero_mem (h : ℝ) ('], unexplained 0 []
(3) raw blocks with docstrings found verbatim in the Unused file: 33, after removing visibility modifiers: 3 more
```

(1) parses the files independently of the move script: comments stripped, split into declaration
blocks, the 36 blocks at base (seven pieces) and tip (`Unused` file) compared. (2) line diff of each
piece base → tip: every removed line is in a moved block, or one of the 9 listed blank lines
(`cube3/ctx_removed.json`: runs of blank lines left by the removal collapsed to one — Faces 7,
Coverage 1, SquareBoundary 1); the only changed line is the `square_zero_mem` restore; nothing
added. (3) the raw blocks including docstrings and attributes. No section comment was removed.

## Probes

`Lib/AxiomAudit.lean` and `Hopf/Proof/AxiomAudit.lean` probe none of the 36 names. All 36 are
private to the `Unused` module after the restore, so they cannot be probed from another module; no
`Unused/AxiomAudit.lean` was created. The 34 theorems get one `#print axioms` each at the end of
`Unused/Topology/Dimension/CubeBoundaryThreeCells.lean` (the two definitions are not probed).

## Checks (at `32343779`, under nohup, `cube3/checks.out`)

```
lake build Lib -> exit 0: Build completed successfully (9428 jobs).
lake build Unused -> exit 0: Build completed successfully (2385 jobs).
lake build Solution S6Shortcuts S6 Challenge -> exit 0: Build completed successfully (9489 jobs).
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit -> exit 0: Build completed successfully (9431 jobs).
AxiomAudit: depends-on-axioms lists 3741 axioms ['Classical.choice', 'Quot.sound', 'propext'] no-axiom lines 13 sorryAx 0
lake build Unused (chain run at 32343779): depends-on-axioms lists 33 axioms ['Classical.choice', 'Quot.sound', 'propext'] no-axiom lines 1 sorryAx 0
stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
ratchet PASS: 123 <= baseline 1648
grep Lib imports Hopf/Unused: []
grep imports Unused: []
sorry/axiom/admit in Unused: []
```

The no-axiom `Unused` probe is `swapped_ordered_pair_ne`. The census scans `Hopf/` only, so it does
not count the new tree. Greps: `grep -rnE '^(public )?import (Hopf|Unused)' Lib/ --include=*.lean`
and `grep -rnE '^(public )?import Unused' Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean`,
both empty. No build warning in any `CubeBoundaryThreeCells` piece or in `Unused` (the warnings in
the `Lib` log are replayed, pre-existing ones of other modules).

## envdiff

`lake env lean-agent-ide dump Solution Lib Unused --modules Hopf,Lib,Unused` (39179 constants,
rename map 0 entries), then `envdiff.py dump_head.jsonl dump_after.jsonl` (`cube3/envdiff.txt`,
`cube3/envdiff.json`):

```
constants before 39175 after 39179 (keys 39073 39074 )
lost 2 added 6 of which source declarations: 0 0 ; names with changed type 1 of which source: 0
auxiliary lost/added/changed (not judged): 2 6 1
module moves (source declarations, 1-to-1):
      20  Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells -> Unused.Topology.Dimension.CubeBoundaryThreeCells
       3  Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage -> Unused.Topology.Dimension.CubeBoundaryThreeCells
      10  Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces -> Unused.Topology.Dimension.CubeBoundaryThreeCells
       2  Lib.Topology.Dimension.CubeBoundaryThreeCells.Lattice -> Unused.Topology.Dimension.CubeBoundaryThreeCells
       1  Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary -> Unused.Topology.Dimension.CubeBoundaryThreeCells
ambiguous module changes: 0
auxiliary constants that changed module: 7
VERDICT PASS
```

Moves = the 36 (2 + 20 + 10 + 3 + 1). envdiff compares names with the private mangling removed, so
the private constants (33 at base, 36 after) show as moves, not as lost + added: 0 such pairs to
reconcile. Independent reconciliation by demangled name and `typeHashPublic`
(`cube3/reconcile.py`, `cube3/reconcile.out`): `moved parents: 36, same demangled name +
typeHashPublic, now in Unused: 36`. The auxiliaries, name by name:

- `card_lattice._simp_1_2`, `_simp_1_3`, `square_remaining_index_cases._proof_1_1`: same hash, moved
  with their parent.
- `edge_endpoints_distinct._simp_1_2` (lost) / `._simp_1_1` (added): same hash `2525783790`,
  renumbered.
- `edgeMidpoint._proof_1` (added) and `edgeMidpoint.eq_1` (changed hash): at base the definition's
  body used `squareMidpoint._proof_1`, a proof abstracted by the earlier `squareMidpoint` in
  `Faces`; in `Unused` the same proof (hash `2547959801` in both) is abstracted under
  `edgeMidpoint`'s own name, and the equation lemma mentions it.
- `ambientOfThreeCoordinates.eq_1`, `shiftedVertexJ.eq_1`, `shiftedVertexK.eq_1` (added, in `Unused`
  beside the `Lib` copies): equation lemmas of private `Lib` definitions realized again in `Unused`
  by `simp [ambientOfThreeCoordinates]` and `simp only [shiftedVertexJ, shiftedVertexK]` in the moved
  proofs.

No source declaration was lost, added or changed type.

## Left

1. **The other widenings of `099a566a`**: 30 declarations (10 of them `@[expose]`) stay; each has a live user
   in another piece (dump), but whether each `@[expose]` is individually needed was not tested
   (needs one build per removal). Reproduce:
   `grep -nE '^@\[expose\] public' Lib/Topology/Dimension/CubeBoundaryThreeCells/*.lean`.
2. **Other dead code in `Lib`**: only the cube3 pieces were examined; the same closure over the whole
   `Lib` is not done. Reproduce for one module family: `python3 Lib/reports/unused/cube3/deadset.py <dump>`
   with `P`/`PIECES` changed.
3. **`Unused` in the check chain**: `lake build Unused` is not a default target, so it runs only where
   the chain names it. Reproduce: `grep -n defaultTargets lakefile.toml`.
4. **Items 2–7 of `Lib/reports/wave-2/cube3.md` "Left"** are unchanged by this move. Reproduce:
   `sed -n '/^## Left/,/^## Files/p' Lib/reports/wave-2/cube3.md`.

## Files in `Lib/reports/unused/cube3/`

`deadset.py` + `deadset.out` (dead set), `grepcheck.py` + `grepcheck.out`, `blocks.py` +
`blocks_base.json` (block extraction), `move.py` + `ctx_removed.json` (the move), `verbatim_check.py`
+ `verbatim.out`, `reconcile.py` + `reconcile.out`, `envdiff.json`, `envdiff.txt`, `checks.out`,
`unused_axioms.out`. Scripts read the scratch dumps under `/home/goblin/.claude/jobs/06995e68/tmp/`
(`head3/dump_head.jsonl`, `unused/dump_after.jsonl`); `move.py` read its header from
`unused/unused_header.lean` in the scratch directory (the header is the top of the `Unused` file).
