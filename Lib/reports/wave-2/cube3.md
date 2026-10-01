# Wave 2 receipt: `cube3` (`Lib/Topology/Dimension/CubeBoundaryThreeCells.lean`)

Agent: Claude Opus 5.5 (model ID `claude-opus-5-5`), the second agent on this assignment (the first
was stopped before any commit; its uncommitted module-system experiments `ZTest{A,B,C,D}.lean` were
deleted, nothing of it is used). Start 2026-10-01 19:59 CEST, end 2026-10-01 20:28 CEST.
Base `lib/integration` at `3760f829`; branch `wave2/cube3`; commits `190d287c` … the receipt commit.
Judgement entry: verdict C ("dimension-3 cell bookkeeping with proof-ledger labels"). Twin: the
cell structure of the subdivided cube boundary (Engelking, *Dimension Theory*, §1.8;
Hurewicz–Wallman, *Dimension Theory*, Ch. IV); no Mathlib twin.

At the base the proof-ledger labels the auditors quoted (`L0–L4`, `CD10C-I`, "canonical lines …")
were already gone: `grep -nE 'canonical|Textbook|ledger|CD[0-9]|\b[LDCHFEI][0-9]{1,2}\b'` over the
file at `3760f829` finds nothing. What remained were 94 *plain* `/- … -/` comments over the
declarations of the first half, so 12 of the 19 public declarations had no docstring.

## Commits

| commit | step |
|---|---|
| `190d287c` | 94 plain declaration comments (lines 31–778) become `/-- … -/` docstrings, text unchanged |
| `099a566a` | visibility: 25 declarations `public`, 11 definitions `@[expose] public` (see below) |
| `344b7b6c` | split into seven pieces + facade (tool, seven runs) |
| `9e1e83b5` | 19 docstrings rewritten from their statements (comment-only) |
| `03b0049c` | import trim: `Lattice` no longer imports the cube |
| receipt commit | this file and `Lib/reports/wave-2/cube3/` |

## The cut

Seven pieces under `Lib/Topology/Dimension/CubeBoundaryThreeCells/`; the original module is a facade
(module docstring naming the pieces + seven `public import`s, nothing else). Consumers
(`CubeBoundaryThreeBricks`, `Lib/AxiomAudit.lean`, `Lib.lean`) unchanged.

| piece | lines moved | declarations (public) | textbook topic |
|---|---|---|---|
| `Lattice` | 233 | 30 (13) | uniform mesh `-1 + k h`, `h = 2/N`, of `[-1,1]`: bounds, endpoints, `N+1` points, separation `≥ h`, successor; mesh interval `[a, a+h]` of a point via the clipped floor index |
| `Cells` | 506 | 73 (29) | vertices, edges, squares of the subdivided `∂[-1,1]³`; lower corner and uniqueness of presentations; `squareRelInterior`, `edgeEndpoints`; finiteness; endpoints are vertices |
| `Faces` | 411 | 32 (5) | the face `x i = ±1` containing a square; boundary containment ⇔ saturated fixed coordinate; closed/open squares as coordinate rectangles; `square_coordinate_description` |
| `Coverage` | 164 | 20 (1) | every boundary point lies in a square (`exists_square_mem`) |
| `RelInterior` | 80 | 6 (1) | relative interiors of distinct squares are disjoint |
| `SquareBoundary` | 307 | 26 (1) | boundary of a square = union of its four edges, all mesh edges |
| `Separation` | 482 | 26 (3) | vertex separation, edges through a common endpoint, edges without one are `≥ h` apart |

Total 2183 source lines in 213 units (one ranged declaration each), each moved exactly once.
Import graph: `Lattice` ← `Cells` (+ `CubeBoundaryThree`) ← `Faces` ← `Coverage`, `RelInterior`,
`Separation`; `Cells` ← `SquareBoundary`.

### How the tool was run

1. `190d287c` first: `split_module.py` extends a unit upward over `/-- … -/` docstrings but stops at a
   plain block comment, so the 94 plain comments would have become context copied into all pieces.
   Converting them in place keeps every line number, so `dump_head.jsonl` still anchors the tool.
2. Seven runs (`cube3/run_split.sh`) on the visibility-patched source (`099a566a`, again same line
   numbers), one piece moved per run, the keep file discarded: `cube3/split-<Piece>.receipt.json`.
   Partition by line ranges of the source: `cube3/partition.py` (→ `piece_of.json`). Check
   (`cube3/verbatim_check.py`): for each of the 213 moved units, the source lines it names occur
   verbatim in its piece as committed in `344b7b6c` — `moved units verbatim in pieces: 213 names 213`.
3. Context edits per piece (`cube3/assemble.py`, `cube3/docs.py`): new header (`module`, imports,
   piece docstring, the two `set_option`s, `open Set`, `namespace`); dropped: the stray plain comment
   "Coordinate evaluation/extensionality, set transport, real order/cancellation, …" (a list of
   proof techniques, not attached to a declaration), the empty `end`/`namespace` pair between the
   two halves, and the section comment "Enclosure of a boundary point by a cell", which described a
   "point of a mesh edge within half a mesh of an endpoint" lemma that is not in the file.

### Visibility (`099a566a`)

The file is a Lean `module`: a declaration without `public` is private to it. A piece can only use
the public declarations of another piece, and only unfold definitions marked `@[expose]`. Every
declaration used across pieces (dump `uses`, `cube3/partition.py`) was made `public`; definitions
whose bodies later pieces unfold (anonymous constructors and projections on `SquareParam`, `.1` on
`v ∈ vertices N h`, `rw [edgeGeom]`, …) got `@[expose]`. A trial without any `@[expose]`
(`cube3/b3.log`) failed in `Faces` and `SquareBoundary` on exactly these, so they are needed;
`latticeLowerEndpoint` is `public` but not exposed (exposing it would force exposing the floor
helpers below it, and no piece unfolds it).

- `public` (25): `mesh_identities`, `mesh_pos`, `lattice_subset_interval`, `finite_lattice`,
  `lattice_endpoints`, `lattice_separation`, `lattice_successor`, `mesh_two_of_one`, `edge_mem_iff`,
  `edge_coordinate_formula`, `edge_parameter_extract`, `square_coordinate_formula`, `square_zero_mem`,
  `square_parameter_extract`, `square_nonconstant_coordinates`, `square_remaining_index`,
  `square_remaining_coordinate`, `square_relInterior_coherent`, `square_subset_boundary_iff`,
  `Ambient_ext_of_three`, `square_indices_exhaust`, `square_closed_coordinate_rectangle`,
  `latticeLowerEndpoint`, `latticeLowerEndpoint_data`, `clipped_floor_enclosure`.
- `@[expose] public` (11; `vertices`, `squares` were public already): `lattice`, `latticeBelowTop`,
  `VertexParam`, `vertices`, `edgeGeom`, `EdgeParam`, `squareGeom`, `squareOpenGeom`, `SquareParam`,
  `squares`, `coordinateNonconstant`.

Names are unchanged; `envdiff` compares names with the private mangling removed, so the change is
invisible to it (see below). Public declarations: 19 before, 53 after.

## `Hopf/Proof` moves: none

Consumers: `grep -rnE '^(public )?import Lib.Topology.Dimension.CubeBoundaryThreeCells$'` finds
`Lib.lean`, `Lib/AxiomAudit.lean` and `Lib/Topology/Dimension/CubeBoundaryThreeBricks.lean`; no `Hopf`
file, no root. Closure over `dump_head.jsonl` (`cube3/closure.py`): of the 406 constants of the module,
353 are reached backwards from a constant of another `Lib` module (`CubeBoundaryThreeBricks` and
`CubeBoundaryThreeDimension`, through the 19 public declarations); no `Hopf` or `Solution` constant
uses any of them. The 36 unreached ranged declarations (list in "Left") are all module-private
lemmas that nothing uses at all. They were not moved, because their proofs use module-private
helpers that `Lib` needs (`EdgeParam`, `edgeEndpointsRaw`, `square_directions_mem_of_set_eq`,
`clippedFloorIndex`, … — 38 of them at the base): a `Hopf/Proof` file could reach those only if they
were made public `Lib` API for the sake of dead code, or through `import all`, which a non-`module`
`Hopf` file cannot write and which `Lib/reviews/INTEGRATION-3.md` rules out for new code. Nothing
of the module is project material in the sense of rule 3: no dimension-6 hypothesis, no
`Hemisphere.Sphere 2`, no `mo1973`, no W4W1 index machinery. `Lib/AxiomAudit.lean` probes (the 19
original public names) stay.

## Renames

None (`cube3/rename.txt` is empty). `Ambient_ext_of_three` (capital `A`) is now public; see "Left".

## Universe lifts

None: the file has no `Type` binders (everything lives in `Ambient = EuclideanSpace ℝ (Fin 3)`).

## Docstrings

Computed (`grep -c '^/--'` over the seven pieces, and a script that checks the line above every
`public` declaration head): 213 declarations, 213 docstrings; 53 public declarations, 0 without a
docstring (before: 19 public, 12 of them with only a plain comment). 94 docstrings came from the
plain comments (`190d287c`); 19 that described the proof or the construction rather than the
statement were rewritten from binders and conclusion (`9e1e83b5`): `mesh_pos`, `lattice_endpoints`,
`latticeLowerEndpoint`, `clipped_floor_enclosure`, `vertices`, `vertex_mem_boundary`,
`squareRelInterior`, `square_relInterior_coherent`, `square_presentation`, `edgeEndpoints`,
`edge_presentation`, `finite_vertices`, `finite_edges`, `finite_squares`,
`edge_endpoints_vertices`, `square_subset_boundary_iff`, `exists_square_mem`,
`square_eq_of_relInterior_inter_nonempty`, `square_boundary_edges`. Seven new piece docstrings and
the rewritten facade docstring state the mathematics.

## Imports

`Lattice`: `Mathlib.Data.Int.Interval`, `Mathlib.Algebra.Order.Archimedean.Real.Basic`,
`Mathlib.Data.Set.Card` (the mesh of `[-1,1]` does not need the cube). `Cells`:
`Lib.Topology.Dimension.CubeBoundaryThree` + `Lattice` (`Mathlib.Analysis.Convex.Segment` comes with
the cube). Other pieces: only the pieces they use. No `maxSynthPendingDepth`, no kitchen-sink `open`,
no `universe`.

## Checks (all at `03b0049c`, under nohup, logs in the scratch directory)

```
lake build Lib.Topology.Dimension.CubeBoundaryThreeCells{,.Lattice,.Cells,.Faces,.Coverage,.RelInterior,.SquareBoundary,.Separation}
Build completed successfully (2385 jobs).
lake build Lib
Build completed successfully (9285 jobs).
lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9344 jobs).
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9287 jobs).
```

No warning in any piece. Axiom audit: 3302 `depends on axioms` lists parsed, every axiom in
{propext, Classical.choice, Quot.sound}; 0 `sorryAx`. `python3 scripts/lib_stock_census.py --check`:
`stock declarations under Hopf/: 123` … `ratchet PASS: 123 <= baseline 1648`.
`grep -rn '^import Hopf' Lib/ --include=*.lean`: empty (the 9 hits of the unrestricted grep are
pre-existing `.md`/`.txt` logs under `Lib/docs/`).

## envdiff

`dump Solution Lib --modules Hopf,Lib` at `03b0049c` (38302 constants, rename map 0 entries), then
`envdiff.py dump_head.jsonl dump_after.jsonl` (`cube3/envdiff.txt`, `cube3/envdiff.json`):

```
constants before 38301 after 38302 (keys 38199 38200 )
lost 3 added 4 of which source declarations: 0 0 ; names with changed type 3 of which source: 0
auxiliary lost/added/changed (not judged): 3 4 3
module moves (source declarations, 1-to-1): 73 Cells, 20 Coverage, 32 Faces, 30 Lattice,
  6 RelInterior, 26 Separation, 26 SquareBoundary
ambiguous module changes: 0
VERDICT PASS
```

Moves = the plan (213 = 30 + 73 + 32 + 20 + 6 + 26 + 26). The auxiliaries, name by name:
`lattice.eq_1` (changed hash; `lattice` is now an exposed public definition, its equation lemma is
realized in `Lattice`), `ambientOfThreeCoordinates.eq_1` (changed hash) and the new
`ambientOfThreeCoordinates._proof_1` (the `if r = i …` decidability proof abstracted under the
definition's own name in `Coverage` instead of being shared in the old module),
`latticeLowerEndpoint_data._proof_1_1` (changed hash, proof renumbering). No source declaration
changed type, was lost or added.

## Left

1. **36 unused private lemmas** (no constant of `Lib`, `Hopf` or `Solution` uses them; deletion
   candidates, not deleted in this wave). Reproduce: `python3 Lib/reports/wave-2/cube3/closure.py`
   (reads the base `dump_head.jsonl`; prints `ours 406 need 353`; the list is `cube3/notneed.txt`). By piece —
   `Lattice`: `card_lattice`, `mesh_two_of_one`; `Cells`: `coordinateNonconstant`,
   `coordinate_constant_value_transport`, `coordinate_variation_of_set_eq`,
   `edge_coordinate_minima_attained`, `edge_endpoints_distinct`, `edge_nonconstant_coordinates`,
   `edge_presentation_unique`, `increasing_pair_eq_of_direction_set_eq`,
   `shared_edge_presentation_identity`, `square_coordinate_minima_attained`,
   `square_nonconstant_coordinates`, `square_order_suffices`, `square_parameter_swap`,
   `square_presentation_unique`, `square_remaining_index_cases`, `square_remaining_intrinsic`,
   `swapped_ordered_pair_ne`, `zero_mesh_edge_nonunique`, `zero_mesh_images`,
   `zero_mesh_square_nonunique`; `Faces`: `all_abs_lt_not_boundary`, `edgeMidpoint`,
   `edgeMidpoint_mem`, `edge_midpoint_all_abs_lt`, `edge_no_other_saturated_forces_moving_neg_one`,
   `edge_saturated_coordinate_suffices`, `edge_subset_boundary_iff`, `face_sign_eq_of_mem`,
   `square_intrinsic_face`, `square_unit_mesh_endpoint_case`; `Coverage`:
   `ambientOfThreeCoordinates_apply_{i,j,k}`; `SquareBoundary`: `shifted_corner_commutes`.
   Four declarations, with five modifiers (`mesh_two_of_one`, `coordinateNonconstant`, which got
   both `public` and `@[expose]`, `square_nonconstant_coordinates`, `square_zero_mem`), are now
   public only because dead lemmas in a later piece use them (`mesh_two_of_one` through
   `square_unit_mesh_endpoint_case`, the other three through `square_intrinsic_face`); deleting the dead lemmas would let them go private again
   (corrected 2026-10-02: this said "Three of them (`mesh_two_of_one`, `coordinateNonconstant`,
   `square_nonconstant_coordinates`) are now public only because dead lemmas in a later piece use
   them"; the review `Lib/reports/wave-reviews/W2.md` finding 2 found the fourth, `square_zero_mem`,
   whose only uses outside `Cells` are `Faces.lean:129` and `:144`, inside the dead
   `square_intrinsic_face`).
   (2026-10-02: the 36 moved to `Unused/…`, see `Lib/reports/unused/cube3.md`)
2. **Floor lemmas** (auditors: belong in `Algebra/Order/Floor`): `floor_real_bounds` is
   `⟨Int.floor_le u, Int.lt_floor_add_one u⟩` (twins `Int.floor_le`, `Int.lt_floor_add_one`);
   `cast_int_nat_sub_one`, `int_nat_sub_one_nonneg`, `int_floor_top_split` are `push_cast`/`omega`
   one-liners. All private to `Lattice`; nothing to extract. `grep -n 'floor' Lib/Topology/Dimension/CubeBoundaryThreeCells/Lattice.lean`.
3. **Raw/public definition pairs**: `squareRelInterior := squareRelInteriorRaw`,
   `edgeEndpoints := edgeEndpointsRaw` (private `Raw` versions wrapped by a public alias).
   `grep -n 'Raw' Lib/Topology/Dimension/CubeBoundaryThreeCells/Cells.lean`.
4. **Names**: `Ambient_ext_of_three` (capital `A`, now public) would be `ambient_ext_of_three`;
   `mesh_identities`, `mesh_pos` are generic names in the project namespace
   `TopologicalSpace.CubeBoundaryThree`. Not renamed (a rename of a newly public helper is cheap but
   was not needed for the split). `grep -n 'Ambient_ext_of_three' -r Lib/Topology/Dimension/`.
5. **Dimension 3 only**: everything is stated for `Fin 3` with `fin_cases` case splits; a library
   version would be a cubical-complex structure on `∂[-1,1]ⁿ` (judgement suggestion), not attempted.
   `grep -c 'fin_cases' Lib/Topology/Dimension/CubeBoundaryThreeCells/*.lean`.
6. **Style of the first half**: `Lattice`, `Cells` and the top of `Faces` (former lines 31–778) have
   no blank line between declarations and two-space continuation indentation; moved verbatim.
   `grep -c '^$' Lib/Topology/Dimension/CubeBoundaryThreeCells/Cells.lean`.
7. **Axiom probes** of the 34 newly public declarations are not added to `Lib/AxiomAudit.lean`
   (they are covered by the 19 existing probes, whose proofs use them).
   `grep -c 'CubeBoundaryThree\.' Lib/AxiomAudit.lean`.

## Files in `Lib/reports/wave-2/cube3/`

`split-<Piece>.receipt.json` (7), `envdiff.json`, `envdiff.txt`, `rename.txt` (empty),
`closure.py`, `verbatim_check.py`, `notneed.txt` (the 36 + their auxiliaries), `partition.py`, `piece_of.json`,
`pub.txt`, `expose.txt`, `vis.py`, `run_split.sh`, `assemble.py`, `docs.py`, `PROGRESS.md`.
