# Wave 1 receipt — `Lib/Geometry/Manifold/Morse/Connection.lean`

Branch `wave1/connection` (worktree `/home/goblin/hopf-w1-connection`), base `lib/integration` at
`e669bc93`. Judgement: `Lib/reports/round-7/judgement/monoliths.md`, entry "Connection.lean
(231 declarations, 8180 lines)", verdict C. Twin: Milnor, *Lectures on the h-cobordism theorem*,
Theorem 5.4 (first cancellation theorem) and its proof in §5; the flow-box pieces cf. Lee,
*Introduction to Smooth Manifolds*, Theorem 9.22.

## The cut

`Connection.lean` (8169 lines, 231 declarations = 266 ranged constants with the fields and
constructors of its two structures) was cut into 18 modules
`Lib/Geometry/Manifold/Morse/Connection/<Topic>.lean`, each with a module docstring stating the
mathematics and the textbook reference. `Connection.lean` stays as a facade (module docstring
listing the pieces, `import` of the 18 pieces, nothing else); `Lib.lean` and the 38 consumers are
unchanged.

Tool: `lean-agent-ide tools/split_module.py`, applied once per piece to the original source with
`--stay` = every ranged constant not in the piece (the move file is the piece, the keep file is
discarded); dump = a module-only dump of the base (`dump Lib.Geometry.Manifold.Morse.Connection`,
same source and build as `dump_head.jsonl`). Receipts: `connection/split_<Piece>.json` (per unit:
names, lines in the source, SHA-256 of the text written). Post-processing of each piece, by
script: the original module docstring replaced by the piece's; section headers (`/-! ### … -/`)
covering no declaration of the piece dropped; the `section … end` of source l.1331–1550 carrying
`attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2` kept only in the two pieces
with declarations inside it (`NoReturn`, `TimeChange`); one header renamed
(`SignEnumerations`: "Split coordinates" for the two `splitCoordinates_*_zero_iff` lemmas that
came from the "Transported corrections" section). Verbatimness: for every moved unit the text of
its source lines (SHA-256 as in the receipt) occurs verbatim in the piece file, and each of the
266 constants was placed exactly once (`do_split.py`, assertions).

| piece | lines moved | declarations | textbook topic |
|---|---|---|---|
| `Connection/CubicEndpoints.lean` | 277 | 8 | endpoint slices and clocks of the cubic model (Milnor h-cobordism §5, proof of Thm 5.4) |
| `Connection/MinimumBasins.lean` | 290 | 9 | density of the forward basins of the minima, belt branches (Baire; Milnor §4) |
| `Connection/NoReturn.lean` | 345 | 9 | no-return neighbourhoods of an isolated connecting orbit (Milnor §5) |
| `Connection/BeltArc.lean` | 299 | 16 | belt arcs and meridians of a handle (Milnor §3, §5) |
| `Connection/TimeChange.lean` | 471 | 16 | time changes and band normalisation of a descent flow (Milnor §3) |
| `Connection/Suspension.lean` | 447 | 22 | suspended flow of a level diffeomorphism, level flow cylinders (Milnor §4) |
| `Connection/LevelHolonomy.lean` | 662 | 20 | realising an isotopy of a regular level by the flow (Milnor §4–§5) |
| `Connection/TransverseTimeLifts.lean` | 200 | 8 | transversality of flow sheets through transverse level maps (Milnor §5) |
| `Connection/PhaseCylinder.lean` | 643 | 17 | flow-box charts of a connecting orbit with a phase (Lee ISM Thm 9.22) |
| `Connection/TransitionPhase.lean` | 291 | 6 | transition maps between flow-box charts (Lee ISM Thm 9.22) |
| `Connection/TransportedCorrections.lean` | 220 | 5 | transport of supported isotopies through transverse charts (Milnor §5) |
| `Connection/SignEnumerations.lean` | 125 | 8 | sign vectors, coordinate enumerations, split coordinates (Milnor, Morse Theory §2) |
| `Connection/EndpointBasins.lean` | 497 | 10 | stable/unstable planes at the cubic endpoints, `NativeEndpointSliceData` (Milnor §5) |
| `Connection/TransverseBlocks.lean` | 674 | 14 | linearising a transverse germ by supported isotopies (Milnor §5) |
| `Connection/CylinderHolonomy.lean` | 515 | 10 | holonomy corrections of a flow cylinder (Milnor §4–§5) |
| `Connection/PhaseFlow.lean` | 803 | 18 | phase clocks and the phase-corrected cylinder (Milnor §5) |
| `Connection/FieldChartGluing.lean` | 313 | 13 | gluing flow-box charts along an axis (Lee ISM Thm 9.22; Milnor §5) |
| `Connection/CubicFieldChart.lean` | 759 | 22 | the cubic field chart along a unique connecting orbit (Milnor Thm 5.4) |
| **total** | **7831** | **231** | |

("lines moved" = lines of the declaration units incl. docstrings and `… in` prefixes; the other
338 lines of the source are header, section headers, `open`s and blank lines.)

Piece imports (exact `uses` graph of the dump, acyclic): every piece imports `Mathlib` and
`Lib.Geometry.Manifold.Morse.Rearrangement` (the original list; both are used directly — the
vocabulary `cubicFlowCylinder`, `AdaptedWindows`, `nativeCubicDescent`, … comes through
`Rearrangement`) plus the sibling pieces it uses:
`BeltArc ← MinimumBasins`; `TimeChange ← NoReturn`; `LevelHolonomy ← Suspension, TimeChange`;
`TransverseTimeLifts ← Suspension`; `PhaseCylinder ← LevelHolonomy, TimeChange`;
`TransitionPhase ← PhaseCylinder`; `EndpointBasins ← CubicEndpoints, SignEnumerations,
TransitionPhase, TransportedCorrections`; `TransverseBlocks ← TimeChange, TransportedCorrections,
TransverseTimeLifts`; `CylinderHolonomy ← CubicEndpoints, Suspension, TransverseBlocks,
TransverseTimeLifts`; `PhaseFlow ← CylinderHolonomy, PhaseCylinder, Suspension, TimeChange,
TransverseBlocks, TransverseTimeLifts`; `CubicFieldChart ← CubicEndpoints, FieldChartGluing,
PhaseCylinder, SignEnumerations, TransverseTimeLifts`; the other six import no sibling. No
further import trimming was attempted (`import Mathlib` is the project-wide convention).

Placement differing from file order (all by the `uses` graph): `FlowSuspension.exists_native_vertical_field_replacement`
and `mvfderiv_native_height_field` (source l.62, 106) went to `CylinderHolonomy` (their only
user, `exists_full_cylinder_holonomy`); `TransverseGerms.splitCoordinates_negative_zero_iff`,
`splitCoordinates_positive_zero_iff` (l.4490, 4503) to `SignEnumerations`;
`MorseCancellation.NativeEndpointSliceData` (l.1277) to `EndpointBasins` with its constructors;
the FlowTimeChange "Normalized level cylinders" section (l.2404–2538) to `LevelHolonomy`
(it uses `Suspension` and is used by the holonomy realisation, so it cannot sit in either
neighbour); the "Cylinder basin labels" section (l.8034–8112) to `CylinderHolonomy`.

## `Hopf/Proof` moves and the closure argument

None. Closure over `dump_head.jsonl` (`connection/closure.json`, script `closure.py`: `uses`
restricted to `Lib` modules, auxiliaries attributed to their parent declaration, structure
fields to their structure): 68 constants of the module are used directly by another `Lib`
module (`connection/closure_users.json`; `Morse/Cancellation.lean` alone uses 57 of them,
including `exists_full_cubic_chart_from_corrected_cylinder`, `exists_unique_phase_corrected_cylinder`,
`exists_normalized_connection_cylinder`; further users `AdaptedWindows`, `BeltCancellation`,
`CircleGluing`, `SurgeryCollapse`, `RearrangementTheorem`, `Whitney/EmbeddedArcs`), and the
backward closure inside the module contains 258 of the 266 ranged constants = 224 of the 231
declarations. The 7 unreachable declarations are all in `BeltArc`:
`MorseCancellation.nativeLowerMeridian_coordinates_mem_target`, `nativeLowerMeridian_height`,
`nativeLowerMeridianFamily`, `nativeLowerMeridian`, `nativeLowerMeridian_zero`,
`nativeUpperMeridian_flow`, `nativeLowerMeridian_homotopic_attaching` (two of them used by
`Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean`). They were NOT moved: the file
contains no project material in the sense of the rules — `grep -n -i 'mo1973\|Sphere 2\|Hemisphere\|= 6\b\|index 2\|index 3\|receipt' Lib/Geometry/Manifold/Morse/Connection.lean`
(at the base) is empty, every statement is over `{E M : Type*}` with an arbitrary `m : ℕ`, and
the seven are general constructions on `AdaptedWindows E f` (the attaching sphere pushed
through a handle by the flow). Listed under "Left" for a later decision.

## Renames

None. `grep -rn 'mo1973' Lib/Geometry/Manifold/Morse/Connection*` is empty; `rename.txt` is
empty. The `native*` vocabulary (94 declaration names, 403 occurrences in the source) was left
(rule 5: consumer edit not small — 38 consumers); see "Left".

## Universe lifts

None: no `{E M : Type}`, `.{0}` or `universe` in the file (`grep -n 'Type}\|\.{0}\|^universe'`
empty on the pieces); everything is already `Type*`.

## Docstrings

231/231 non-private declarations carry a docstring (computed by a script over the 18 pieces:
231 declaration heads, 0 private, 0 without a preceding `/-- … -/`); none had to be written.
Each piece has a new module docstring (`/-! # … -/`); the facade's docstring lists the pieces.

## Checks (all green; lake v4.33.0 has no `-j` option — "error: unknown short option '-j'" — so every build ran plain, pinned to three cores with `taskset -c 3,4,5`)

```
$ lake build Lib.Geometry.Manifold.Morse.Connection
✔ [8761/8761] Built Lib.Geometry.Manifold.Morse.Connection (7.3s)
Build completed successfully (8761 jobs).
$ lake build Lib
✔ [9163/9164] Built Lib (4.0s)
Build completed successfully (9164 jobs).
$ lake build Solution S6Shortcuts S6 Challenge
ℹ [9215/9216] Built Solution (4.3s)
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9216 jobs).
$ lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9166 jobs).
   (3302 `depends on axioms` lines, every set ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx)
$ python3 scripts/lib_stock_census.py --check
stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
ratchet PASS: 123 <= baseline 1648
$ grep -rn '^import Hopf' Lib/ --include=*.lean | wc -l
0
```

## envdiff

`dump_after.jsonl` = `lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` at the tip
(38249 constants; no rename map, nothing renamed); `envdiff.py dump_head.jsonl dump_after.jsonl`
(`connection/envdiff.txt`, `connection/envdiff.json`):

```
constants before 38248 after 38249 (keys 38146 38147 )
lost 1 added 2 of which source declarations: 0 0 ; names with changed type 1 of which source: 0
auxiliary lost/added/changed (not judged): 1 2 1
module moves (source declarations, 1-to-1): 266, all Lib.Geometry.Manifold.Morse.Connection -> Connection.<Piece>
ambiguous module changes: 0
auxiliary constants that changed module: 98
VERDICT PASS
```

Moves = the plan: BeltArc 16, CubicEndpoints 8, CubicFieldChart 22, CylinderHolonomy 10,
EndpointBasins 37 (10 declarations + the 27 fields and constructor of `NativeEndpointSliceData`),
FieldChartGluing 13, LevelHolonomy 20, MinimumBasins 9, NoReturn 9, PhaseCylinder 17, PhaseFlow 26
(18 + the 8 fields and constructor of `PhaseFlowCoordinates`), SignEnumerations 8, Suspension 22,
TimeChange 16, TransitionPhase 6, TransportedCorrections 5, TransverseBlocks 14,
TransverseTimeLifts 8 — the 231 declarations and 35 structure constants of the cut table.
Not "moves only", reconciled name by name: the one lost / two added / one changed-type key is
the single auxiliary `TransverseGerms.transverseBlockMap._proof_1` — in the source this
abstracted proof was shared with (and named after) an earlier declaration of the module; in
`TransverseBlocks.lean` the definition realises its two abstracted proofs itself as `_proof_1`,
`_proof_2` (the old `_proof_1` hash reappears as `_proof_2`). No source declaration lost, added
or changed.

## Left

* `native*` / `Native*` vocabulary not renamed (94 declaration names in the pieces, e.g.
  `FlowSuspension.nativeSuspensionFlow`, `FlowCancellation.native_no_return_of_supported_perturbation`,
  `MorseCancellation.NativeEndpointSliceData`; 38 consumers):
  `grep -hoE '^(theorem|def|structure|abbrev) [A-Za-z_.]*[nN]ative[A-Za-z_]*' Lib/Geometry/Manifold/Morse/Connection/*.lean | wc -l` → 94.
* Seven `BeltArc` declarations unreachable from `Lib` (see the closure argument), two of them
  used by `Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean`; kept in `Lib` as general
  handle geometry — a move to `Hopf/Proof/Geometry/Manifold/Morse/Connection/BeltArc.lean` is
  possible if the owner classes them as project material:
  `python3 -c "import json;print(json.load(open('Lib/reports/wave-1/connection/closure.json'))['free'])"`.
* Misfiled general lemmas kept beside their users (candidates for an upstream home):
  `MorseCancellation.compact_partial_chart_image_nowhereDense`, `interior_zero_product_empty`
  (`Connection/MinimumBasins.lean`; general topology), the `SignedCoordinates.*` /
  `exists_coordinate_enum` combinatorics (`Connection/SignEnumerations.lean`; `Fintype`/`Fin`),
  `TransverseCoordinates.surjective_coprod_swap` (`Connection/TimeChange.lean`; linear algebra):
  `grep -n 'compact_partial_chart_image_nowhereDense\|interior_zero_product_empty\|surjective_coprod_swap' Lib/Geometry/Manifold/Morse/Connection/*.lean`.
* Duplicate: `SignedCoordinates.negative_card_split` (`Connection/SignEnumerations.lean`) and
  `MorseCancellation.negative_card_split` (`Morse/Birth.lean`), named by the auditors; both kept:
  `grep -rn 'negative_card_split' Lib/Geometry/Manifold/Morse/Birth.lean Lib/Geometry/Manifold/Morse/Connection/SignEnumerations.lean`.
* Auditor suggestion `Flow/TimeChange.lean`, `Flow/Suspension.lean`, `Flow/FieldChartGluing.lean`:
  the pieces were placed under `Morse/Connection/` (rule 1 default; the time-change and
  suspension lemmas are stated for Morse descent fields with `ManifoldMorse.criticalPoints`,
  `RegularLevel`), a relocation to `Lib/Geometry/Manifold/Flow/` is a facade-dissolving step.
* Facade `Connection.lean` still to be dissolved (later step): consumers keep importing it.
