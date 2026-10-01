# Integration review 7 — the `Lib` work of `center-solution` since integration 6 (2026-10-02)

Source `center-solution` pinned at `8ea19482`; range `bcf711d6..8ea19482` restricted to `Lib` and `Lib.lean`:
51 commits, one author, all `Lib`-only. Replayed per commit on `int7/replay` (base `8ff8d81e`) by one Opus 5.5
seat, receipt `Lib/reports/integration-7/REPLAY.md` with `replay.log`; merged `--no-ff` at `6572e509`.

| method | commits |
|---|---|
| clean `git cherry-pick -x` | 46 |
| cherry-pick + append rule for `Lib/AxiomAudit.lean` | 3 |
| rerouted (the target file is a facade since wave 2) | 2 |
| adaptation commits / real collisions | 0 / 0 |

Reroutes: `RiemannBoundary.principalRoot_three_reverse_of_wedge` → `Lib/Analysis/Complex/RiemannMapping/
PrincipalRoot.lean` (its dependencies are there); `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge`
→ `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` (it uses `rotatedPrincipalRootFour`,
`quarticRootRotation`, moved there by wave 2), probe in `Hopf/Proof/AxiomAudit.lean`. Both statement blocks are
byte-identical to the source. The merge `12f41cf0` in the range has no `Lib` diff of its own.

Content: nine new modules (`Geometry/Hyperbolic/Models` 7,870 lines, `Geometry/Hyperbolic/GeodesicEquations`,
`Geometry/Manifold/Riemannian/CurveTransport` 1,957, `Geometry/Manifold/VectorBundle/Riemannian`,
`Order/Fin/Refinement`, `Analysis/Calculus/CurveVariation`, `Analysis/InnerProductSpace/FiniteDimensional`,
`LinearAlgebra/BilinearForm/Reflection`, `Topology/Compactification/BoundaryLimits`), additions to
`Algebra/Group/Prod` and `Analysis/Complex/Mobius`; 456 declarations (+ 7 `local notation` parser constants);
437 probes. All nine new files are byte-identical to the source at `8ea19482`.

## Checks on the merged head `17ba7739` (waves + integration 7 + `fix/waves`; one Opus 5.5 seat, read-only)

| check | result |
|---|---|
| `lake build Lib` | green, 9,428 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,489 jobs; `mathoverflow_1973` on `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` | green; 3,736 + 5 probes (+ 13 axiom-free), only the three standard axioms, `sorryAx` 0 |
| `scripts/lib_stock_census.py --check` | 123, ratchet PASS |
| `grep -rnE '^(public )?import Hopf' Lib/ --include=*.lean` | empty |
| `Lib.lean` closure | every `Lib` module is reached |
| environment diff against the wave-2 head (`envdiff-merged-17ba7739.{json,txt}` beside the replay receipt) | 38,373 → 39,175 constants; 0 lost source; 463 added source = the 456 declarations of the range + 7 notation constants (`Hyperbolic.termV/F/B/I/J/K/K_1`), checked name by name against the replay diff; 2 changed types, the two `DiskFraming` statements whose hashes return to their base values (3226562774, 995586449) by the `fix/waves` restore; 0 module moves. Tool verdict FAIL by construction (unaccepted additions) |

## Left (deliberately not done in the replay; see NEXT_STEPS)

- `Hyperbolic/Models.lean` is one 7,870-line module (nine namespaces); `CurveTransport.lean` is 1,957 lines.
- 275 added lines carry manuscript-style labels ("Textbook source: `CENTER_…_TEXTBOOK.md`", "G04.F, canonical
  lines 125–126", "j.6.A"), 255 of them in `Models.lean`.
- `Models.lean` builds `upperHalfPlaneLengthMetricSpace` and proves it proper and complete; Mathlib has
  `MetricSpace ℍ` and `ProperSpace ℍ` (`UpperHalfPlane/Metric.lean`). No lemma identifies the two distances.
- ~240 lint warnings came over unchanged (Models 201, CurveTransport 35).
- The cube-root lemma is in `Lib` by dependency; by topic it belongs with the exponent-3 material in
  `Hopf/Proof/…/SectorRoots`.
- `center-solution` has moved past the pin (`75a6f9a9`, +304 lines on `GeodesicEquations.lean`, 27 probes).
- While the source keeps appending to these files, restructuring them here turns later clean cherry-picks into
  hand reroutes; the split, the label sweep and the Mathlib bridge wait for the owner's word.
