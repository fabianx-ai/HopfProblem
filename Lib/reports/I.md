/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane I report — quotient manifolds, mapping torus, split extensions

**Current status:** see the current-tree audit and Wang ownership handoff below; earlier remaining-unit lists are historical.

**Status: 4 of ~14 units landed (green); the remainder is enumerated below.**

## Landed

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/Instances/RiemannSphere.lean` | PeriodConstruction TwoAffineCharts 7758–8011 + RiemannSphere 8012–8082 (pulled forward from lane I by lane H to unblock the atlas) | 37 | (H baseline) |
| `Lib/Topology/Algebra/FreeActionLocus.lean` | PeriodConstruction FreeActionLocus.* | 13 | 867880d |
| `Lib/Geometry/Manifold/Quotient/LocalOrbit.lean` | PeriodConstruction LocalOrbitQuotient.* subset | 17 | 91dc733 |
| `Lib/Geometry/Manifold/Quotient/Atlas.lean` | PeriodConstruction OnePointAtlas.* + BranchedQuotientAtlas.* subset | 22 | 91dc733 |
| `Lib/Topology/MappingTorus/Basic.lean` | LocalModels MappingTorus.* 6899–8394 | 76 | 79211df |

## Remaining lane I units (resume order, each = one cfg + delete + build + commit)

1. `MappingTorus/HomologyCover.lean` ← BoundaryTopology `MappingTorusHomology.*` 3988–4609 (58)
2. `MappingTorus/Wang.lean` (+ `WangAlgebra.lean` split if desired) ← IntegralHomology `MappingTorusHomology.*` 7576–8688 (105) — axiom probe `wang_exact_at_mappingTorus`
3. `GroupTheory/SplitExtension.lean` ← BoundaryTopology `SplitGroupExtension.*` (13) — probe `SplitGroupExtension.mulEquiv`
4. `GroupTheory/PresentedGroup/CentralTwist.lean` ← BoundaryTopology `TwistGroup.*` (21)
5. `FiberBundle/TwoOpenTransition.lean` ← BoundaryTopology `TwoOpenTransition.*` (45)
6. `Topology/Covering/Quotient.lean` ← LocalModels `CoveringQuotient.*` (17) + DiscreteQuotient (13)
7. `Topology/Covering/DiagonalQuotient.lean` (+ `FundamentalGroup/DiagonalQuotient.lean`) ← AF `DiagonalQuotient.*` (41) + BT `DiagonalQuotient.*` (36)
8. `Homotopy/SublevelRetraction.lean` ← LocalModels `ThreefoldHomologyFinitenessRetraction.*` (22; rename per lane task)
9. `Homotopy/LocalCollapse.lean` ← CuspFilling `CuspRetraction.Patching.*` 490–631 (11; rename per lane task)
10. `Quotient/Covering.lean` ← CuspFilling `InvariantSubsetQuotient.*` (14) + `CoveringOrthant.*` (6) + `ProductRestriction.*` (5)

## Lane I honest obstructions so far

- LocalOrbitQuotient.localHomeomorph + 3 atlas decls: welded to
  `SpecialPeriods.triangleGeometricAction` (project) and
  `BranchedQuotientAtlas.contDiffAt_transition_of_lift`
  (Hopf/LCP/Specialization.lean 14450, outside all lanes' ranges).

---

# Lane I, session 2 addendum (HomologyCover landed; Wang blocked)

## Landed this session

- `Lib/Topology/MappingTorus/HomologyCover.lean` (58, d92f3cf)
- `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` (58, 5e9a74e — pull-forward)
- `Lib/AlgebraicTopology/SingularHomology/CrossInsert.lean` (3, 5e9a74e — pull-forward)

## Wang (`MappingTorus/Wang.lean`, IH 7576–8688, 105 decls): BLOCKED

Closure requires, besides landed material, the cross-product / circle-path cluster:
- `PeriodTorusHigherHomology.crossProduct*` + `chainBilinear*`/`homologyDesc*`/
  `homologyLinearMap*` in Hopf/Hurewicz.lean (~106 decls, dense `attribute
  [local instance] integerTensorModule in` runs), and
- `PeriodTorusHigherHomology.positiveCircleCross`, `CirclePaths.*`,
  `twoChainSmallCycle*`, `connectingHomomorphism_twoChain`,
  `crossProductEdge_path_boundary` in Hopf/LCP/CuspFilling.lean.

First extraction attempt ended in a proof-script rewrite loop (rejection test 5).
This cluster needs its own declaration-level Stage-4 cut (proposed target
`Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`) before Wang can move.
The four `LinearMap.map_smul` proof sites that failed under the local
`integerLinearMapModule` instance are the seam to re-derive first.

## Tooling

- extract.py still mangles one-line `attribute [local instance] X in` in two
  ways (head stripped + indented). Post-extract normalizer used:
  `re.sub(r'^\s*(?:attribute \[local instance\] )?((?:\w+\.)+integer(?:Tensor|LinearMap)Module) in\s*$', r'attribute [local instance] \1 in', ...)`.
  Fix the hoister before the next unit.

---


---

# Wang obstruction (2026-09-12, NEXT-STEPS item 6)

The cross-product coherence web (114 declarations) landed in
`Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (276c58b) — that
half of item 6 is done. Landing `Lib/Topology/MappingTorus/Wang.lean`
(`MappingTorusHomology.*`, IH 7576–8684, 105 declarations, contiguous,
zero interleaved) is still obstructed, but now only by three named clusters
outside the block:

1. `Elliptic.HigherHomology.MappingTorusQuotient.*` (Specialization, lane C) —
   `Circle`, `mappingTorusHomeomorph`, `mappingTorusHomeomorph_project`,
   `project`, plus their own dependency cone (~30 declarations).
2. `PeriodTorusHigherHomology.{CirclePaths.positiveLoop, positiveCircleCross,
   connectingHomomorphism_twoChain, crossProductEdge_path_boundary,
   twoChainSmallCycle}` (CuspFilling, lane C/J) — ~8 declarations.
3. `CuspRetraction.Patching`-adjacent short helpers surfaced by the same cone.

Moving these means pure-moving lane-C/J material (the first move attempt
dragged 28 Specialization declarations before this was stopped and reverted).
They are next after the C/J owner lands those clusters in Lib, or with the
owner's blessing to move them as part of lane I.

## Wang landing attempt 2 (2026-09-13, post-rename): reverted; CHARGED boundary reached

Second full attempt to land `Lib/Topology/MappingTorus/Wang.lean`, this time
keeping the `Mathoverflow1973` wrapper (pure move, no concurrent shim or
wrapper surgery). Tooling: family-closure mover driven by build errors, plus
HEAD-order topological re-sort of the target file (needed: per-round appending
inverts declaration order and Lean resolves bare names through the current
declaration's own namespace path, so order is load-bearing).

What was proven before the revert:

- The seed families move cleanly: 115 `PassageHomology.*`/`MappingTorusHomology.*`
  declarations from `Hopf/SingularHomology.lean` and `Hopf/LCP/IntegralHomology.lean`.
- The closure then pulls, in order: `PartialChart`, `Elliptic.HigherHomology.
  MappingTorusQuotient`, `Elliptic.CyclicAction`, `Elliptic.FiniteQuotient`
  (wrapping `Elliptic.HigherHomology` wholesale, 402 + 280 declarations),
  then the period-structure universe from `Hopf/LCP/LocalModels.lean` and
  `Hopf/FiniteCore.lean`: `PeriodPoint`, `PeriodDomain`, `Lattice`,
  `LatticeMatrix`, `T₁`/`T₂`/`A₁`/`A₂`, `standardLattice`, `ComplexPlane₂`,
  `columnLattice`, and finally `SpecialPeriods.*`.

That last step is the wall. `SpecialPeriods.Threefold.*` is project vocabulary
(CHARGED per `lean-protocol.md`); a Wang `Lib/` file cannot contain it, and the
Wang sequence code as written references it. The obstruction is therefore not
mechanical but classificatory: landing Wang as a pure move requires first
splitting the period-structure cluster into a FREE core (abstract lattice with
automorphisms, the `T₁`/`T₂`/`A₁`/`A₂` gluing data, `PeriodPoint` Mobius
steps) and a CHARGED shell (`SpecialPeriods.Threefold` instantiations). That
split is a generalize-then-move item needing the textbook file, not a pure
move, and belongs to the owner's sequencing.

Also recorded for whoever retries: alias spellings (`FirstHurewicz.X` for
`SingularChains.X`, `PeriodTorusHigherHomology.X` for `SingularHomology.X`)
are shim artifacts and must be rewritten to true names at the move boundary;
standalone `@[...]` attribute lines must travel with their declaration (the
mover's doc-comment/`attribute ... in` upward walk misses them; 398 lines had
to be re-anchored in the attempt).

## Current-tree audit (2026-09-13, GLM seat run by Devin/Astra)

The historical remaining-unit list is not the current state. `HomologyCover`,
`SplitExtension`, `CentralTwist`, `TwoOpenTransition`, `Covering/Quotient`,
`Covering/DiagonalQuotient`, `Homotopy/SublevelRetraction`,
`Homotopy/LocalCollapse`, and `Covering/InvariantSubset` already exist in Lib.
The corresponding generic namespace blocks are no longer in Hopf; they are
not re-extracted. The six `CoveringOrthant` local-chart declarations are the
independent quotient-covering remainder moved by this unit. They compose a
local inverse of a quotient covering with a source chart and verify the
source, inverse, target and coordinate formulas (Forster, *Lectures on Riemann
Surfaces*, §§1–3, quotient charts).

`TwistGroup.c_twistOrder` and the two `TwistGroup.main_*` consequences remain
in Hopf: their `twistOrder` uses `S6.TwoExceptionalGluing.gluingDefect 3 4`.
This is not a pure generic extraction. The local-orbit/atlas obstructions
recorded earlier are also not claimed resolved by this unit.

### Wang ownership handoff — do not broaden the family cut

At source revision `e5a00e9`, the exact Hopf type-and-value dependency graph
for the remaining `MappingTorusHomology` and `PassageHomology` families maps
to 232 explicit source declarations: CuspFilling 71, IntegralHomology 103,
Specialization 43, SingularHomology 15. Generated kernel helper names are
not treated as reasons to move their containing source families. This
Hopf-only closure does not reach `SpecialPeriods`; the earlier wholesale
family expansion does not establish a CHARGED obstruction for this cut.

The owner explicitly kept the C/J-owned circle cross-product prerequisites
with C/J. They are not moved by this seat. **Wang and Mathoverflow1973 wrapper
removal remain pending on that ownership handoff**, not silently abandoned.
The exact candidate source names/ranges/hashes are in
`Lib/reports/I-wang-dependencies.json`; this is dependency evidence, not an
authorization to move every row. No historical draft is copied.

`MappingTorusHomology.wang_exact_at_fibre` and
`MappingTorusHomology.wang_exact_at_mappingTorus` already live in
`Lib/Topology/MappingTorus/HomologyCover.lean`. The outstanding Wang block
contains finite-cover transfer and norm formulas, not the first proof of
Wang exactness. `Lib/Topology/MappingTorus/Wang.lean` is not landed yet.

### Quotient-chart remainder receipt

Six declarations moved verbatim from `Hopf/LCP/CuspFilling.lean:1358–1400`
at `e5a00e9` into `Lib/Topology/Covering/Quotient.lean`; individual ranges,
attribute wrappers and SHA-256 hashes are recorded in
`Lib/reports/I-quotient-chart-provenance.json`. No proof term or statement
changed. The sole consumer edit is the explicit Quotient module import;
the target was already registered in `Lib.lean`.

`lake build Lib.Topology.Covering.Quotient Hopf.LCP.CuspFilling` passed with
pinned Lean 4.33.0. Temporary `I_QuotientCheck.lean`, importing only the Lib
module, checked `CoveringOrthant.localChart_symm_apply` and printed exactly
`[propext, Classical.choice, Quot.sound]` for
`CoveringOrthant.localChart_coordinate_identity`. Source/target byte checks
passed for all six declarations, and `git diff --check` was clean.
Census: **2,293 → 2,287**, prefix list unchanged. The next consolidated
consumer-chain gate will include this move; it is not claimed rerun here.
Wang and wrapper removal remain pending with the C/J owner as stated above.

Consolidated consumer gate after the Suspension rename: `lake build Lib
Solution S6Shortcuts S6 Challenge` and `lake env lean Lib/AxiomAudit.lean`
both exited 0 with pinned Lean 4.33.0. This includes the quotient-chart move
above; the earlier deferred-chain note is now discharged. Wang and wrapper
removal remain pending on the owner's C/J handoff.
