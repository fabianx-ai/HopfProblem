/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane I report — quotient manifolds, mapping torus, split extensions

**Status: 4 of ~14 units landed (green); the remainder is enumerated below with exact
resume configs (cfg files in ~/s6-notes/hopf-lib-a/).**

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

- `~/s6-notes/hopf-lib-a/dag.py` + `dag_gen.py` → `DAG.md`: computed import DAG
  (dotted-name references over 721fc82 bytes, rename-mapped, family over-
  approximation). Every future unit's import list is now precomputed.
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
