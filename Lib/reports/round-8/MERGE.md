# Round 8 — integration of the seven judgement-round branches into `lib/integration`

Worktree `/home/goblin/hopf-lib-integration`, branch `lib/integration`, common base `4e15a034`,
Lean v4.33.0 / Mathlib v4.33.0.

Merge order (each `git merge --no-ff r8/<name>`):

| # | branch | conflicted files | head after merge |
|---|---|---|---|
| 1 | `r8/dup-sheaf` | (merged before this seat) | `124b7f25` |
| 2 | `r8/pins` | 16 | `5ad9ec3c` |
| 3 | `r8/moved` | 0 | `9ffac3fc` |
| 4 | `r8/dup-hom` | 0 | `1e0cf7ac` |
| 5 | `r8/dfiles-c` | 3 | `12232351` |
| 6 | `r8/dfiles-b` | 0 | `1302a5e8` |
| 7 | `r8/dfiles-a` | 2 | `fc6b6ffe` |

## Resolution rule

`dup-sheaf` unified duplicate definitions and rerouted their consumers; `pins` lifted
universe-zero pins in the same files.  Where the two met, the resolution everywhere was:
**keep `dup-sheaf`'s survivor and reroute, and keep `pins`' universe generalisation on whatever
survives**; where `pins` generalised a declaration `dup-sheaf` deleted, the generalisation is
moot and the deletion stands.  No declaration that both sides kept was dropped, no statement was
weakened, and no `sorry`/`axiom` was introduced.

## 2. `r8/pins` — 16 conflicted files, one line each

All sixteen are the same collision: `dup-sheaf` renamed/deleted a sheaf declaration on the
lines `pins` re-spelled at `.{u}`.

| file | resolution |
|---|---|
| `Lib/CategoryTheory/Sites/Leray/ResolutionAbutment.lean` | `TopCat.ConstantSheaf.integralSheaf` (not `Leray.integralSheaf`) with `pins`' `homEquivCoyonedaHomologyOfIsKInjective.{u + 1}` |
| `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikov.lean` | `integralDerivedObject` at `TopCat.{u}` over `TopCat.ConstantSheaf.integralSheaf` |
| `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2Transgression.lean` | survivor `integralSheaf` plus `pins`' explicit `(C := AbelianSheaf Y)` |
| `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean` (7 hunks) | `Leray.integralSheaf` stays deleted (hunk 1 resolved empty); the six consumer hunks take the survivor plus `pins`' `(C := AbelianSheaf Y)` and `Ext.{u}` |
| `Lib/CategoryTheory/Sites/Leray/SheafificationStalkCompatibility.lean` (5 hunks) | `TopCat.Sheaf.sheafification` (survivor) with `AddCommGrpCat.{u}` everywhere |
| `Lib/Topology/Sheaves/Cohomology/AcyclicResolution.lean` | `TopCat.Sheaf.globalSectionsFunctor` at `AddCommGrpCat.{u}` |
| `Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1.lean` (4 hunks) | the file's own `globalSectionsFunctor`, `globalSectionsFunctor_additive` and `unitSheaf` stay deleted (their lifted copies are moot); the four consumers use the survivors at `.{u}` |
| `Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1Naturality.lean` | `TopCat.ConstantSheaf.integralSheaf` at `Ext.{u}` / `Sheaf.H.{u}` |
| `Lib/Topology/Sheaves/Cohomology/FlasqueAcyclic.lean` (2 hunks) | private `constantIntegerSheaf` stays deleted; consumer at `Ext.{u}` over the survivor |
| `Lib/Topology/Sheaves/Cohomology/HomeomorphProjectiveDimension.lean` (2 hunks) | `dup-sheaf`'s renames `integralSheafEquivImageIso`, `integralSheaf_hasProjectiveDimensionLT_iff_of_iso` at `TopCat.{u}` |
| `Lib/Topology/Sheaves/Cohomology/ProjectiveDimension.lean` | rename `integralSheaf_hasProjectiveDimensionLT_iff_cohomology_subsingleton` at `TopCat.{u}` |
| `Lib/Topology/Sheaves/Cohomology/RepresentedOpenProjectiveDimension.lean` (3 hunks) | `dup-sheaf`'s renames (`integralToFreeTop`, `integralSheafFreeTopIso`, `integralSheaf_hasProjectiveDimensionLT_iff_freeOpen_top`) at `TopCat.{u}` |
| `Lib/Topology/Sheaves/FiniteClosedPushforward/AcyclicResolution.lean` | survivor in `h0GlobalIso_mk₀` at `TopCat.{u}` |
| `Lib/Topology/Sheaves/FiniteClosedPushforward/AcyclicResolutionH1.lean` (5 hunks) | survivor throughout at `.{u}` |
| `Lib/Topology/Sheaves/H1Vanishing/Flasque.lean` (2 hunks) | private `constantIntegerSheaf` stays deleted; `Ext.addEquiv₀.{u}` over the survivor |
| `Lib/Topology/Sheaves/SheafificationLocal.lean` | `(TopCat.Sheaf.sheafification X).obj P` (survivor, not the inlined `presheafToSheaf` body) at `AddCommGrpCat.{u}` |

## 3. `r8/moved` — no conflicts

## 4. `r8/dup-hom` — no conflicts

## 5. `r8/dfiles-c` — 3 conflicted files

| file | resolution |
|---|---|
| `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` | `dfiles-c`'s rename `cohomologyAddCommGroup` → `instAddCommGroupH` **and** its new docstring, carried to `pins`' `{X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)`.  `dfiles-c`'s module-docstring sentence "the universes are fixed at `TopCat.{0}`" was false after the lift and now reads "the declaration is universe-polymorphic". |
| `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean` | the consumer `sheafCohomologyAddCommGroup` takes the new name `instAddCommGroupH` at `.{u}` |
| `Lib/Topology/Sheaves/SheafificationLocal.lean` | `dfiles-c`'s four new docstrings kept, on the `pins`-lifted `.{u}` signatures, over `dup-sheaf`'s survivor `TopCat.Sheaf.sheafification`; the `sheaf` docstring now names the survivor, and the module docstring's "everything is at `TopCat.{0}`" reads `TopCat.{u}` |

## 6. `r8/dfiles-b` — no conflicts

## 7. `r8/dfiles-a` — 2 conflicted files

| file | resolution |
|---|---|
| `Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean` | add/add at the end of the file: both blocks kept, concatenated (`dfiles-a`'s five `PuncturedRadial`/`LocalDegree` declarations after `dup-hom`'s four `sphereMap_*`/`homology_relative_sign` declarations) |
| `Lib/Geometry/Manifold/Morse/CutTransport.lean` (2 hunks) | `dfiles-a` deleted the two blocks from the `Lib` file (they moved to `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean`); deletion kept |

Follow-up inside the same merge (not a conflict, but a cross-branch break the merge created):
`dfiles-a`'s new `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` was written on the base
and still named `MorseCancellation.classCoordinateMatrix` and
`MorseCancellation.eq_mul_transvection_of_columns`, which `r8/moved` had renamed.  Four
references retargeted to `LinearEquiv.coordMatrix` and `Matrix.eq_mul_transvection_of_columns`,
exactly as `moved` had done on the `Lib` side.

## Build lines

Per merge, from the worktree root with
`/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake`:

| after merge | command | result |
|---|---|---|
| `r8/pins` | `lake build Lib` | `Build completed successfully (9149 jobs).` |
| `r8/moved` | `lake build Lib` | `Build completed successfully (9151 jobs).` |
| `r8/dup-hom` | `lake build Lib Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9192 jobs).` |
| `r8/dfiles-c` | `lake build Lib Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9192 jobs).` |
| `r8/dfiles-b` | `lake build Lib Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9191 jobs).` |
| `r8/dfiles-a` | `lake build Lib Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9197 jobs).` |

Final, on the integrated head:

| command | result |
|---|---|
| `lake build Lib` | `Build completed successfully (9144 jobs).` |
| `lake build Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9196 jobs).` — `'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | `Build completed successfully (9144 jobs).` — 3300 `depends on axioms` lines, every one a subset of `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| `python3 scripts/lib_stock_census.py --check` | `stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)` / `ratchet PASS: 123 <= baseline 1648` |

## Envdiff

Base dump: the dump of `4e15a034`
(`/home/goblin/.claude/jobs/06995e68/tmp/r8-pins/dump_base.jsonl`, 38593 constants).
After dump: `lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib --rename rename.txt`
on the integrated head, 38254 constants.

`rename.txt` (copied here) is the concatenation of the seven branches' maps in the direction the
tool needs, `<name in the after environment> <name in the base environment>`: 91 entries, keys
unique.  Directions taken from the receipts — `dup-sheaf` (10), `moved`
(`rename-new-to-old.txt`, 34), `dfiles-c` (9), `dfiles-b` (`rename.txt`, 8) and `dfiles-a`
(12, both orientations, disjoint name sets) are already after→base; `dup-hom`'s `rename.txt` is
written base→after and its 18 lines are **reversed** here (its own receipt records that the map
as stored is a no-op on the after dump); `pins` has no renames.

```
constants before 38593 after 38254 (keys 38491 38152)
lost 1151 added 812 of which source declarations: 348 130
names with changed type 771 of which source: 477
auxiliary lost/added/changed (not judged): 803 682 294
module moves (source declarations, 1-to-1): 33 pairs
ambiguous module changes: 0
VERDICT FAIL
```

Full lists: `envdiff.json`, `envdiff.txt` (beside this file).  The `FAIL` verdict is the lost
names and the changed types, both reconciled below; `envdiff` calls any of them unexplained
unless passed with `--accept`.

### Lost-name reconciliation

Subtracting the names that appear in both `lost` and `added` (those are *changed types*, not
deletions), **221 source names are lost and not re-added.  Every one of them is a deletion its
branch's receipt lists, with a surviving twin named there.  Nothing else is lost.**

| count | branch | receipt entry |
|---|---|---|
| 171 | `dup-hom` | `Lib/reports/round-8/dup-hom/RECEIPT.md` §4 table A — `FundamentalGroup.VanKampen.*` deleted with the van Kampen monolith, twin `FundamentalGroup.VanKampen.Cocone.*` in the split (table A lists 228 suffixes; 171 of them carry a declaration range in these dumps and so count as source) |
| 13 | `dup-hom` | §4 table B — `CoverNaturality.*` → `SingularMayerVietoris.*` (table B lists 15) |
| 5 | `dup-hom` | §4 table C — the `CategoryTheory.HomologicalComplex.shortCycleClass*` cocycle-class helpers; three of the five come back promoted out of `private` as `CategoryTheory.ShortComplex.shortCycleClass_{surjective,quotient,eq_zero_iff}` in the new `Lib/Algebra/Homology/ShortComplex/AbCycleClass.lean` |
| 1 | `dup-hom` | §4 table D — `AlgebraicTopology.SingularCochains.homotopy_on_cocycle_succ`, twin `CochainComplex.homotopy_on_cocycle_succ` |
| 28 | `dup-sheaf` | `Lib/reports/round-8/dup-sheaf/RECEIPT.md` items 9 (10 names), 8 (9 names), 7 (9 names) — listed in full below |
| 3 | `dfiles-b` | `Lib/reports/round-8/dfiles-b/RECEIPT.md`, `Lib/Algebra/Group/SurjectiveDescent.lean` deleted: `descendHomOfSurjective` (Mathlib `MonoidHom.liftOfSurjective`), `descendHomOfSurjective_comp` (`MonoidHom.liftOfRightInverse_comp`), `fibre_constant_of_ker_le` |
| 0 | `moved`, `dfiles-a`, `dfiles-c`, `pins` | these four branches delete nothing; their changes are moves, renames and universe lifts |
| **221** | | |

The `dup-sheaf` 28, in full (each → its surviving twin per that receipt):

* item 9 (10): `TopCat.SheafH1.unitSheaf`, `CategoryTheory.Sheaf.Leray.integralSheaf`,
  `TopCat.SheafH1.constantIntegerSheaf`, `TopCat.SheafCohomology.constantIntegerSheaf`
  → `TopCat.ConstantSheaf.integralSheaf`;
  `TopologicalSpace.OpenCover.SetOpenCover.sheafGlobalSectionsFunctor(_additive)`,
  `TopCat.Sheaf.FiniteSupport.topEvaluation` → `TopCat.Sheaf.globalSectionsFunctor(_additive)`;
  `TopCat.SheafificationPushforward.sheafification`,
  `CategoryTheory.Sheaf.Leray.sheafification(_additive)` → `TopCat.Sheaf.sheafification(_additive)`.
* item 8 (9): the nine `TopCat.FunctionSheaf.*` → `TopCat.DependentFunctionSheaf.*` at the
  constant family.
* item 7 (9): `TopCat.SingularCochainSheaf.` `SmallKernelGlobalOne`, `smallKernelGlobalOne`,
  `complexSheaf_exactAt_one`, `exists_restriction_primitive_one`,
  `globalCochainComparison_boundary_detect_one`, `globalCochainComparison_cycle_lift_one`,
  `globalCochainComparison_homology_isIso_one`,
  `globalCochainComparison_homology_isIso_one_of_small_chains`, `globalUnitSurjective`
  → the `_succ` / `SmallKernelGlobal … 1` statements at `0`.

### Added names

Exactly **3** source names are added and were not present before, all documented by `dup-hom`
item 6: `CategoryTheory.ShortComplex.shortCycleClass_{eq_zero_iff,quotient,surjective}`, the
three helpers promoted from `private` when the cocycle-class block moved to
`Lib/Algebra/Homology/ShortComplex/AbCycleClass.lean`.

### Changed types

477 source names changed type; 350 of them `envdiff` itself classifies as `PROOF-NAMING` (the
use-set is unchanged — these are the `pins` universe generalisations).  Of the remaining 127:

* 11 are `dup-hom`'s documented `FundamentalGroup.VanKampen.TwoOpenCover` ⇝
  `…Cocone.TwoOpenCover` substitution in the statement (the nine
  `SpecialPeriods.Threefold.attachment*`, `SphereHomology.suspensionConeCover`,
  `SphereHomology.twoOpenCover_simplyConnectedSpace`);
* 17 more are the van Kampen declarations hand-ported into the `Cocone.` namespace, whose
  statements name the surviving structure;
* the rest sit in the Leray / `Topology.Sheaves` cluster (34 + 20 + 11 + 9 + 5 + 4 + 3 + 2) and
  are the `pins` universe lift combined with `dup-sheaf`'s respelling of a statement onto the
  surviving duplicate — in every case the proposition is unchanged, because each deleted name
  was an abbreviation (or an `n = 0` instance) of its survivor.

### Module moves

33 one-to-one module moves, 0 ambiguous; they are exactly the moves the `moved`, `dfiles-a`,
`dfiles-b`, `dfiles-c` and `dup-sheaf` receipts describe (the `Hopf/Proof/` returns, the new
`Lib` modules `Combinatorics/IndexDisorder`, `Geometry/Manifold/Curve/CircleGluing`,
`Algebra/Homology/ShortComplex/AbCycleClass`, `Algebra/Homology/Homotopy/CocycleEvaluation`,
`Topology/Sheaves/Sheafification`, `Geometry/Manifold/Morse/EqualRangeHomology`,
`AlgebraicTopology/SingularHomology/SpherePointTransport`, and the `SingularCochainSheaf`
`H1` → positive-degree consolidations).  Full list in `envdiff.txt`.
