# Round-8 receipt: `dfiles-c` (three sheaf files graded D)

Branch `r8/dfiles-c`, base `4e15a034`, worktree `/home/goblin/hopf-r8-dfiles-c`.
Packet: the last three entries of `Lib/reports/round-7/judgement/d-files.md`.

## Per item

### 1. `Lib/Topology/Sheaves/Cohomology/SphereTwo.lean` — moved to `Hopf/Proof/`

Commit `702a01f0`.

The audit verdict is "proof-specific: a special case of the project's own
`CoveringDimension.lean`, wrapped for the application", and the suggestion is to move the file
to `Hopf/Proof`.  Done: the file is now
`Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean`.

Moved, statements byte-identical:

| declaration |
| --- |
| `TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo` |
| `TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo` |
| `TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo` |
| `TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo` |

plus the file's two anonymous `local instance`s (`Additive` for global sections, `HasExt` for
the sheaf category) and one auxiliary proof term.

Changed around the move:

* standard copyright/SPDX header added (the file had none);
* module docstring rewritten.  It now names the textbook result — Godement, *Topologie
  algébrique et théorie des faisceaux*, II.5.12 — and the two library declarations this file
  instantiates, `TopCat.SheafCohomology.derivedGlobalSections_isZero_of_coveringDimensionLE`
  (`Lib/Topology/Sheaves/Cohomology/CoveringDimension.lean`) and
  `TopologicalSpace.SphereTwo.hasCoveringDimensionLE_two_of_homeomorph`
  (`Lib/Topology/Dimension/SphereTwo.lean`), and says why the file is not library material.
  The manuscript's "Corollary 6.5, equation (n)" pointers are kept: under `Hopf/Proof/` they
  are the right kind of comment.
* `Lib.lean`: the module line removed.
* `Lib/AxiomAudit.lean`: the four `#check` / `#print axioms` probes removed.  `Lib` may never
  import `Hopf.*` (guarded by `scripts/lib_stock_census.py`), so the probes cannot follow the
  declarations; there is no `Hopf`-side probe file to move them to, and creating one was out
  of scope.  The declarations remain axiom-audited transitively: they are in the import
  closure of `Solution.lean`, whose `#print axioms` line is unchanged.
* `Hopf/Proof/Final.lean`: added `import Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo`.
  The file had **no** consumer on this base — the only references to it were `Lib.lean` and
  the `AxiomAudit` probes; its manuscript consumers live on `w4-w1-solution`.  The `Hopf`
  lean_lib has no root module, so a `Hopf/**` file is compiled only if something in the
  `Solution` import graph imports it; without this line the four theorems would stop being
  built and would leave the environment dump entirely.  `Hopf/Proof/Final.lean` is the sink of
  that graph (it is what `Solution.lean` imports), which is why the line goes there.

### 2. `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` — stays; renamed and documented

Commit `d87ad506`.

**Why it stays.**  The audit asks for deletion in favour of
`CategoryTheory.Abelian.Ext.instAddCommGroup`.  The round-7 names pass already tried exactly
that (`Lib/reports/round-7/names/RECEIPT.md`, row for this file): all call sites were rewritten
to Mathlib's instance, the `public import`s were replaced, the file was deleted, and
`lake build Lib` then failed with `failed to synthesize Add (Sheaf.H Q 0)` /
`AddZero (Sheaf.H F n)` in `Lib/Topology/Sheaves/Cohomology/ShortExactDegreeOne.lean` and
`Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean`.  Typeclass resolution does not
see through `CategoryTheory.Sheaf.H` to `Ext`, so this registration is load-bearing; closing
the gap is an upstream change to `Sheaf.H`.  The attempt was reverted then and is not repeated
here.

**What was done instead** (the part of the audit row that does not require deletion):

* renamed `CategoryTheory.Sheaf.cohomologyAddCommGroup` to
  `CategoryTheory.Sheaf.instAddCommGroupH` — the standard Mathlib instance name for
  `AddCommGroup (Sheaf.H F n)`; the old name mentioned a `cohomology` that does not occur in
  the type.  Statement, binders, universes and proof term are unchanged.  All eleven call
  sites were updated (`Lib/AxiomAudit.lean`,
  `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean`,
  `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/CanonicalPositive.lean`,
  `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/ConstantPointFibre.lean`,
  `Lib/Topology/Sheaves/ConstantSheafH1.lean`, `Lib/Topology/Sheaves/ConstantProductH1.lean`,
  `Lib/Topology/Sheaves/ConstantProductPositiveFibreIndependence.lean`);
* standard copyright/SPDX header added;
* module docstring rewritten with `## Main results` and `## Implementation notes`.  It names
  the two Mathlib files the content comes from
  (`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` for `Sheaf.H` being `Ext`,
  `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean` for
  `Ext.instAddCommGroup`), states that the proof term *is* that Mathlib instance, and records
  the failed-deletion experiment so the next audit does not repeat it.  The previous "This
  module owns that unconditional instance" ownership language is gone;
* declaration docstring rewritten to say the same in one sentence.

### 3. `Lib/Topology/Sheaves/SheafificationLocal.lean` — stays; documented

Commit `042e2662`.

**Why it stays.**  Mathlib has the two facts the file *cites* but not the three it *proves*
(`Lib/reports/round-7/names/RECEIPT.md`): `exists_local_representative`, `germ_unit_eq_iff`,
`exists_restriction_eq_of_germ_unit_eq`.  Four `Lib` modules use them and/or `sheaf`/`unit`
(`Leray/SheafificationStalkCompatibility`, `Leray/SheafificationNeighborhoodGerm`,
`Leray/CanonicalPositiveNeighborhoodSection`, `SingularCochainSheaf/GlobalSections`; also
`SheafificationLocalGerm` and `SingularCochainSheaf/GlobalKernelLocal`).  Deleting them means
restating and reproving in all of those — a proof change, not a documentation pass.

**What was done** — documentation only; no declaration added, removed, renamed, weakened or
generalised:

* module docstring rewritten with `## Main results` (the three theorems this file contributes)
  and `## References` naming every Mathlib input:
  `CategoryTheory.Presheaf.isLocallySurjective_toSheafify`
  (`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`),
  `TopCat.Presheaf.isLocallySurjective_iff`
  (`Mathlib/Topology/Sheaves/LocallySurjective.lean`),
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` and `TopCat.Presheaf.germ_eq`
  (`Mathlib/Topology/Sheaves/Stalks.lean`), with an explicit statement that Mathlib does not
  carry the three shrink-the-neighbourhood results;
* docstrings added to the four undocumented declarations `sheaf`, `unit`, `unit_stalk_isIso`,
  `unit_stalk_injective`.  The `sheaf` and `unit` docstrings spell out the Mathlib terms they
  abbreviate, which answers the audit's "every downstream file must then unfold them".

`sheaf` and `unit` were **not** renamed.  The audit row asks for their removal, not for a
different name; introducing a third spelling would churn six modules without addressing the
finding, and removal is the refactor described above.

## Rename map

`Lib/reports/round-8/dfiles-c/rename.txt` (copied from the scratch directory).  Note the
direction: `lean-agent-ide dump --rename` is applied to the **after** dump and its `report` /
`publicType` look the *current* name up in the map, so each line is
`<name in the after environment> <name to report>`.  A map written the other way round is a
silent no-op (that was checked: the first run of the dump, with the line reversed, reported
145 lost / 145 added).

| after-dump name | reported as | why |
| --- | --- | --- |
| `CategoryTheory.Sheaf.instAddCommGroupH` (+ `._proof_1` … `._proof_5`) | `CategoryTheory.Sheaf.cohomologyAddCommGroup` (+ `._proof_1` … `._proof_5`) | the rename of item 2 |
| `instAdditiveSheafOpensCarrierGrothendieckTopologyAddCommGrpCatObjOppositeFunctorSheafSectionsOpTop_hopf` (+ `._proof_1`) | `…_lib_1` (+ `._proof_1`) | auto-generated name of the moved file's anonymous `local instance`; the suffix encodes the Lake library, so moving the file from lean_lib `Lib` to lean_lib `Hopf` renames it |
| `instHasExtSheafOpensCarrierGrothendieckTopologyAddCommGrpCat_hopf` | `…_lib_2` | same, for the second `local instance` |

The two auto-generated instances occur in the statements of three of the four moved theorems,
so without these three map lines those theorems' `typeHashPublic` changes and envdiff reports
them as lost and added.  The `_lib`/`_lib_1` numbering of the anonymous instances in the
modules that did **not** move (`Cohomology/CoveringDimension`, `Cohomology/Cech/Ext`,
`Cohomology/Cech/DerivedGlobalSections`) is unchanged, so no other entry is needed; this was
checked by diffing the two name sets, whose symmetric difference is exactly the nine names in
the map.

## Lost-name table

None.  `lost 0 / added 0 / changed type 0`.  No declaration was deleted in this packet.

## Envdiff summary

`lean-agent-ide dump Solution Lib --modules Hopf,Lib` before and after (38593 constants each),
`tools/envdiff.py`, receipt in `envdiff.json` beside this file:

```
constants before 38593 after 38593 (keys 38491 38491 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
       6  Lib.Topology.Sheaves.Cohomology.SphereTwo -> Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo
ambiguous module changes: 0
auxiliary constants that changed module: 1
VERDICT PASS
```

The single module move is item 1 (four theorems plus the file's two `local instance`s; the one
auxiliary constant is the `_proof_1` of the first of them).  Nothing is lost, nothing is added,
no type changed.

## Build

All from the worktree root, Lean/Mathlib v4.33.0:

```
lake build Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo   0
lake build Hopf.Proof.Final                                   0
lake build Lib.Topology.Sheaves.Cohomology.AddCommGroup        0
lake build Lib.Topology.Sheaves.SheafificationLocal            0
lake build Lib                                                 0
lake build Solution S6Shortcuts S6 Challenge                   0
lake build Lib.AxiomAudit                                      0
python3 scripts/lib_stock_census.py --check                    0
```

`Lib.AxiomAudit` reports only `propext`, `Classical.choice`, `Quot.sound` (the distinct axiom
sets printed are `[propext, Classical.choice, Quot.sound]`, `[propext, Classical.choice]`,
`[propext, Quot.sound]`, `[propext]`).  `Solution.lean` still prints
`'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice,
Quot.sound]`.  The census ratchet passes: `123 <= baseline 1648` (unchanged — the moved file
lands under `Hopf/Proof/`, which the census excludes).

## Commits

```
702a01f0  Lib/Topology/Sheaves/Cohomology/SphereTwo.lean: move to Hopf/Proof (D verdict)
d87ad506  Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean: name the Mathlib twin, keep the instance
042e2662  Lib/Topology/Sheaves/SheafificationLocal.lean: name the Mathlib inputs, document every declaration
```

(plus this receipt)

## Left undone

* `sheaf` / `unit` in `SheafificationLocal.lean` are still there; removing them, as the audit
  asks, is a refactor of six `Lib` modules.
* `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` still exists; deleting it needs the
  `Sheaf.H` instance-resolution gap fixed upstream.
* The four axiom probes for the moved `sphereTwo` theorems have no home: `Lib/AxiomAudit.lean`
  cannot import `Hopf.*`, and there is no `Hopf`-side probe file.  If one is wanted, that is a
  new file and a decision for the owner.
