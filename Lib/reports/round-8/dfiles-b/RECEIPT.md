# Round-8 receipt: `dfiles-b`

Packet: the D-verdict files of `Lib/reports/round-7/judgement/d-files.md` under `Lib/Algebra`,
`Lib/AlgebraicTopology`, `Lib/GroupTheory`, `Lib/LinearAlgebra`, `Lib/Analysis`, `Lib/Data`.
Worktree `/home/goblin/hopf-r8-dfiles-b`, branch `r8/dfiles-b`, base `4e15a034`.

Two files named in the packet were already settled by the round-7 names branch and were skipped:
`Lib/GroupTheory/SplitExtension.lean` (kept: Mathlib's `GroupExtension.Splitting` needs the
conjugation action) and `Lib/LinearAlgebra/Dual/Contragredient.lean` (already deleted at the base).

## Per item

| file | verdict executed | commit |
| --- | --- | --- |
| `Lib/Algebra/Group/SurjectiveDescent.lean` | deleted; Mathlib twins named below | `fff26c16` |
| `Lib/Algebra/Group/ResidualRelations.lean` | moved to `Hopf/Proof/Algebra/Group/ResidualRelations.lean` | `282ec4c1` |
| `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | moved to `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | `23f6eb4d` |
| `Lib/Algebra/Group/LatticeImageCollapse.lean` | moved to `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean` | `31c38660` |
| `Lib/Analysis/Real/MeshScale.lean` | folded into its only consumer, renamed out of Mathlib's `Real` | `b67b67df` |
| `Lib/Data/Int/SignedResidual.lean` | moved to `Hopf/Proof/Data/Int/SignedResidual.lean`, renamed out of Mathlib's `Int` | `cd893c55` |
| `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` | moved to `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean` | `b5767bb7` |
| `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean` | moved to `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean` | `ba11838f` |
| `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | moved to `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | `ba11838f` |
| `Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean` | island kept in Lib, renamed by its statement | `67f49883` |
| `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean` | **partial**: stray general lemmas extracted; file cannot leave Lib (see below) | `513197b9` |
| `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean` | **partial**: general island given its own documented module; file cannot leave Lib (see below) | `9ec657d4` |

### `Lib/Algebra/Group/SurjectiveDescent.lean` — deleted

Auditors: "Mathlib already has it: `MonoidHom.liftOfSurjective`". The only consumer was
`Lib/AxiomAudit.lean`; its probe block and the `Lib.lean` entry were removed. Twins, verified with
`#check` under `lake env lean` before deleting:

| deleted | surviving twin |
| --- | --- |
| `descendHomOfSurjective` | `MonoidHom.liftOfSurjective` (**`Mathlib/Algebra/Group/Subgroup/Basic.lean:930` — corrected; this receipt and commit `fff26c16` both said `Subgroup/Ker.lean`, where the name does not occur; the packet had it right**) |
| `descendHomOfSurjective_comp` | `MonoidHom.liftOfRightInverse_comp` (`liftOfSurjective` is `liftOfRightInverse` at `Function.surjInv`) |
| `fibre_constant_of_ker_le` | **deleted, no named twin (corrected)**.  The `{ g // f.ker ≤ g.ker }` subtype packaging named here is a *type*, not a declaration, and it does not state the implication `∀ a b, f a = f b → g a = g b`; Mathlib has no lemma of that shape (`ker_le_ker`, `ker_le`, `eq_of_ker_le`, `le_ker_iff` were all searched), and `MonoidHom.liftOfRightInverse_comp_apply` is not one either — it needs a right inverse of `f`, which the deleted lemma does not assume.  The reason for deleting stands: the lemma existed only to convert that hypothesis into the fibre-constancy form `descendHomOfSurjective` demanded, it has no consumer outside `Lib/AxiomAudit.lean`, and its content is a four-line consequence of `MonoidHom.mem_ker` + `eq_of_mul_inv_eq_one` (re-proved by the reviewer).  But the protocol asks for a named twin or an explicit "deleted, no twin, because …" entry, and this is the latter.  **A fix agent is re-adding the declaration** (`Lib/reviews/REVIEW-7-8.md` §3, dfiles-b: "re-add it, four lines"), so this deletion is expected to be undone |

`MonoidHom.liftOfSurjective_comp` does **not** exist in Mathlib v4.33.0; the `_comp` twin is
`MonoidHom.liftOfRightInverse_comp`.

### `Lib/Algebra/Group/LatticeImageCollapse.lean` — moved, and is a duplicate

The 14 declarations duplicate the `LatticeCuspNormalClosure.*` family of
`Hopf/Proof/LCP/BoundaryTopology.lean`, stated there for `PeriodLattice = Fin 4 → ℤ`, `A₁`, `A₂`,
`ε = ![1,2,-4,0]`, `ε' = ![1,3,-3,0]` and `γ v = v 0` of `Hopf/Proof/FiniteCore.lean`. That family,
not this module, is what the proof uses; the module had no consumer at all. It was moved rather
than deleted so that no statement is lost (`image_firstBasis_eq` has no counterpart in the
`LatticeCuspNormalClosure` family), and it is pulled into the build by `Hopf/Proof/Final.lean`.
The duplication is recorded here for whoever removes one of the two copies.

### `Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean` — island kept in Lib

The D verdict is about the name ("the paper-facing lower transfer condition"), not the content:
all five declarations are generic over `[CommRing R]`, and the Lib file
`Lib/Algebra/Homology/ThreeColumnSpectralSequence/LowerTransfer.lean` consumes them, so moving
them under `Hopf/Proof` would make a Lib file import `Hopf.*` (forbidden by
`scripts/lib_stock_census.py`'s second guard). The island therefore stays in Lib and is renamed
to say what it asserts; the module docstring gains `## Main results` and a Weibel §5.2 reference.

### The two files that could not leave Lib

`Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean` (65 → 58 declarations) and
`Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean` (48 → 35 declarations) are consumed by
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` (and `MiddleBlocks.lean`,
`SurgeryHomology.lean`):

* from `LocalDegreeNeighborhoods`: `LocalDegree.nonempty_separatedNeighborhoods`,
  `LocalDegree.SeparatedNeighborhoods.overlapMap_coe`,
  `LocalDegree.NativeNeighborhood.singlePoint_cover`, `NativeChartTransition.*`;
* from `OnePointCover`: `OnePointCover.{oldPatch, finitePatch, cover, oldPatch_open,
  finitePatch_open, overlapRadius, overlapRadius_pos}`,
  `SphereNormalCoordinates.normalDerivative_smul_isInvertible`,
  `SpherePoint.{instLocal2, instLocal3}`.

`SurgeryCollapse.lean` belongs to the round-7 **monoliths** packet (another agent) and stays in
Lib, so moving either file under `Hopf/Proof` this round would make Lib files import `Hopf.*`.
What the auditors named as keepable/misfiled was done instead:

* `LinearSphereAction.{sphereMap_comp, sphereMap_trans, normalized_linearSphereMap,
  sphereMap_relative, homology_relative_sign}` → `Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean`
  (docstrings added; that module already owns `LinearSphereAction.sphereMap` and
  `homology_eq_sign_smul`).
* `SublevelDisk.{contractibleSpace, homology_subsingleton}` → `Lib/Geometry/Manifold/Morse/Reeb.lean`
  (docstrings added). The auditors said `Morse/SublevelSets`; `SublevelDisk` itself is declared in
  `Morse/Reeb.lean`, so that is the owner. `Reeb.lean` gains
  `import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance`.
* the 13 `SpherePoint.*` transport declarations → the new documented module
  `Lib/AlgebraicTopology/SingularHomology/SpherePointTransport.lean` ("the special orthogonal
  group acts transitively on the unit sphere by maps of determinant one, and such a map is the
  identity on singular homology"; Hatcher §2.2), which imports only `Mathlib` and
  `Lib.AlgebraicTopology.SingularHomology.LinearSphereAction` instead of `OnePointCover`'s
  48-import block.

**Left for a later round** (needs `SurgeryCollapse.lean` to be settled first): moving the
remaining native-chart / one-point-cover material of those two files under `Hopf/Proof`, their
48-import blocks, and the missing docstrings on their remaining declarations.

## Rename map

`rename-old-to-new.txt` is the human-readable map (`old new`). `rename.txt` is the file handed to
`lean-agent-ide dump --rename`, which per `spec/dump.md` must send every **new** name back to its
**old** spelling, i.e. it is the same map with the columns swapped.

| old | new |
| --- | --- |
| `Real.exists_mesh_scale` | `TopologicalSpace.CubeBoundaryThree.exists_mesh_scale` |
| `Int.signed_residual_coordinate_zero` | `ThreefoldHomology.signed_residual_coordinate_zero` |
| `ThreeColumnPage.LowerTransferCondition` | `ThreeColumnPage.LowerDifferentialsBijectiveAndNeZero` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_coefficients` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_coefficients` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_isUnit_of_coefficients_eq` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_isUnit_of_coefficients_eq` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_injective` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_injective` |
| `ThreeColumnPage.Data.lowerTransferCondition_iff_all_subsingleton` | `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_all_subsingleton` |
| `ThreeColumnSpectralSequence.Convergence.lowerTransferCondition` | `ThreeColumnSpectralSequence.Convergence.lowerDifferentialsBijectiveAndNeZero` |

## Lost names

`envdiff.txt` / `envdiff.json` (copied here) report, over the rename map:

```
constants before 38593 after 38588 (keys 38491 38486)
lost 8 added 3 of which source declarations: 3 0 ; names with changed type 0 of which source: 0
```

The three lost source declarations are exactly the three deleted above; no other name was lost and
no type changed.

| lost source name | surviving twin |
| --- | --- |
| `descendHomOfSurjective` | `MonoidHom.liftOfSurjective` |
| `descendHomOfSurjective_comp` | `MonoidHom.liftOfRightInverse_comp` |
| `fibre_constant_of_ker_le` | **none — deleted with no named twin (corrected)**; see the item-1 table above for the reason and the note that a fix agent is re-adding it |

The remaining five lost / three added entries are auxiliary (`_proof_*`, `.eq_1`) equation and
proof constants of the renamed and moved declarations, which the rename map does not cover;
`envdiff` does not judge them. `changed_type_source`, `changed_type_proof_naming`,
`changed_type_accepted` and `changed_type_all` are all empty.

### Module moves (reported, not judged)

```
      14  Lib.Algebra.Group.LatticeImageCollapse -> Hopf.Proof.Algebra.Group.LatticeImageCollapse
       1  Lib.Algebra.Group.ResidualRelations -> Hopf.Proof.Algebra.Group.ResidualRelations
       5  Lib.Algebra.Homology.ThreeColumnPage.LowerTransfer -> Lib.Algebra.Homology.ThreeColumnPage.LowerDifferentials
       1  Lib.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter -> Hopf.Proof.AlgebraicTopology.FundamentalGroup.VanKampen.FiniteStarCharacter
      21  Lib.AlgebraicTopology.Hurewicz.DegreeSix -> Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix
       2  Lib.AlgebraicTopology.Hurewicz.SphereGenerator -> Hopf.Proof.AlgebraicTopology.Hurewicz.SphereGenerator
       5  Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods -> Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
       2  Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods -> Lib.Geometry.Manifold.Morse.Reeb
      13  Lib.AlgebraicTopology.SingularHomology.OnePointCover -> Lib.AlgebraicTopology.SingularHomology.SpherePointTransport
       1  Lib.Analysis.Real.MeshScale -> Lib.Topology.Dimension.CubeBoundaryThreeLebesgue
       1  Lib.Data.Int.SignedResidual -> Hopf.Proof.Data.Int.SignedResidual
      20  Lib.GroupTheory.PresentedGroup.CentralTwist -> Hopf.Proof.GroupTheory.PresentedGroup.CentralTwist
ambiguous module changes: 0
auxiliary constants that changed module: 34
```

`envdiff`'s `VERDICT FAIL` is the expected consequence of the three intentional deletions; every
lost source name is accounted for in the table above.

## Build

Every edited module was built in the foreground before each commit; the final state builds green:

```
lake build Lib Solution S6Shortcuts S6 Challenge Lib.AxiomAudit
Build completed successfully (9190 jobs).
real    10m28.960s
```

`Lib.AxiomAudit` emits only the three permitted axioms: over the whole audit the axiom lines are
`[propext, Classical.choice, Quot.sound]` (1712), `[propext, Quot.sound]` (112), `[propext]` (10),
and 12 declarations depend on no axiom; no other axiom appears.

```
python3 scripts/lib_stock_census.py --check
stock declarations under Hopf/: 123
ratchet PASS: 123 <= baseline 1648
```

The census is unchanged by the moves: `scripts/lib_stock_census.py` excludes `Hopf/Proof/`.

## New modules

Not registered in `Lib.lean` (they are proof-side):

* `Hopf/Proof/Algebra/Group/ResidualRelations.lean`
* `Hopf/Proof/Algebra/Group/LatticeImageCollapse.lean`
* `Hopf/Proof/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean`
* `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean`
* `Hopf/Proof/AlgebraicTopology/Hurewicz/SphereGenerator.lean`
* `Hopf/Proof/Data/Int/SignedResidual.lean`
* `Hopf/Proof/GroupTheory/PresentedGroup/CentralTwist.lean`

Registered in `Lib.lean`:

* `Lib/AlgebraicTopology/SingularHomology/SpherePointTransport.lean`
* `Lib/Algebra/Homology/ThreeColumnPage/LowerDifferentials.lean` (renamed from `LowerTransfer.lean`)

The three modules whose declarations have no consumer (`ResidualRelations`,
`FiniteStarCharacter`, `LatticeImageCollapse`) are pulled into the proof build by
`Hopf/Proof/Final.lean`; the others are imported by the file that uses them
(`Hopf/Proof/LCP/IntegralHomology.lean`, `Hopf/Proof/LCP/BoundaryTopology.lean`,
`Hopf/Recognition.lean`, `Hopf/Proof/Recognition.lean`).

## Commits

`4e15a034..` (oldest first)

```
fff26c16 Lib/Algebra/Group/SurjectiveDescent.lean: delete (Mathlib has it)
282ec4c1 Lib/Algebra/Group/ResidualRelations.lean: move to Hopf/Proof
23f6eb4d Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean: move to Hopf/Proof
31c38660 Lib/Algebra/Group/LatticeImageCollapse.lean: move to Hopf/Proof
b67b67df Lib/Analysis/Real/MeshScale.lean: fold into its only consumer
cd893c55 Lib/Data/Int/SignedResidual.lean: move to Hopf/Proof and out of Int
b5767bb7 Lib/GroupTheory/PresentedGroup/CentralTwist.lean: move to Hopf/Proof
ba11838f Lib/AlgebraicTopology/Hurewicz/{DegreeSix,SphereGenerator}.lean: move to Hopf/Proof
67f49883 Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean: name the island by its statement
513197b9 Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean: extract the stray general lemmas
9ec657d4 Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean: give the sphere-transport island its own owner
```

`DegreeSix` and `SphereGenerator` share one commit: `SphereGenerator` imports `DegreeSix` and is
its only Lib consumer, so splitting them would leave a Lib file importing `Hopf.*` at the
intermediate commit.

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r8-dfiles-b.md` (ACCEPT WITH FINDINGS; every move,
rename and extraction is statement-preserving and fully reconciled against envdiff — all 12 commits
and the whole branch diff were read and the ~60 touched declarations checked exhaustively, not
sampled).  These corrections are to this receipt's text only; no Lean file was changed by them.

1. **`fibre_constant_of_ker_le` was deleted without a named twin (finding 1)**, corrected in both
   tables above.  The "twin" given — Mathlib's `{ g // f.ker ≤ g.ker }` subtype packaging — is a
   type, not a declaration, and does not state the implication.  Mathlib has no lemma of that shape.
   Nothing mathematical is lost (four lines from `MonoidHom.mem_ker` + `eq_of_mul_inv_eq_one`; no
   consumer outside `Lib/AxiomAudit.lean`), but the entry must read "deleted, no twin, because …",
   and it now does.  **A fix agent is re-adding the declaration** under the packet-level fix list
   (`Lib/reviews/REVIEW-7-8.md` §3, dfiles-b), so the deletion is expected to be undone; the same
   correction is made in `Lib/reports/round-8/MERGE.md`, which also named no twin.
   Rule adopted: a lost-source-name table must name a **declaration** per row, or carry an explicit
   "no twin, reason" — free text describing a type passed the envdiff reconciliation while naming
   nothing checkable.

2. **Wrong Mathlib file for `MonoidHom.liftOfSurjective` (finding 2)**, corrected in the item-1
   table.  It is `Mathlib/Algebra/Group/Subgroup/Basic.lean:930`, not
   `Mathlib/Algebra/Group/Subgroup/Ker.lean` (where `grep -n liftOfSurjective` is empty); the packet
   had it right at "Basic.lean l.932" and both this receipt and commit `fff26c16` copied a wrong
   path.  The twins themselves are correct — `liftOfSurjective` is an `abbrev` for
   `liftOfRightInverse` at `Function.surjInv`, and `liftOfRightInverse_comp` is the `_comp` half —
   and the claim that `MonoidHom.liftOfSurjective_comp` does not exist in v4.33.0 is true (only
   `RingHom.liftOfSurjective_comp` does).  Mathlib twin citations should carry a `file:line`
   produced by `grep`, not from memory.

3. **Packet suggestions silently not taken (finding 3).**  The packet asked, for
   `Hurewicz/SphereGenerator.lean`, to state `exists_sphereMap_of_homologyEquiv` for general `n ≥ 2`
   next to `HopfDegree.sphere_homotopicRel_of_topClass_eq` before moving, and for
   `FiniteStarCharacter` and `SignedResidual` to inline at the call site.  None was done, and this
   receipt neither does them nor lists them under "Left for a later round".  The moves are
   statement-preserving, so this is a reporting gap, not unsoundness.  Recorded here as **left,
   with no attempt**.  Note also the honest description of the three consumer-less modules
   (`ResidualRelations`, `FiniteStarCharacter`, `LatticeImageCollapse`, verified to have no consumer
   at base beyond `Lib.lean`/`AxiomAudit.lean`): they are **dead code parked under `Hopf/Proof`**,
   kept alive by three imports in `Hopf/Proof/Final.lean`.

4. **The stock/proof import direction changed and the receipt does not say so (finding 4).**
   `Hopf/Recognition.lean` — a *stock* file, not under `Hopf/Proof` — gained
   `import Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix`; at base it had zero `Hopf.Proof`
   imports.  No rule in the brief forbids it and the census ratchet counts declarations only, but it
   should have been recorded.  In the same class: the unused
   `import Lib.GroupTheory.PresentedGroup.CentralTwist` lines were dropped from the stock
   `Hopf/LCP/{BoundaryTopology,IntegralHomology}.lean` (correct — `TwistGroup` is used only in
   `Hopf/Proof/LCP/BoundaryTopology.lean`) and are not listed either.

5. **Unlisted cosmetic edits (finding 5).**  (a) A new section header
   `/-! ## Lib.Algebra.Group.DeterminingFamily -/` was inserted in `Lib/AxiomAudit.lean` (the
   `DeterminingFamily` probes had been sitting under the removed `LatticeImageCollapse` header).
   (b) The seven moved files drop the `Copyright (c) 2026 Fabian Franz` / `Authors` header lines for
   the `Hopf/Proof` SPDX style but omit the `/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/` first
   line that every other `Hopf/Proof` file carries.  (c) `CentralTwist.lean` also lost its unused
   `open Set Function Filter Manifold Topology` line.  All harmless; all unrecorded until now.

6. **One citation is loose (finding 6), a code fix.**  `LowerDifferentials.lean` cites Weibel §5.2;
   that section defines bounded spectral sequences, convergence and edge maps and treats the
   two-column collapse, and the reviewer does not recall a three-column statement there.  The
   reference is to a section, not a numbered result, so it is loose rather than wrong.  The Hatcher
   §2.2 citation on `SpherePointTransport.lean` is correct.
