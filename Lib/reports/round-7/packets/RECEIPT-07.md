# Round 7 checklist packet 07 — receipt

Worktree `/home/goblin/hopf-r7-p07`, branch `r7/packet-07`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.

All 32 files of `packet-07.md` are done; nothing is left.
One commit per file, `538f7987..acd98e17` (32 commits).

## Totals

| item | count |
|---|---|
| files done | 32 / 32 |
| module docstrings re-cited or added (item 1) | 30 files |
| declaration docstrings/comments with a manuscript label stripped (item 1) | 297 |
| docstrings added (item 2) | 245 |
| universe pins generalised (item 3) | 1 declaration (`TopCat.Sheaf.pushforwardAdditive`); 29 `.{0}` pins left, forced |
| `: Type` binders widened (item 4) | 7 declarations; **62 left, forced (corrected; the receipt said "58 + 1")** — Wang 58, SphereTwo 1, BasedDiskLifting 2, CubeBoundaryThreeDimension 1 |

No declaration was deleted, renamed, or given a new hypothesis; no `sorry`,
`axiom` or `admit` was introduced.

## Per file

### `Lib/Topology/Dimension/`

| file | item 1 | item 2 | item 3 | item 4 | left / obstacle |
|---|---|---|---|---|---|
| `Covering.lean` | module docstring rewritten (Engelking §1.6, Hurewicz–Wallman Ch. V, Munkres §50; `Main definitions`/`Main results`/`References`), `CD12C-T` label and `T01`–`T06` proof comments removed | 5 added (`refl_index`, `comp_index`, `refl_comp`, `comp_refl`, `comp_assoc`) | none present | none: all binders already `Type u`/`Type v`/… | — |
| `CubeBoundaryThree.lean` | module docstring rewritten (Engelking §1.8, Hurewicz–Wallman Ch. IV, Mathlib `gaugeRescaleHomeomorph`); 26 `Textbook Notation/Definition/Lemma (A0)…(H1)` prefixes stripped | 0 missing | none | none | — |
| `CubeBoundaryThreeBricks.lean` | module docstring added (Engelking Thm 1.8.2); 27 `(Lemma 4.2)…(Lemma 4.6, C8)`, `Definition 4.1`, `(Definition 4.5, R9)` labels and one "receipt" removed | 0 missing | none | none: both binders already `Type r` | — |
| `CubeBoundaryThreeCells.lean` | module docstring rewritten (Engelking §1.8, Hurewicz–Wallman Ch. IV), `CD10C-I` section comment rewritten; 213 `Textbook L0/D1/C03/H2/F1/Q1/I1/Lemma 3.7(b), lines nnnn–nnnn (Dnnn):` prefixes stripped; no `Textbook`/`receipt` left | 0 missing | none | none | — |
| `CubeBoundaryThreeDimension.lean` | module docstring added (Engelking Thm 1.8.2, Hurewicz–Wallman Thm IV 1); 16 `Lemma 5.1(a)/(b)/(c)`, `Proposition 5.2/5.3` prefixes stripped | 0 missing | none | 4 widened: `FiniteBrickRefinement`, `finiteBrickRefinementOfScale`, `exists_finiteBrickRefinement`, `FiniteBrickRefinement.toCriterion` (`{ι : Type}` → `{ι : Type r}`) | the result type of `toCriterion` keeps `(κ : Type)`: forced by `HasCoveringDimensionLE Boundary`, whose refinement indices live in the universe of `Boundary` |
| `CubeBoundaryThreeLebesgue.lean` | module docstring rewritten (Munkres Lemma 27.5, Engelking Thm 1.8.2); both declaration docstrings re-cited; `Q-D/Q-L/Q-P/Q-I/Q-N/Q-S/Q-A` and `lines 1348--1366` labels removed | 0 missing | none | none: `{ι : Type v}` already polymorphic | — |
| `SphereTwo.lean` | module docstring added (Engelking 1.8.3/1.8.6, Hurewicz–Wallman Thm IV 1); "Corollary 6.2/6.3" and the "index-universe receipt" sentence removed | 0 missing | none | 0 of 1 | `{B : Type}` forced by `HasCoveringDimensionLE.of_homeomorph {X Y : Type u}` (same universe for both spaces; the sphere is in `Type 0`). Build error with `Type u`: `SphereTwo.lean:40:2: Type mismatch`. Widening needs a cross-universe transport lemma, i.e. a proof rewrite in `Covering.lean` |

### `Lib/Topology/Gluing/`, `Homotopy/`, `MappingTorus/`, `MetricSpace/`

| file | item 1 | item 2 | item 3 | item 4 | left / obstacle |
|---|---|---|---|---|---|
| `Gluing/OverBase.lean` | module docstring rewritten (gluing over a covered base; `Main definitions`; Mathlib `TopCat.GlueData`), the `fdab1700…` move-only sentence and the `CENTER_GENERIC_PATCH_HOMEOMORPH_TEXTBOOK.md` / `GP1–GP7` section comment removed | **62 new `/--` blocks: 40 declaration docstrings + 22 structure-field docstrings (corrected; the receipt said 21 fields)** — `ThreefoldGluing.Data` has 12 fields and `SpecialPeriods.Threefold.Star.Input` 10, all documented | none | none | the audit's rename `ThreefoldGluing`/`SpecialPeriods` → `GlueData.OverBase` was not done: it would remove and add declarations |
| `Homotopy/BasedDiskLifting.lean` | `Main results` and Hatcher §4.1 added; both `## Proof` sections moved from the docstrings into comments at the head of the proofs | 0 missing (both docstrings restated) | none | 0 of 2 | `{X Y : Type}` forced by `Hurewicz.homotopyMap {X Y : Type}` (`Lib/AlgebraicTopology/Hurewicz/Naturality.lean`, outside the packet), which occurs in the surjectivity hypothesis. Build error with `Type*`: `BasedDiskLifting.lean:61:66: Application type mismatch` |
| `Homotopy/ConvexContraction.lean` | module docstring rewritten with `Main definitions` and Hatcher §0 | both docstrings restated as statements | none | none: already `Type u` | — |
| `Homotopy/EquivariantCoveringLift.lean` | Hatcher Prop. 1.34 / §1.3 added to the module docstring and to `lift_eq_smul_of_eq_at` | 0 missing | none | none: already six universe variables | — |
| `Homotopy/PuncturedPlaneCyclic.lean` | module docstring rewritten (the theorem and the van Kampen proof; Hatcher Thm 1.7, Ex. 1.22, §1.2); the "range theorem … no paper-specific monodromy assertion" paragraph removed | 51 added | none | none | — |
| `Homotopy/QuotientCoveringSpace.lean` | module docstring rewritten (Hatcher Prop. 1.31 and 1.39); the "Core-A topology workstream" sentence removed | both docstrings expanded | none | none: already `Type u/v/w` | — |
| `MappingTorus/Wang.lean` | module docstring rewritten (chain-level Mayer–Vietoris input for the Wang sequence; Hatcher Example 2.48); the "Wang-family rows" topic list removed | 100 added (every public declaration; the one `private` helper left undocumented, as instructed) | none | 3 widened: `PassageHomology.radialCylinderHomeomorph`, `…_symm_fst`, `…_symm_snd_coe` (`(E : Type)` → `(E : Type*)`) | the other 58 `: Type` binders are forced by Type-pinned imported interfaces outside the packet: `SingularMayerVietoris.SingularHomology (Y : Type)` (`…/SingularHomology/MayerVietoris.lean`), the singular chain interface (`…/SingularHomology/Chains.lean`), `PassageHomology.cylinderPuncture {E : Type}`, `PassageHomology.twoPunctureSet {X : Type}` and `PassageHomology.puncturedVectorSpace` (`…/SingularHomology/LocalDegree.lean`). Widening all of them gives 40+ cascading elaboration errors, the first at `Wang.lean:79:43: Application type mismatch`; widening only the `PassageHomology` chart block still fails at `Wang.lean:311:44` |
| `MetricSpace/LebesgueNumber.lean` | module docstring moved out of `namespace Metric` to the head of the file and re-cited (Munkres Lemma 27.5, Mathlib `lebesgue_number_lemma_of_metric`); "canonical Corollary 2.1" replaced in both declaration docstrings; `L-01`…`L-06` labels removed | 0 missing | none | none: already `Type u/v` | the unused `hδ : 0 < δ` of `subset_cover_of_diam_lt_of_ball_cover` is kept: dropping it would change the statement |

### `Lib/Topology/Sheaves/`

| file | item 1 | item 2 | item 3 | item 4 | left / obstacle |
|---|---|---|---|---|---|
| `AddCommGrpPushforward.lean` | module docstring rewritten (Godement II.4, Hartshorne II.1/III.8); ownership sentence removed | 0 missing | **2 pins generalised**: `TopCat.{0}`/`AddCommGrpCat.{0}` → `TopCat.{v}`/`AddCommGrpCat.{v}` in `TopCat.Sheaf.pushforwardAdditive` | none | — |
| `Cohomology/AcyclicResolution.lean` | module docstring rewritten (Hartshorne III.1.2A, Godement II.4.7, Weibel 2.4.6) | 4 added (`Resolution`, `isAcyclicFor`, `globalComplexMap_id`, `globalComplexMap_comp`) | 0 of 5 | none | forced by `CategoryTheory.Sheaf.cohomologyAddCommGroup` (`Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean`, outside the packet), the only `AddCommGroup (Sheaf.H F n)` instance and itself pinned to `TopCat.{0}`/`AddCommGrpCat.{0}`/`Sheaf.H.{0}` |
| `Cohomology/AcyclicResolutionH1.lean` | module docstring rewritten (Hartshorne III.1.2A, Godement II.4.7, Weibel 2.4.6) | 2 added (`globalSectionsFunctor_additive`, `h0GlobalIso_naturality`) | **0 of 16 (corrected; the receipt said 15)** — 5 + 16 + 8 = 29 is what the header's "29 `.{0}` pins left" needs | none | same obstacle; measured build error with `.{u}`: `AcyclicResolutionH1.lean:53:4: failed to synthesize instance of type class AddCommGroup (Sheaf.H F 0)` |
| `Cohomology/AcyclicResolutionH1Naturality.lean` | bare title expanded into a statement with Hartshorne III.1.2A / Godement II.4.7 | 1 added (`extZeroGlobalIso_naturality`) | 0 of 8 | none | same obstacle |
| `Cohomology/Cech/CochainSheafResolution.lean` | `textbook section CD-05C, equations (C11)--(C14)` → Godement II.5.2 / Hartshorne III Lemma 4.2 | 21 added | none | none | — |
| `Cohomology/Cech/Coefficients.lean` | `textbook section CD-05` → Godement II.5.1–5.3 / Bredon III.4 | 2 added | none | none: all binders universe-polymorphic | — |
| `Cohomology/Cech/CohomologySystem.lean` | `textbook section CD-04` → Godement II.5.7 / Bredon III.4 | 3 added | none | none | — |
| `Cohomology/Cech/Colimit.lean` | `textbook section CD-04` → Godement II.5.8 / Bredon III.4; the "used by the covering-dimension argument" consumer sentence replaced by the filtered-colimit description | 0 missing | none | none | — |
| `Cohomology/Cech/ColimitCoefficients.lean` | `textbook section CD-05` → Godement II.5 / Bredon III.4 | 4 added | none | none | — |
| `Cohomology/Cech/ConnectingHom.lean` | `reviewed textbook section CD-05H`, `(C20)`, `(C21)`, `(C22)--(C23)` replaced by the mathematical statements and Godement II.5.9–5.10 / Bredon III.4 (7 places) | 7 added | none | none | the audit's split of the file at `boundaryClass` was not done: it would move declarations between modules |
| `Cohomology/Cech/CoveringDimensionVanishing.lean` | `CD-06`/`CD-07` → Godement II.5.12, Engelking §1.6 | 0 missing | none | none | — |
| `Cohomology/Cech/DegreeZero.lean` | `textbook section CD-05A, equations (C7)--(C8)` → Godement II.5.2 / Hartshorne III Lemma 4.1 | 4 added | none | none | — |
| `Cohomology/Cech/DirectedSystem.lean` | `textbook section CD-04` (module docstring and `instPreorder`) → Godement II.5.7 / Bredon III.4 | 1 added (`instNonempty`) | none | none | — |
| `Cohomology/Cech/FlasqueAcyclic.lean` | `textbook section CD-05D, equations (C9), (C15), (C16)` → Godement II.5.2.3 / Hartshorne III.2.5, III.4.2 | 0 missing | none | none | the index universe stays `ι : Type u`: decoupling it needs `AddCommGrpCat.{max u v}` products throughout the imported ordered-Čech interface, outside the packet |
| `Cohomology/Cech/LocalLifting.lean` | `textbook section CD-05G, equations (C18)--(C20)` → Godement II.5.10 / Bredon III.4 | 0 missing | none | none | — |
| `Cohomology/Cech/LocallyFiniteRefinement.lean` | `textbook section CD-05` → Munkres §41 and Mathlib `precise_refinement` | 0 missing | none | none | — |
| `Cohomology/Cech/LocallyZeroCochain.lean` | `textbook section CD-05F` → Godement II.5.10 / Bredon III.4; the three-paragraph proof narrative moved from the module docstring into a comment at the head of `exists_refinement_pullback_eq_zero_of_isLocallyZero_of_isZero_empty` | 0 missing | none | none | — |

## Build lines

Each file was built alone and green before its commit. Final builds at `acd98e17`:

```
lake build Lib                                 -> Build completed successfully (9150 jobs).   [exit 0]
lake build Solution S6Shortcuts S6 Challenge   -> Build completed successfully (9189 jobs).   [exit 0]
lake build Lib.AxiomAudit                      -> Build completed successfully (9150 jobs).   [exit 0]
```

`Lib.AxiomAudit` axiom sets (the complete set of distinct lines):

```
depends on axioms: [propext, Classical.choice, Quot.sound]
depends on axioms: [propext, Classical.choice]
depends on axioms: [propext, Quot.sound]
depends on axioms: [propext]
```

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

## Environment diff

`lean-agent-ide dump Lib --modules Lib` before (at `9552305f`) and after (at `acd98e17`),
compared with `tools/envdiff.py`:

```
constants before 21719 after 21719 (keys 21713 21713)
lost 56 added 56 of which source declarations: 0 0
names with changed type 56, of which source: 30
VERDICT PASS
```

**0 source declarations lost, 0 added.** All 56 lost/added constants are auxiliary
(`_proof_n`) constants of the declarations whose types changed.

### Changed types (30) and the generalisation that explains each

| # | name | explanation |
|---|---|---|
| 1 | `TopCat.Sheaf.pushforwardAdditive` | item 3: `TopCat.{0}`/`AddCommGrpCat.{0}` → `TopCat.{v}`/`AddCommGrpCat.{v}` |
| 2–3 | `TopCat.FiniteClosedPushforward.pushforward_exact`, `…pushforward_shortExact` | their statements contain the `PreservesZeroMorphisms` instance derived from `pushforwardAdditive` (both `use` it); it is now applied at an explicit level `.{0}` instead of being monomorphic. Statement unchanged |
| 4–11 | `CategoryTheory.Sheaf.Leray.higherDirectImageResolutionIso`, `…homologyPresheafPushforwardIso`, `…integralCoyonedaPushforwardHomologyIso`, `…integralCoyonedaPushforwardIso`, `…resolutionCohomologyIso_hom_apply`, `…resolutionCohomologyIso_inv_apply`, `…resolutionExtZeroIso_hom_apply`, `…resolutionExtZeroIso_inv_apply` | same cause: each `uses` `TopCat.Sheaf.pushforwardAdditive` in its type. Statements unchanged |
| 12–14 | `PassageHomology.radialCylinderHomeomorph`, `…_symm_fst`, `…_symm_snd_coe` | item 4: `(E : Type)` → `(E : Type*)` in `Wang.lean` |
| 15 | `PassageHomology.radialCylinderChart_symm_eq` | its statement mentions `radialCylinderHomeomorph`, now universe-polymorphic (applied at `.{0}`). Statement unchanged |
| 16 | `MorseCancellation.radialParameterChart_apply` | same: `uses` `radialCylinderHomeomorph` and `radialCylinderChart_symm_eq` in its type. Statement unchanged |
| 17–30 | `TopologicalSpace.CubeBoundaryThree.FiniteBrickRefinement` and its projections/constructor `.N`, `.h`, `.epsilon`, `.hN`, `.hh`, `.finiteIndex`, `.cover`, `.refinement`, `.multiplicity`, `.mk`, `.toCriterion`, plus `exists_finiteBrickRefinement` and `finiteBrickRefinementOfScale` | item 4: `{ι : Type}` → `{ι : Type r}` in `CubeBoundaryThreeDimension.lean` |

Every changed type is accounted for by a universe or binder generalisation of this
packet, or by an application of one of those generalised constants inside a statement
that is otherwise unchanged. Nothing is unexplained.

## Commits

`538f7987..acd98e17`, 32 commits, one per file, in this order:

```
538f7987 Lib/Topology/Sheaves/AddCommGrpPushforward.lean
812a4b02 Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1.lean
ec925b79 Lib/Topology/Sheaves/Cohomology/AcyclicResolution.lean
ae3a2ff3 Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1Naturality.lean
2b4fefd1 Lib/Topology/Sheaves/Cohomology/Cech/DirectedSystem.lean
e18cbba7 Lib/Topology/Sheaves/Cohomology/Cech/CohomologySystem.lean
877d38ee Lib/Topology/Sheaves/Cohomology/Cech/Coefficients.lean
eb9e3064 Lib/Topology/Sheaves/Cohomology/Cech/Colimit.lean
8e063069 Lib/Topology/Sheaves/Cohomology/Cech/ColimitCoefficients.lean
3f4df68f Lib/Topology/Sheaves/Cohomology/Cech/CoveringDimensionVanishing.lean
f858a46e Lib/Topology/Sheaves/Cohomology/Cech/FlasqueAcyclic.lean
75c8982f Lib/Topology/Sheaves/Cohomology/Cech/LocallyZeroCochain.lean
376d7c9c Lib/Topology/Sheaves/Cohomology/Cech/LocalLifting.lean
6b358207 Lib/Topology/Sheaves/Cohomology/Cech/LocallyFiniteRefinement.lean
22ae05e1 Lib/Topology/MetricSpace/LebesgueNumber.lean
c7fa5f82 Lib/Topology/Dimension/Covering.lean
215959b2 Lib/Topology/Dimension/SphereTwo.lean
9fbc579d Lib/Topology/Dimension/CubeBoundaryThree.lean
543600a9 Lib/Topology/Dimension/CubeBoundaryThreeLebesgue.lean
eb0e14b7 Lib/Topology/Dimension/CubeBoundaryThreeDimension.lean
790256cc Lib/Topology/Dimension/CubeBoundaryThreeBricks.lean
fe0b80ff Lib/Topology/Dimension/CubeBoundaryThreeCells.lean
9b8329b4 Lib/Topology/Homotopy/QuotientCoveringSpace.lean
86b2204a Lib/Topology/Homotopy/EquivariantCoveringLift.lean
6dd8d970 Lib/Topology/Homotopy/ConvexContraction.lean
4656025f Lib/Topology/Homotopy/BasedDiskLifting.lean
f0f79db6 Lib/Topology/Sheaves/Cohomology/Cech/DegreeZero.lean
480b2350 Lib/Topology/Sheaves/Cohomology/Cech/CochainSheafResolution.lean
c55c8e0e Lib/Topology/Sheaves/Cohomology/Cech/ConnectingHom.lean
277ea6a7 Lib/Topology/Gluing/OverBase.lean
66440d10 Lib/Topology/Homotopy/PuncturedPlaneCyclic.lean
acd98e17 Lib/Topology/MappingTorus/Wang.lean
```

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-07.md` (ACCEPT WITH FINDINGS; the work is
sound — no deletion, rename, hypothesis change, `sorry` or `axiom`; the one universe lift keeps the
`u = 0` statement literally, re-elaborated by the reviewer; the 30 changed types are all
attributable to this packet).  These corrections are to this receipt's text only; no Lean file was
changed by them.

1. **Header counts (findings 4, 5, 6), all corrected in place.**
   * `: Type` binders: "58 + 1 left" → **62 left**.  Counting `: Type)` / `: Type}` at the branch
     tip: `MappingTorus/Wang.lean` 58, `Dimension/SphereTwo.lean` 1,
     `Hurewicz/BasedDiskLifting.lean` 2 (the row says "0 of 2") and
     `Dimension/CubeBoundaryThreeDimension.lean` 1 (the `(κ : Type)` in the result type of
     `FiniteBrickRefinement.toCriterion`).  The "7 widened" figure is right (Wang 61 → 58,
     CubeBoundaryThreeDimension 5 → 1).
   * `Cohomology/AcyclicResolutionH1.lean`: "0 of 15" → **0 of 16** (the packet list also said ×16);
     5 + 16 + 8 = 29 is what the header's "29 pins left" needs.
   * `Gluing/OverBase.lean`: "40 added + 21 structure fields" → **62 new `/--` blocks = 40
     declaration docstrings + 22 field docstrings** (`ThreefoldGluing.Data` 12 fields,
     `SpecialPeriods.Threefold.Star.Input` 10).  The 245 total is unaffected, since it excludes
     fields.

   All three are the kind of slip a script that sums the per-file table would have prevented; that
   is now the rule (`Lib/reviews/REVIEW-7-8.md` §4).

2. **The manuscript-label sweep was not complete (finding 1).**  This receipt's item-1 column for
   `Cech/CochainSheafResolution.lean` ("(C11)–(C14)") and `Cech/DegreeZero.lean` ("(C7)–(C8)") reads
   as if the sweep were finished.  It removed only the **module-docstring** labels (commits
   `480b2350`, `f0f79db6`); three declaration docstrings still carry one, at the branch tip and at
   head `39f1d12b`:
   * `Lib/Topology/Sheaves/Cohomology/Cech/CochainSheafResolution.lean:1009` — "This is equation
     (C13), transported through the canonical comparison";
   * `…/CochainSheafResolution.lean:1042` — "This is the normalized form of equation (C14).";
   * `…/Cech/DegreeZero.lean:699` — "This is equation (C8), valid without separation or
     paracompactness hypotheses."

   `(C8)`, `(C13)` and `(C14)` refer to nothing in `Lib`.  In addition
   `Lib/Topology/Dimension/CubeBoundaryThreeDimension.lean:261` still says "assemble the previously
   proved **receipts**" (manuscript jargon).  The four are on the fix list
   (`Lib/reviews/REVIEW-7-8.md` §3, packet 07).  A grep for `\(C[0-9]+\)`, `CD-`, `Textbook`,
   `receipt` over the packet's files after the last commit would have caught them.

3. **No per-packet `envdiff.json`/`.txt` is in the repository (finding 7).**  The environment-diff
   section above quotes a tool run ("lost 56 added 56 … changed type 56, of which source: 30,
   VERDICT PASS") that cannot be re-inspected: `Lib/reports/round-7/packets/` holds only the ten
   receipts and ten packet lists, and the only round-7 artefact is the merged
   `envdiff-merged-d950428a.{json,txt}`, which mixes all ten packets.  The reviewer could check the
   30 named constants against the merged file (all present under `changed_type_proof_naming`, none
   lost or added at source level), which is weaker than checking this packet's own run; the
   sentence "lost 56 / added 56 are all `_proof_n`" is **unverifiable from the tree**.  Committing
   the JSON/TXT beside the receipt is the standing rule from round 8 on.

4. **Citation and docstring findings are code fixes, not receipt fixes.**  Hatcher "Example 1.22" in
   `Topology/Homotopy/PuncturedPlaneCyclic.lean:30` (the deformation retraction of `ℂ ∖ {0}` onto
   `S¹` is Chapter 0 material; Ex. 1.22 is a van Kampen example), Weibel "Theorem 2.4.6" in
   `AcyclicResolution.lean:24` and `AcyclicResolutionH1.lean:28` (the acyclic-resolution statement is
   Exercise 2.4.3; Hartshorne III.1.2A, cited alongside, is correct) and the "*exactly* acyclicity"
   wording of `AcyclicResolution.lean:56` are on the `Lib/reviews/REVIEW-7-8.md` §3 list.  Both
   doubtful citations were copied from the audit's twin column in `packet-07.md` rather than checked;
   the round-8 rule is that such citations are marked "cf." unless verified against the book.
