# Round 8, seat `dup-hom` — internal duplicates (AUDIT.md finding 5)

Packet: `Lib/reports/round-7/judgement/duplicates.md`, items 1, 2, 3, 4, 5, 6, 10, 11.
Worktree `/home/goblin/hopf-r8-dup-hom`, branch `r8/dup-hom`, base `4e15a034`.
Items 7, 8, 9 and every file under `Lib/Topology/Sheaves` belong to another seat and were not
touched.

## 1. Per item

### Item 1 — van Kampen monolith vs the `VanKampen/` split — DONE (`ba7f0b36`)

`Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` (1823 lines, 167 source declarations)
and `VanKampen/{Basic,PathValue,Pushout,Surjectivity}.lean` were two complete copies of the
Seifert–van Kampen development, the first under `FundamentalGroup.VanKampen.`, the second under
`FundamentalGroup.VanKampen.Cocone.`.  149 declaration names agreed modulo the `Cocone.`
segment.

Survivor: the split.  It is the Mathlib-PR copy (#28246, S. Kumar, credited in the file
headers), it is the copy `Lib/AxiomAudit.lean` probes (431 `#check`/`#print axioms` lines; the
monolith was probed nowhere), and it is module-system code.

Ported before deletion:

* the uniqueness half of Hatcher Thm 1.20, which the split had only implicitly as
  `pushoutEquiv.symm` — 16 declarations, into `VanKampen/Pushout.lean`
  (`pushoutOfU`, `pushoutOfV`, `pushoutBase`, `pushoutOfU_comp_overlapHomU`,
  `pushoutOfV_comp_overlapHomV`, `pushoutOf_compatible`, `pushoutToFundamentalGroup`,
  `pushoutToFundamentalGroup_of`, `pushoutToFundamentalGroup_comp_of`,
  `pushoutToFundamentalGroup_comp_ofU`, `pushoutToFundamentalGroup_comp_ofV`,
  `fundamentalGroupToPushout`, `fundamentalGroupToPushout_comp_inclusionU`,
  `fundamentalGroupToPushout_comp_inclusionV`,
  `fundamentalGroupToPushout_comp_pushoutToFundamentalGroup`,
  `pushoutToFundamentalGroup_comp_fundamentalGroupToPushout`).
  Each statement was checked character-for-character against the monolith modulo the inserted
  `Cocone.` segment: 16 of 16 identical.
* `SphereHomology.twoOpenCover_fundamentalGroup_eq_one`, as
  `FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroup_eq_one` in
  `VanKampen/Surjectivity.lean` (same statement, verified the same way).
* docstrings onto the eight previously undocumented declarations of `VanKampen/Pushout.lean`.

`SphereHomology.twoOpenCover_pathConnectedSpace` already had the twin
`FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pathConnectedSpace` in `Surjectivity.lean`;
nothing to port.

Rerouted: 21 modules now import `VanKampen.Surjectivity` instead of the monolith (`Lib.lean`
already listed every split module, so its monolith import was simply dropped); the three files
that named monolith declarations —
`Lib/AlgebraicTopology/SingularHomology/SuspensionCover.lean`, `Hopf/Proof/Hurewicz.lean`,
`Hopf/Proof/LCP/BoundaryTopology.lean` — now name the `Cocone.` declarations.

### Item 2 — `SingularHomology/Chains.lean` vs `SimplexPaths`/`CycleClasses`/`Degree1` — LEFT

Real and large.  `SingularChains.*` (`Chains.lean`, 153 declarations, plus 87 more in
`PathClass.lean`, `FirstHurewicz.lean`, `HomotopyExtension.lean`,
`CubeChainDecomposition.lean`) duplicates `AlgebraicTopology.Hurewicz.*` (the three Mathlib-PR
reference copies) name for name: 35 pairs against `SimplexPaths.lean`, 63 against
`Degree1.lean`, 4 renames (`inducedHomology*` vs `SingularH1.map*`), 56 more in the satellites,
12 renames of the Hurewicz theorem itself (`hurewiczMap` vs `hurewiczHom`, …).

Not attempted here: `Chains.lean` has 57 importers and ~3200 name references, the PR files
carry a "kept verbatim" contract that forbids editing them, and the `ChainHomology` halves are
*not* the same statement (fixed `ℤ`/`LinearMap`/explicit quotient `Opchains` against general
`R`/`ModuleCat` morphisms/abstract `opcycles`), so 20 of the pairs need re-proving rather than
aliasing.  This does not fit the remaining budget of this seat and is left as a whole so that it
is done in one piece.  The concrete five-step plan (alias the simplex/path half, then the
singular half, re-prove the `ChainHomology` façade, then `PathClass`/`FirstHurewicz`, then port
the finsupp/basis layer upstream) is in the round-7 judgement material and was re-derived in
full during this seat.

### Item 3 — barycentric subdivision / mesh — LEFT

Real and large.  `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` l.1115–2635
(124 declarations, namespace `SingularMayerVietoris`) duplicates
`Lib/AlgebraicTopology/SingularSmallChains/Barycentric/*` (18 modules) almost verbatim; the
Barycentric side is the survivor (A-grade, arbitrary cover, universe-polymorphic, fully
axiom-audited, and it additionally proves a `HomotopyEquiv`, not only a `QuasiIso`).

Not attempted here: the two copies are typed on *different* chain complexes
(`SingularChains.Chains X n` against `TopCat.SingularSmallChains.Barycentric.Chains X n`) and on
different `Simplex` towers, so the deletion needs the same `SingularChains`↔Mathlib-PR bridge
that item 2 needs; five of the statements (`realizedChain_mem_small`,
`eventually_subdivision_mem_small`, …) are two-set specialisations that must be re-derived at
`I := Bool` from the arbitrary-cover forms; and the consumers are
`CrossProduct.lean` (944 references), `CubeChainDecomposition.lean` (124),
`PrismOperator.lean` (20), `CubeTriangulation.lean` (2).  Items 2 and 3 should be done together.

Sub-claim checked and refuted: `Coproduct.homologyBiproductEquiv` is *not* duplicated under
`SingularSmallChains/Barycentric/*`.  The only near-twin is the binary
`SingularMayerVietoris.homologyBiprodEquiv` (`MayerVietoris.lean:768`), which is a different
statement (`K ⊞ L`, universe `u`) from the finite `Coproduct.homologyBiproductEquiv`
(`⨁ K`, `[Fintype ι]`, universe `0`); both are kept, for the reason given under item 5.

### Item 4 — Mayer–Vietoris naturality proved twice — DONE (`a3c8ce9c`)

`Naturality.lean` proved naturality of the connecting homomorphism twice with the same
hypotheses, once under `CoverNaturality.` and once under `SingularMayerVietoris.`.  Survivor:
`SingularMayerVietoris.` — it is the development the module docstring announces, it has 23
external uses against 9, and it alone states the general forms
`connectingHomomorphism_naturality_of_sequenceMap` (naturality along an arbitrary chain-sequence
map) and `smallHomologyComparison_naturality_of_comm` (an arbitrary chain map with a commutation
hypothesis).  13 declarations deleted, twins in table B below; two of those twins
(`smallConnecting_naturality`, `comparison_naturality`) are the more general statements, so the
deleted declarations are instances of them.

Kept, with reasons: `CoverNaturality.chainMap_comp` and `map_intersection` (no twin); the
cover-order swap block (`intersectionSwap` … `connecting_swap`: swapping `U` and `V` negates
`δ` — genuinely different content); the crossed form (`reversingIntersectionMap`,
`connecting_reversing_naturality`: hypotheses `MapsTo f U V'`, `MapsTo f V U'`); and the
chart-transported form (`overlapCoordinateMap`, `normalized_connecting_naturality`: extra
parameters `S T` with homotopy equivalences).  These now sit after the `SingularMayerVietoris`
block, since they call into it.

Rerouted: `OnePointCover.lean`, `LocalContributionsNaturality.lean`,
`Geometry/Manifold/Morse/SurgeryCollapse.lean` — 9 call sites.

### Item 5 — Hatcher Prop 2.6 binary vs finite — KEPT BOTH (`a3c05a72`)

The proposition is proved twice but **no declaration is duplicated**: the two towers share no
statement.  `SingularHomology.sumHomologyEquiv : H_n(X ⊕ Y) ≃ₗ[ℤ] H_n X × H_n Y` and
`Coproduct.sigmaHomologyEquiv : H_n(Σ i, X i) ≃ₗ[ℤ] ∀ i, H_n (X i)` differ in domain, codomain
and hypotheses (`[Fintype ι]` exists only on the Coproduct side); neither is a Lean instance of
the other without a transport along `X ⊕ Y ≃ₜ Σ b : Bool, …` that does not exist in the tree;
and each carries API the other lacks (the `sumElim`/fold calculus, 9 consumer files; the
`Pi.single` decomposition, 3 consumer files).  Both kept; the two module docstrings now say so
and point at each other so the next audit pass does not re-flag them.  No declaration added,
removed or changed by that commit.

### Item 6 — `InjectiveResolutionHomology` vs `InjectiveResolutionCoyoneda` — KEPT BOTH; the `shortCycleClass` triple — DONE (`60b9593e`)

**Kept both Ext files.**  They are not the same theorem twice in the sense the packet assumes.
`InjectiveResolution.positiveHomologyExtIso` is about the ℕ-graded literal complex
`Hom(A, R•)` in strictly positive degrees, lands in `AddCommGrpCat` (so it composes
categorically) and comes with a naturality statement on `Cᵒᵖ` plus an explicit cocycle calculus;
`InjectiveResolution.coyonedaHomologyExtAddEquiv` is about the ℤ-graded
`CochainComplex.HomComplex.coyonedaComplex`, covers degree 0, is a bare `AddEquiv` with no
naturality, and is universe-free in `HasExt.{w}`.  Deriving one from the other needs an
`extend ComplexShape.embeddingUpNat` comparison that exists nowhere in the tree; that is new
mathematics, not de-duplication.

**Done: the cocycle-class helpers.**  The elementwise description of
`ShortComplex.abHomologyIso` existed twice with character-for-character identical statements and
proofs — publicly in `Ext/InjectiveResolutionHomology.lean` and as `private` helpers in
`HomologicalComplex/CycleLift.lean`.  New module
`Lib/Algebra/Homology/ShortComplex/AbCycleClass.lean` holds the union once in namespace
`CategoryTheory.ShortComplex`; both former owners import it.  Five private declarations deleted,
twins in table C.

Not done, recorded: the parallel `ModuleCat ℤ` pair
(`CategoryTheory.HomologicalComplex.ChainCycleLift.shortCycleClass*` against
`SingularChains.ChainHomology.shortCycleClass*`) is the same duplication one level down.  It is
left because `SingularChains.ChainHomology` is item 2's territory and both should move together.

### Item 10 — mesh files and the degree-one cochain lemmas — MOSTLY KEPT; one sub-item DONE (`ecf64466`)

**Mesh files: kept, premise refuted.**  `ArbitraryCoverMesh.lean` does not supersede
`MeshLebesgue`/`MeshAffine`/`MeshSubdivision`; it *imports* them
(`MeshLebesgue → MeshAffine → MeshSubdivision → ArbitraryCoverMesh`) and consumes `meshFactor`,
`eventually_meshFactor_pow_mul_lt` and `simplex_formalSubdivision_iterate_diam` from them.  No
module here can be deleted.  What is parallel is the two-set tail of each file, but those are
*not* the same statement as the arbitrary-cover forms: the conclusion is `… ⊆ U ∨ … ⊆ V` against
`∃ i, … ⊆ U i`, and the arbitrary-cover form carries an extra `[Nonempty K]`.  A statement may
only be deleted when a surviving twin with the *same* statement exists, so these stay.  (They
are dead code — no consumer outside the four mesh files — and deriving the two-set forms as
corollaries inside `ArbitraryCoverMesh.lean` is the right follow-up, but that is a rewrite, not
a de-duplication, and it must be coordinated with item 3, which owns a fourth copy of the whole
mesh stack at `MayerVietoris.lean:2283–2631`.)

"The three two-set-cover files" of the packet are these same three files, not a fourth group.

**`SingularSmallChains/Basic.lean` degree-one lemmas: blocked.**  `homotopy_on_cocycle_one`,
`smallCochain_cocycle_lift_exact_one`, `smallCochain_boundary_of_restriction_boundary_one` and
`cochainRestriction_homologyMap_isIso_one` are the `n := 0` / `n := 1` instances of the general
lemmas in `CochainHomotopy.lean`.  They cannot be removed from this seat: `CochainHomotopy.lean`
imports `Basic.lean`, so the `_one` lemmas cannot be restated in terms of the `_succ` ones
without moving them into `CochainHomotopy.lean`, and the two live consumers of the middle two
are `Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1Criterion.lean:92,135`, which belongs
to another seat.  Handed over.

**Done: the third copy of `homotopy_on_cocycle_succ`.**  Found while checking the above:
`TopCat.SingularSmallChains.homotopy_on_cocycle_succ` (`CochainHomotopy.lean:40`) and
`AlgebraicTopology.SingularCochains.homotopy_on_cocycle_succ` (`PositivePrimitives.lean:123`)
had character-for-character identical statements in import-incomparable modules.  Neither module
is the statement's subject — it is about `Homotopy`.  New module
`Lib/Algebra/Homology/Homotopy/CocycleEvaluation.lean` states it once as
`CochainComplex.homotopy_on_cocycle_succ`; both former owners import it;
`Lib/AxiomAudit.lean` probes it once instead of twice.

### Item 11 — `AcyclicResolutionH1` vs `TwoStepResolution`; the `PostnikovD2*` cluster — KEPT BOTH

**The two structures are not the same statement.**  `TwoStepResolution` is `AcyclicResolutionH1`
plus a field `epi_g : Epi complex.g`, and that field is load-bearing in both directions: it is
what makes `second_shortExact`/`connectingTwo` (hence the whole transgression tower) available,
and the main `AcyclicResolutionH1` constructors would *fail* it — `AcyclicResolution.trunc n`
(`Ext/AcyclicResolution.lean:221`) has `.g` a differential `Kⁿ⁺¹ ⟶ Kⁿ⁺²` of a longer
resolution, likewise `AcyclicResolutionH2.tail` and `kernelTrunc`.  So neither structure may
gain or lose that field.  The two `Hom` structures are also not field-identical (the packet's
"field-for-field" is wrong): `AcyclicResolutionH1.Hom` bundles a `ShortComplex` hom, and
`TwoStepResolution.Hom` carries `τ₁`/`τ₂`/`τ₃` unbundled with `cat_disch` autoparams.

Six `TwoStepResolution` declarations (`boundary`, `toBoundary`, `toBoundary_ι`, `ι_toBoundary`,
`first`, `first_shortExact`) *are* re-proofs of `AcyclicResolutionH1` declarations, and
`first_shortExact` is verbatim identical for 13 lines.  Collapsing them needs
`structure TwoStepResolution extends AcyclicResolutionH1 where epi_g : …`, which rewrites four
constructor sites and — for the `Hom` half — five `Lib/Topology/Sheaves` files belonging to
another seat.  Left for a seat that owns both directories.

**The `PostnikovD2*` cluster is not a duplicate at all.**  `Ext/PostnikovD2*` *imports*
`SpectralObject/PostnikovD2.lean` (`PostnikovD2PageSplice.lean:12`) and applies the general-`(p,q)`
lemma at `p = 0`.  The `p = 0` restriction is not sloppiness: `coyonedaPostnikovD₂SourceHom`
uses `(singleFunctor C 0).preimage`, which is available only in column 0, where
`E₂^{0,q+1} = Hom(P, H^{q+1}K) = Ext⁰`.  No declaration to delete.

## 2. Rename map

`Lib/reports/round-8/dup-hom/rename.txt` (also `$S/rename.txt`).  One genuine rename of a
surviving declaration:

| old | new |
|---|---|
| `TopCat.SingularSmallChains.homotopy_on_cocycle_succ` | `CochainComplex.homotopy_on_cocycle_succ` |

The map also lists the 17 declarations hand-ported out of the deleted van Kampen monolith into
the `Cocone.` namespace (16 pushout declarations and
`SphereHomology.twoOpenCover_fundamentalGroup_eq_one`), so that the correspondence is machine
readable.

Note on the tool: `lean-agent-ide dump --rename` maps `old ↦ new` over the environment it is
dumping, so a map written `old new` only has an effect when applied to the environment that
still contains the *old* spellings — the base.  Applied to the after dump, as the round-8 rules
prescribe, it is a no-op, and the renamed declarations therefore appear in the envdiff as one
lost and one added name rather than as a bijection.  They are listed in table D below instead.
As a substitute check, the 17 ported statements were compared character-for-character with the
monolith text modulo the inserted `Cocone.` segment: 17 of 17 identical (script output
`mismatches: 0 of 16` plus the `fundamentalGroup_eq_one` pair printed in full).

## 3. Envdiff

```
constants before 38593 after 38295 (keys 38491 38193)
lost 335 added 37 of which source declarations: 219 32 ; names with changed type 12 of which source: 11
auxiliary lost/added/changed (not judged): 116 5 1
module moves (source declarations, 1-to-1):
       3  Lib.Algebra.Homology.DerivedCategory.Ext.InjectiveResolutionHomology -> Lib.Algebra.Homology.ShortComplex.AbCycleClass
ambiguous module changes: 0
auxiliary constants that changed module: 3
VERDICT FAIL
```

`FAIL` is the expected verdict for a de-duplication pass: the tool fails whenever a source key is
lost.  Receipt copy: `Lib/reports/round-8/dup-hom/envdiff.json`.

**Lost source names: 263 by the name filter used below (219 by the tool's stricter
source/auxiliary split; the difference is auto-generated `congr_simp`/projection companions of
deleted definitions, which carry declaration ranges).  Every one is a deleted duplicate with a
surviving twin, or one of the 11 names whose type changed; the tables are exhaustive.**

The module move is the `ShortComplex` block of item 6 moving to its own file; the 3 auxiliary
module changes are its `_proof_` companions.

**Added source names (32):** the 16 ported pushout declarations plus
`TwoOpenCover.pushoutToFundamentalGroup_of` and `TwoOpenCover.fundamentalGroup_eq_one` under
`FundamentalGroup.VanKampen.Cocone.` (item 1); the three helpers promoted from `private` in
`CycleLift.lean` to `CategoryTheory.ShortComplex.shortCycleClass_{surjective,quotient,eq_zero_iff}`
(item 6); `CochainComplex.homotopy_on_cocycle_succ` (item 10); and the 11 names below, which
appear as both lost and added because their type changed.

**Names with changed type (11).**  All eleven are the single substitution
`FundamentalGroup.VanKampen.TwoOpenCover` ⇝ `FundamentalGroup.VanKampen.Cocone.TwoOpenCover`
in the statement, forced by deleting one of two field-for-field identical structures.  The full
diff of every non-import line in `Hopf/` and `SuspensionCover.lean` between the base and `HEAD`
is exactly that substitution plus two call-site rewrites of the ported corollaries, so no
hypothesis was added and no statement weakened:

```
SpecialPeriods.Threefold.attachmentCover
SpecialPeriods.Threefold.attachmentLeftGroupEquiv
SpecialPeriods.Threefold.attachmentLeftGroupEquiv_inclusion
SpecialPeriods.Threefold.attachmentLeftHomeomorph
SpecialPeriods.Threefold.attachmentOverlapGroupEquiv
SpecialPeriods.Threefold.attachmentOverlapHomeomorph
SpecialPeriods.Threefold.attachmentRightGroupEquiv
SpecialPeriods.Threefold.attachmentRightGroupEquiv_overlap
SpecialPeriods.Threefold.attachmentRightHomeomorph
SphereHomology.suspensionConeCover
SphereHomology.twoOpenCover_simplyConnectedSpace
```

## 4. Lost-name table (deleted copy -> surviving twin)

### A. `FundamentalGroup.VanKampen.*` -> `FundamentalGroup.VanKampen.Cocone.*` (item 1, 228 names)

Every one of these is `FundamentalGroup.VanKampen.<suffix>` deleted with the monolith, twin
`FundamentalGroup.VanKampen.Cocone.<suffix>` in the split.  Suffixes, in full:

```
LocalPathValue
LocalPathValue.HomotopyInvariant
LocalPathValue.IsPrimitive
LocalPathValue.IsPrimitiveUpTo
LocalPathValue._sizeOf_1
LocalPathValue._sizeOf_inst
LocalPathValue.casesOn
LocalPathValue.compatible
LocalPathValue.ctorIdx
LocalPathValue.exists_primitive
LocalPathValue.exists_primitiveUpTo_step
LocalPathValue.extension
LocalPathValue.extension_extends
LocalPathValue.isPrimitiveUpTo_zero
LocalPathValue.isPrimitive_subpath
LocalPathValue.mk
LocalPathValue.mk._flat_ctor
LocalPathValue.mk.inj
LocalPathValue.mk.injEq
LocalPathValue.mk.noConfusion
LocalPathValue.mk.sizeOf_spec
LocalPathValue.noConfusion
LocalPathValue.noConfusionType
LocalPathValue.primitive_unique
LocalPathValue.rawValue
LocalPathValue.rawValue_cast
LocalPathValue.rawValue_local
LocalPathValue.rawValue_refl
LocalPathValue.rawValue_subpath
LocalPathValue.rawValue_subpath_mul
LocalPathValue.rawValue_subpath_zero_one
LocalPathValue.rawValue_trans
LocalPathValue.rec
LocalPathValue.recOn
LocalPathValue.refl
LocalPathValue.subpath_mul
LocalPathValue.trans
LocalPathValue.transport
LocalPathValue.transport.congr_simp
LocalPathValue.transport_isPrimitive
LocalPathValue.transport_subpath
LocalPathValue.transport_zero
LocalPathValue.value
LocalPathValue.value.congr_simp
LocalPathValue.value_cast
LocalPathValue.value_eq_of_path_eq
PathValue
PathValue.Extends
PathValue.HomotopyInvariant
PathValue._sizeOf_1
PathValue._sizeOf_inst
PathValue.casesOn
PathValue.ctorIdx
PathValue.fundamentalGroupHom
PathValue.homotopyInvariant_of_open_cover
PathValue.mk
PathValue.mk._flat_ctor
PathValue.mk.inj
PathValue.mk.injEq
PathValue.mk.noConfusion
PathValue.mk.sizeOf_spec
PathValue.noConfusion
PathValue.noConfusionType
PathValue.rec
PathValue.recOn
PathValue.refl
PathValue.square_cell_of_local
PathValue.square_strip
PathValue.subpath_mul
PathValue.trans
PathValue.value
PathValue.value_cast
PathValue.value_eq_of_homotopy_of_open_cover
PathValue.value_eq_one_of_constant
PathValue.value_squareHorizontal_homotopy
PathValue.value_squareVertical_homotopy_one
PathValue.value_squareVertical_homotopy_zero
PathValue.value_subpath_zero_one
TwoOpenCover
TwoOpenCover.ChartGroup
TwoOpenCover.Compatible
TwoOpenCover.OverlapGroup
TwoOpenCover.Pushout
TwoOpenCover.U
TwoOpenCover.UGroup
TwoOpenCover.V
TwoOpenCover.VGroup
TwoOpenCover._sizeOf_1
TwoOpenCover._sizeOf_inst
TwoOpenCover.base
TwoOpenCover.baseChart
TwoOpenCover.baseOverlapPoint
TwoOpenCover.baseU
TwoOpenCover.baseUPoint
TwoOpenCover.baseV
TwoOpenCover.baseVPoint
TwoOpenCover.base_mem_chart
TwoOpenCover.casesOn
TwoOpenCover.chart
TwoOpenCover.chartHom
TwoOpenCover.chartPath
TwoOpenCover.chartPathClass
TwoOpenCover.chartPathClass_base
TwoOpenCover.chartPath_base
TwoOpenCover.chart_cover
TwoOpenCover.chart_open
TwoOpenCover.closePath
TwoOpenCover.closePath_homotopic
TwoOpenCover.closePath_loop
TwoOpenCover.closePath_refl
TwoOpenCover.closePath_trans
TwoOpenCover.cover
TwoOpenCover.ctorIdx
TwoOpenCover.fundamentalGroupToPushout
TwoOpenCover.fundamentalGroupToPushout_comp_inclusionU
TwoOpenCover.fundamentalGroupToPushout_comp_inclusionV
TwoOpenCover.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup
TwoOpenCover.globalPathValue
TwoOpenCover.globalPathValue_extends
TwoOpenCover.globalPathValue_homotopyInvariant
TwoOpenCover.hom_ext
TwoOpenCover.inclusionHom
TwoOpenCover.inclusionHomU
TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
TwoOpenCover.inclusionHomV
TwoOpenCover.inclusionHom_comp_overlapHom
TwoOpenCover.inclusionHom_compatible
TwoOpenCover.inclusionU
TwoOpenCover.inclusionV
TwoOpenCover.lift
TwoOpenCover.lift_comp_inclusionU
TwoOpenCover.lift_comp_inclusionV
TwoOpenCover.lift_mk_of_mem
TwoOpenCover.localPathValue
TwoOpenCover.localPathValue_homotopyInvariant
TwoOpenCover.localValue
TwoOpenCover.localValue_compatible
TwoOpenCover.localValue_compatible_UV
TwoOpenCover.localValue_homotopy
TwoOpenCover.localValue_map_loop
TwoOpenCover.localValue_refl
TwoOpenCover.localValue_subpath_mul
TwoOpenCover.localValue_trans
TwoOpenCover.mem_U_or_V
TwoOpenCover.mk
TwoOpenCover.mk._flat_ctor
TwoOpenCover.mk.inj
TwoOpenCover.mk.injEq
TwoOpenCover.mk.noConfusion
TwoOpenCover.mk.sizeOf_spec
TwoOpenCover.noConfusion
TwoOpenCover.noConfusionType
TwoOpenCover.overlap
TwoOpenCover.overlapClose
TwoOpenCover.overlapHom
TwoOpenCover.overlapHomU
TwoOpenCover.overlapHomU_close
TwoOpenCover.overlapHomV
TwoOpenCover.overlapHomV_close
TwoOpenCover.overlapPath
TwoOpenCover.overlapPath_map_U
TwoOpenCover.overlapPath_map_V
TwoOpenCover.overlapToU
TwoOpenCover.overlapToV
TwoOpenCover.pathConnectedIntersection
TwoOpenCover.pathConnectedU
TwoOpenCover.pathConnectedV
TwoOpenCover.pathTo
TwoOpenCover.pathTo_base
TwoOpenCover.pathTo_mem
TwoOpenCover.pushoutBase
TwoOpenCover.pushoutEquiv
TwoOpenCover.pushoutEquiv_of
TwoOpenCover.pushoutOfU
TwoOpenCover.pushoutOfU_comp_overlapHomU
TwoOpenCover.pushoutOfV
TwoOpenCover.pushoutOfV_comp_overlapHomV
TwoOpenCover.pushoutOf_compatible
TwoOpenCover.pushoutToFundamentalGroup
TwoOpenCover.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout
TwoOpenCover.pushoutToFundamentalGroup_comp_of
TwoOpenCover.pushoutToFundamentalGroup_comp_ofU
TwoOpenCover.pushoutToFundamentalGroup_comp_ofV
TwoOpenCover.pushoutToFundamentalGroup_of
TwoOpenCover.rawPathTo
TwoOpenCover.rawPathTo_mem
TwoOpenCover.rec
TwoOpenCover.recOn
convexComb_comp
convexComb_mem_Icc
convexComb_monotone
exists_path_subdivision
homotopyIn
homotopy_subpathTransSubpathRefl_mem
homotopy_subpathTransSubpath_mem
homotopy_transRefl_mem
homotopy_trans_mem
intervalHalf
mem_Icc_of_subpath_mem
mem_of_subpath_mem
pathIn
pathIn.congr_simp
pathIn_apply
pathIn_map
pathIn_refl
pathIn_trans
rectangleBoundaryHomotopy
rectangleBoundaryHomotopy_apply
rectangleBoundaryHomotopy_mem
rectangleHorizontalVertical
rectangleHorizontalVertical_map
rectangleHorizontalVertical_mem
rectangleVerticalHorizontal
rectangleVerticalHorizontal_map
rectangleVerticalHorizontal_mem
squareHorizontal
squarePathHomotopy
squarePathHomotopy_mem_rectangle
squareVertical
subpathTransSubpathIn
subpath_mem_mono
subpath_mem_of_mem_Icc
subpath_subpath
trans_apply_intervalHalf
trans_convexComb_first_half
trans_convexComb_second_half
trans_subpath_first_half
trans_subpath_second_half
```

### B. `CoverNaturality.*` -> `SingularMayerVietoris.*` (item 4, 15 names)

| deleted | surviving twin |
|---|---|
| `CoverNaturality.chainSequenceMap` | `SingularMayerVietoris.chainSequenceMapOfMapsTo` |
| `CoverNaturality.comparison_naturality` | `SingularMayerVietoris.smallHomologyComparison_naturality_of_comm` |
| `CoverNaturality.connecting_naturality` | `SingularMayerVietoris.connectingHomomorphism_naturality` |
| `CoverNaturality.connecting_naturality_apply` | `SingularMayerVietoris.connectingHomomorphism_naturality_apply` |
| `CoverNaturality.inducedChain_mem_small` | `SingularMayerVietoris.inducedChain_mem_small_of_mapsTo` |
| `CoverNaturality.intersection_left` | `SingularMayerVietoris.coverRestriction_intersection_left` |
| `CoverNaturality.intersection_right` | `SingularMayerVietoris.coverRestriction_intersection_right` |
| `CoverNaturality.mapOn` | `SingularMayerVietoris.coverRestriction` |
| `CoverNaturality.smallConnecting_naturality` | `SingularMayerVietoris.connectingHomomorphism_naturality_of_sequenceMap` |
| `CoverNaturality.smallMap` | `SingularMayerVietoris.smallMapOfMapsTo` |
| `CoverNaturality.smallMap_inclusion` | `SingularMayerVietoris.smallMapOfMapsTo_inclusion` |
| `CoverNaturality.smallMap_left` | `SingularMayerVietoris.toSmallLeft_smallMapOfMapsTo` |
| `CoverNaturality.smallMap_right` | `SingularMayerVietoris.toSmallRight_smallMapOfMapsTo` |
| `CoverNaturality.mapOn.congr_simp` | `SingularMayerVietoris.coverRestriction.congr_simp` |
| `CoverNaturality.smallMap.congr_simp` | `SingularMayerVietoris.smallMapOfMapsTo.congr_simp` |

### C. cocycle-class helpers (item 6, 5 names)

| deleted (`private`, `CycleLift.lean`) | surviving twin (`AbCycleClass.lean`) |
|---|---|
| `CategoryTheory.HomologicalComplex.shortCycleClass` | `CategoryTheory.ShortComplex.shortCycleClass` |
| `CategoryTheory.HomologicalComplex.shortCycleClass_eq_zero_iff` | `CategoryTheory.ShortComplex.shortCycleClass_eq_zero_iff` |
| `CategoryTheory.HomologicalComplex.shortCycleClass_quotient` | `CategoryTheory.ShortComplex.shortCycleClass_quotient` |
| `CategoryTheory.HomologicalComplex.shortCycleClass_surjective` | `CategoryTheory.ShortComplex.shortCycleClass_surjective` |
| `CategoryTheory.HomologicalComplex.shortHomologyMap_cycleClass` | `CategoryTheory.ShortComplex.shortHomologyMap_cycleClass` |

### D. two-open-cover corollaries and the cochain-homotopy lemma

| deleted | surviving twin |
|---|---|
| `SphereHomology.twoOpenCover_fundamentalGroup_eq_one` | `FundamentalGroup.VanKampen.Cocone.TwoOpenCover.fundamentalGroup_eq_one` |
| `SphereHomology.twoOpenCover_pathConnectedSpace` | `FundamentalGroup.VanKampen.Cocone.TwoOpenCover.pathConnectedSpace` |
| `AlgebraicTopology.SingularCochains.homotopy_on_cocycle_succ` | `CochainComplex.homotopy_on_cocycle_succ` |
| `TopCat.SingularSmallChains.homotopy_on_cocycle_succ` | `CochainComplex.homotopy_on_cocycle_succ` (rename, see the rename map) |


## 5. Build lines

All run from the worktree root with
`/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake`.

| command | result |
|---|---|
| `lake build Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Surjectivity` | `Build completed successfully (1729 jobs).` |
| `lake build Lib.AlgebraicTopology.SingularHomology.SuspensionCover Lib.AlgebraicTopology.SingularHomology.Naturality` | `Build completed successfully (8724 jobs).` |
| `lake build Lib.AlgebraicTopology.SingularHomology.OnePointCover Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality Lib.Geometry.Manifold.Morse.SurgeryCollapse` | `Build completed successfully (8782 jobs).` |
| `lake build Lib.Algebra.Homology.ShortComplex.AbCycleClass Lib.Algebra.Homology.HomologicalComplex.CycleLift Lib.Algebra.Homology.DerivedCategory.Ext.InjectiveResolutionHomology` | `Build completed successfully (1795 jobs).` |
| `lake build Lib.Algebra.Homology.Homotopy.CocycleEvaluation Lib.AlgebraicTopology.SingularSmallChains.CochainHomotopy Lib.AlgebraicTopology.SingularCochains.PositivePrimitives` | `Build completed successfully (2058 jobs).` |
| `lake build Lib.AlgebraicTopology.SingularHomology.Sum Lib.AlgebraicTopology.SingularHomology.Coproduct` | `Build completed successfully (8715 jobs).` |
| `lake build Lib` | `Build completed successfully (9151 jobs).` |
| `lake build Solution S6Shortcuts S6 Challenge` | `Build completed successfully (9190 jobs).` — `'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | `Build completed successfully (9151 jobs).` — the only axiom sets reported are subsets of `[propext, Classical.choice, Quot.sound]` |
| `python3 scripts/lib_stock_census.py --check` | `ratchet PASS: 123 <= baseline 1648` |

The single `declaration uses 'sorry'` warning is `Challenge.lean:42`, the statement of the open
problem; that file is untouched by this seat (`git diff 4e15a034..HEAD -- Challenge.lean` is
empty).

## 6. Commits

```
ba7f0b36  Lib/AlgebraicTopology/FundamentalGroup: delete the van Kampen monolith
a3c8ce9c  Lib/AlgebraicTopology/SingularHomology/Naturality.lean: one Mayer-Vietoris naturality proof
60b9593e  Lib/Algebra/Homology/ShortComplex/AbCycleClass.lean: one copy of the cocycle-class helpers
ecf64466  Lib/Algebra/Homology/Homotopy/CocycleEvaluation.lean: one cochain-homotopy evaluation lemma
a3c05a72  Lib/AlgebraicTopology/SingularHomology: record why Sum and Coproduct both stay
```

plus this receipt.  Range `4e15a034..HEAD`.

## 7. Left for the next seat

1. **Item 2** — retire `SingularChains.*` in favour of the Mathlib-PR trio
   (`SimplexPaths`/`CycleClasses`/`Degree1`).  ~150 duplicated declarations, 57 importers,
   ~3200 references; the `ChainHomology` halves need re-proving, not aliasing.
2. **Item 3** — replace `MayerVietoris.lean` l.1115–2635 by the
   `SingularSmallChains/Barycentric/*` development.  124 duplicated declarations; needs the same
   chain-tower bridge as item 2, so do the two together.
3. **Item 10, degree-one cochain lemmas** — blocked on
   `Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1Criterion.lean`; needs a seat that owns
   both `SingularSmallChains` and `Topology/Sheaves`.
4. **Item 11, structure merge** — `TwoStepResolution extends AcyclicResolutionH1 where epi_g`;
   the `Hom` half touches five `Lib/Topology/Sheaves` files.
5. **Item 6, `ModuleCat ℤ` cycle-class pair** — `ChainCycleLift.shortCycleClass*` against
   `SingularChains.ChainHomology.shortCycleClass*`; belongs with item 2.
6. **Mesh two-set tails** — dead code in `MeshLebesgue`/`MeshAffine`/`MeshSubdivision`; re-derive
   them from `ArbitraryCoverMesh.lean` at `ι := Bool` (a rewrite, not a deletion), together with
   the fourth copy in `MayerVietoris.lean:2283–2631`.
