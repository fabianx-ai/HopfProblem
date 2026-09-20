# Round 8 — `dup-sheaf` receipt

Worktree `/home/goblin/hopf-r8-dup-sheaf`, branch `r8/dup-sheaf`, base `4e15a034`,
Lean v4.33.0 / Mathlib v4.33.0.  Packet: `Lib/reports/round-7/judgement/duplicates.md`,
items 7, 8, 9 (the sheaf items).

Commits `e8161fd1` (item 9), `910fe5d5` (item 8), `0d8e2b19` (item 7), plus this receipt.

---

## Item 9 — one name for the constant ℤ sheaf, the global-sections functor, `presheafToSheaf`

### Constant integer sheaf

Survivor **`TopCat.ConstantSheaf.integralSheaf`** (`Lib/Topology/Sheaves/ConstantPushforward/GlobalSections.lean`):
it is the universe-polymorphic copy, it carries the documented corepresentability API
(`integralHomGlobalEquiv`, Hartshorne III.2 / Godement II.4), and it already existed.

| deleted | surviving twin |
|---|---|
| `TopCat.SheafH1.unitSheaf` (`Cohomology/AcyclicResolutionH1.lean`) | `TopCat.ConstantSheaf.integralSheaf` |
| `CategoryTheory.Sheaf.Leray.integralSheaf` (`Sites/Leray/ResolutionTransgression.lean`, a self-declared "compatibility spelling") | `TopCat.ConstantSheaf.integralSheaf` |
| `TopCat.SheafH1.constantIntegerSheaf` (private, `H1Vanishing/Flasque.lean`) | `TopCat.ConstantSheaf.integralSheaf` |
| `TopCat.SheafCohomology.constantIntegerSheaf` (private, `Cohomology/FlasqueAcyclic.lean`) | `TopCat.ConstantSheaf.integralSheaf` |

All four had the body `(constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))`,
which is what `TopCat.ConstantSheaf.integralSheaf` unfolds to.  So that the survivor is still
recognised *reducibly* wherever Mathlib spells the constant sheaf out — `CategoryTheory.Sheaf.H F n`
is by definition `Ext ((constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) F n` —
`TopCat.ConstantSheaf.sheaf` is now `@[reducible]`.  Without that, the `calc` in
`TopCat.SheafH1.hom_surjective_of_global_surjective` no longer elaborates.

`TopCat.Sheaf.OpenRestriction.unitFreeTopIso` is **not** a duplicate: it is the isomorphism
`ℤ_X ≅ ℤ[⊤]` between the constant sheaf and the free sheaf on the top open.  It is kept, renamed
`integralSheafFreeTopIso` for consistency (rename map below).

### Global-sections functor

Survivor **`TopCat.Sheaf.globalSectionsFunctor`** in the new module
`Lib/Topology/Sheaves/GlobalSections.lean` (module docstring cites Hartshorne II.1 / Godement II.2).
This is `TopCat.SheafH1.globalSectionsFunctor` moved out of a heavy `Ext` file and generalised from
universe `0` to `u` — `envdiff` reports it as a rename with an unchanged use-set
(`PROOF-NAMING`).  A new module was needed because the three copies sat at incomparable heights in
the import graph (`Cohomology/AcyclicResolutionH1.lean` is above the whole `Ext` stack,
`FiniteSupport/SkyscraperGlobalSections.lean` imports only `Mathlib.Topology.Sheaves.Abelian`).

| deleted | surviving twin |
|---|---|
| `TopologicalSpace.OpenCover.SetOpenCover.sheafGlobalSectionsFunctor` (`Cohomology/Cech/DeltaFunctor.lean`) | `TopCat.Sheaf.globalSectionsFunctor` (character-identical body) |
| `TopologicalSpace.OpenCover.SetOpenCover.sheafGlobalSectionsFunctor_additive` | `TopCat.Sheaf.globalSectionsFunctor_additive` |
| `TopCat.Sheaf.FiniteSupport.topEvaluation` (`FiniteSupport/SkyscraperGlobalSections.lean`) | `TopCat.Sheaf.globalSectionsFunctor` (`Sheaf.forget ⋙ evaluation.obj (op ⊤)`; Mathlib's `sheafSectionsNatIsoEvaluation` is `Iso.refl`) |

`TopCat.SheafCohomology.GlobalSections` (`Cohomology/ShortExactDegreeZeroSections.lean`) is **left**:
it is the `Type` abbreviation for the carrier `F(⊤)`, not the functor, and is used only as a type.

### `presheafToSheaf` aliased three times

Survivor **`TopCat.Sheaf.sheafification`** in the new module
`Lib/Topology/Sheaves/Sheafification.lean` (Godement II.1.2 / Kashiwara–Schapira II.2).  This is
`TopCat.SingularCochainSheaf.sheafification` moved; all three copies had the body
`presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat`.

| deleted | surviving twin |
|---|---|
| `TopCat.SheafificationPushforward.sheafification` | `TopCat.Sheaf.sheafification` |
| `CategoryTheory.Sheaf.Leray.sheafification` | `TopCat.Sheaf.sheafification` |
| `CategoryTheory.Sheaf.Leray.sheafification_additive` | `TopCat.Sheaf.sheafification_additive` |

`TopCat.SheafificationLocal.sheaf` (the *object*-level abbreviation `(presheafToSheaf …).obj P`) now
consumes the survivor rather than repeating its body.

**Observed but out of packet:** `freeOpenFunctor` is defined character-identically three times, in
`Cohomology/FlasqueAcyclic.lean`, `Sites/Leray/ResolutionCohomologyPresheaf.lean` and
`Sites/Leray/FibreStalkEvaluation/Neighborhood.lean`.  Not touched (item 9 names `presheafToSheaf`,
which is the `sheafification` triple).

---

## Item 8 — `FunctionSheaf.lean` is the constant family of `DependentFunctionSheaf.lean`

`Lib/Topology/Sheaves/FunctionSheaf.lean` is deleted.  Every declaration in it is its
`DependentFunctionSheaf` twin at the constant family `fun _ => A`; the two files had
line-for-line identical proofs.  The two consumers
(`SingularCochainSheaf/DegreeZeroFunctions.lean`, `SingularCochainSheaf/DegreeZeroAcyclic.lean`)
now call the dependent version.

| deleted | surviving twin (at `fun _ => A`) |
|---|---|
| `TopCat.FunctionSheaf.presheaf` | `TopCat.DependentFunctionSheaf.presheaf` |
| `TopCat.FunctionSheaf.presheaf_obj` | `TopCat.DependentFunctionSheaf.presheaf_obj` |
| `TopCat.FunctionSheaf.presheaf_map_apply` | `TopCat.DependentFunctionSheaf.presheaf_map_apply` |
| `TopCat.FunctionSheaf.forgetIso` | `TopCat.DependentFunctionSheaf.forgetIso` |
| `TopCat.FunctionSheaf.isSheaf` | `TopCat.DependentFunctionSheaf.isSheaf` |
| `TopCat.FunctionSheaf.sheaf` | `TopCat.DependentFunctionSheaf.sheaf` |
| `TopCat.FunctionSheaf.extendByZero` | `TopCat.DependentFunctionSheaf.extendByZero` |
| `TopCat.FunctionSheaf.restrict_extendByZero` | `TopCat.DependentFunctionSheaf.restrict_extendByZero` |
| `TopCat.FunctionSheaf.sheaf_isFlasque` | `TopCat.DependentFunctionSheaf.sheaf_isFlasque` |

---

## Item 7 — the H¹-first sheaf pipeline

Read: `Lib/reports/round-7/packets/RECEIPT-10.md` ("Notes for the owner": the auditors' tree
restructure was outside packet 10 and the `H¹`-only forks "remain duplicates of the `_succ`
results") and the auditors' entries in `Lib/reports/textbook-audit/audit.json` for
`ComparisonH1`, `GlobalUnitH1`, `GlobalUnitH1Criterion`, `GlobalResolutionH1`, `LocalExactH1`,
`ResolutionH1`, `Pullback/ComparisonH1`, `Pullback/FiniteClosedH1`, `PrimitivesH1`,
`BarycentricSmallChains`.

### Done: what is a literal special case

| deleted | surviving twin |
|---|---|
| `TopCat.SingularCochainSheaf.globalCochainComparison_homology_isIso_one` | `…globalCochainComparison_homology_isIso_succ X A hsmall 0` — identical statement and identical `[NormalSpace X] [ParacompactSpace X]` hypotheses |
| `TopCat.SingularCochainSheaf.globalUnitSurjective` | `…globalCochainUnit_surjective` (it was a one-line alias) |
| `TopCat.SingularCochainSheaf.complexSheaf_exactAt_one` | `…complexSheaf_exactAt_succ X A hLC 0` |
| `TopCat.SingularCochainSheaf.exists_restriction_primitive_one` (private) | `…exists_restriction_primitive_succ … 0` (private) |
| `TopCat.SingularCochainSheaf.SmallKernelGlobalOne` | `…SmallKernelGlobal X A 1` |
| `TopCat.SingularCochainSheaf.smallKernelGlobalOne` | `…smallKernelGlobal X A 1` |
| `TopCat.SingularCochainSheaf.globalCochainComparison_cycle_lift_one` | `…globalCochainComparison_cycle_lift_succ … 0` |
| `TopCat.SingularCochainSheaf.globalCochainComparison_boundary_detect_one` | `…globalCochainComparison_boundary_detect_succ … 0` |
| `TopCat.SingularCochainSheaf.globalCochainComparison_homology_isIso_one_of_small_chains` | `…globalCochainComparison_homology_isIso_succ_of_small_chains … 0` |

Files deleted: `SingularCochainSheaf/GlobalUnitH1.lean`, `SingularCochainSheaf/LocalExactH1.lean`.
Consumers rerouted: `ConstantSheafH1.lean` and `ConstantProductH1FibreIndependence.lean` (they now
call the positive-degree theorem at `0`; they already had the instances it needs),
`SingularCochainSheaf/ResolutionH1.lean`.

Moves (reported by `envdiff`, not judged):
`initialComplex_exact` and its private helper `exists_restriction_constant`
`LocalExactH1.lean → LocalExactPositive.lean` (which now states the whole resolution, Bredon III.1);
`SmallKernelGlobal` `GlobalUnitPositive.lean → GlobalUnitPredicates.lean`;
`smallKernelGlobal` `GlobalUnitPositive.lean → GlobalKernelSmall.lean`.

Predicate collapse: five ad-hoc `Prop` predicates became four — `SmallKernelGlobalOne` is gone and
`GlobalUnitH1Criterion.lean`, which now holds only `GlobalUnitSurjective`,
`GlobalKernelLocallySmall`, `SmallKernelGlobal`, `HasSmallChainEquivalences`, is renamed
`GlobalUnitPredicates.lean` with a docstring saying where each is discharged.

### Recorded and left (each needs a new proof or a statement change)

1. **The H¹ resolution route is not a special case: it is metrizability-free.**
   `constantSheafGlobalH1Iso X A hLC` (`GlobalResolutionH1.lean`) needs only
   `LocallyContractibleSpace X`; `constantSheafGlobalIso X A hLC 0` (`ComparisonPositive.lean`)
   additionally needs `[MetrizableSpace X]`, because `resolution_isAcyclic`
   (`ResolutionPositive.lean`) gets flasqueness of `𝒮^n` from
   `OpenRestriction.isFlasque_of_metrizable`, while the H¹ route only needs
   `zeroCochainSheaf_h1_subsingleton`.  Deleting the H¹ route would add a hypothesis to every
   consumer, which the round-8 rules forbid.  Removing it properly needs (a) `globalCochainComplex`
   moved out of `GlobalResolutionH1.lean` — note `ResolutionPositive.lean` *imports*
   `GlobalResolutionH1.lean` for it, so the H¹ file is currently load-bearing for the positive one —
   and (b) a new proof that the singular-cochain resolution is acyclic without metrizability
   (the auditors suggest hereditary paracompactness).  Left: `GlobalResolutionH1.lean`,
   `ResolutionH1.lean`.
2. **`ComparisonH1.lean` likewise.**  `h1Comparison X A hLC [IsIso …1]` carries no
   `[MetrizableSpace X]`; `constantSheafCohomologyIsoSingular X A hLC 0` does.  Its consumers
   (`ConstantSheafH1.lean`, `ConstantProductH1FibreIndependence.lean`) are stated for compact
   Hausdorff spaces with no metrizability hypothesis.  Left, together with
   `Pullback/ComparisonH1.lean` and `Pullback/FiniteClosedH1.lean`, which are built on it.
3. **`PrimitivesH1.nullhomotopic_pullback_closed_one`** is literally
   `AlgebraicTopology.SingularCochains.nullhomotopic_pullback_closed_succ … 0` and, after this
   packet, unused.  Deleting it orphans a chain of private helpers in the same file
   (`homotopy_apply_closed_one`, `pullback_const_closed_one_zero`, `cocycle_one_point_zero`,
   `pointBoundaryTwo`, `pointChain`, `addHomToIntLinearMap`, `pointSimplex_eq`), which is the
   auditors' larger "replace by one lemma `nullhomotopic_pullback_closed (n : ℕ)`" restructure.
   Left.
4. **Full collapse of the four remaining predicates into one theorem.**
   `hasSmallChainEquivalences_barycentric` (`BarycentricSmallChains.lean`) proves
   `HasSmallChainEquivalences X` for *every* space, and `globalCochainUnit_surjective`,
   `globalKernelLocallySmall`, `smallKernelGlobal` discharge the other three on a normal
   paracompact space; so `globalCochainComparison_homology_isIso_succ` could drop its `hsmall`
   argument entirely.  That removes a hypothesis from a statement — not one of the changes round 8
   allows (move, rename, universe/binder generalisation, deletion with a twin) — and needs
   `GlobalUnitPositive.lean` to import `BarycentricSmallChains.lean`.  Left, with the predicates
   kept and documented.
5. The auditors' remaining suggestions (`ComparisonPositive` absorbing `ComparisonH1`,
   `FiniteClosedPositive` absorbing `FiniteClosedH1`, weakening `[MetrizableSpace]` to hereditary
   paracompactness) all reduce to 1–2 above.  Left.

---

## Rename map

`Lib/reports/round-8/dup-sheaf/rename.txt`.  `dump --rename` keys on the name present in the
environment being dumped, and the map is applied to the *post-change* dump, so each line is
`<name now>` `<name in the base environment>`:

| now | in the base environment |
|---|---|
| `TopCat.Sheaf.globalSectionsFunctor` | `TopCat.SheafH1.globalSectionsFunctor` |
| `TopCat.Sheaf.globalSectionsFunctor_additive` | `TopCat.SheafH1.globalSectionsFunctor_additive` |
| `TopCat.Sheaf.sheafification` | `TopCat.SingularCochainSheaf.sheafification` |
| `TopCat.Sheaf.sheafification_additive` | `TopCat.SingularCochainSheaf.sheafification_additive` |
| `TopCat.Sheaf.integralSheafEquivImageIso` | `TopCat.Sheaf.unitSheafEquivImageIso` |
| `TopCat.Sheaf.integralSheaf_hasProjectiveDimensionLT_iff_cohomology_subsingleton` | `TopCat.Sheaf.unitSheaf_hasProjectiveDimensionLT_iff_cohomology_subsingleton` |
| `TopCat.Sheaf.integralSheaf_hasProjectiveDimensionLT_iff_of_iso` | `TopCat.Sheaf.unitSheaf_hasProjectiveDimensionLT_iff_of_iso` |
| `TopCat.Sheaf.OpenRestriction.integralSheaf_hasProjectiveDimensionLT_iff_freeOpen_top` | `TopCat.Sheaf.OpenRestriction.unitSheaf_hasProjectiveDimensionLT_iff_freeOpen_top` |
| `TopCat.Sheaf.OpenRestriction.integralSheaf_projective_of_discreteTopology` | `TopCat.Sheaf.OpenRestriction.unitSheaf_projective_of_discreteTopology` |
| `TopCat.Sheaf.OpenRestriction.integralSheafFreeTopIso` | `TopCat.Sheaf.OpenRestriction.unitFreeTopIso` |

---

## Envdiff

`Lib/reports/round-8/dup-sheaf/envdiff.json` (full lists).  Base dump `4e15a034`, 38593 constants;
after 38558.

```
constants before 38593 after 38558 (keys 38491 38456)
lost 169 added 134 of which source declarations: 106 78
names with changed type 121 of which source: 83
auxiliary lost/added/changed (not judged): 63 56 38
module moves (source declarations, 1-to-1):
   3  …SingularCochainSheaf.GlobalUnitH1Criterion -> …SingularCochainSheaf.GlobalUnitPredicates
   1  …SingularCochainSheaf.GlobalUnitPositive    -> …SingularCochainSheaf.GlobalKernelSmall
   1  …SingularCochainSheaf.GlobalUnitPositive    -> …SingularCochainSheaf.GlobalUnitPredicates
   2  …SingularCochainSheaf.LocalExactH1          -> …SingularCochainSheaf.LocalExactPositive
   2  …SingularCochainSheaf.Sheaf                 -> …Topology.Sheaves.Sheafification
ambiguous module changes: 0
VERDICT FAIL
```

**Lost names.**  The `lost`/`added` source counts overlap: a name that appears in both is a
*changed type*, not a deletion.  Subtracting the overlap, the names that are lost and not
re-added are **exactly the 28 deleted duplicates of the three tables above**, each with its
surviving twin named there:

* item 9 (10): `TopCat.SheafH1.unitSheaf`, `CategoryTheory.Sheaf.Leray.integralSheaf`,
  `TopCat.SheafH1.constantIntegerSheaf`, `TopCat.SheafCohomology.constantIntegerSheaf`,
  `TopologicalSpace.OpenCover.SetOpenCover.sheafGlobalSectionsFunctor(_additive)`,
  `TopCat.Sheaf.FiniteSupport.topEvaluation`, `TopCat.SheafificationPushforward.sheafification`,
  `CategoryTheory.Sheaf.Leray.sheafification(_additive)`;
* item 8 (9): the nine `TopCat.FunctionSheaf.*`;
* item 7 (9): the nine `TopCat.SingularCochainSheaf.*_one` / `…One` declarations.

Nothing else is lost.  **No source name is added** that is not one of those renames: the 13
added-only keys are all `._proof_n` auxiliaries.

**Changed types (78 source declarations).**  Every one is a statement that named a deleted
duplicate and now names its survivor; the propositions are unchanged, because each deleted name
was an abbreviation (or an `n = 0` instance) of the survivor.  By cause:

| cause | count |
|---|---|
| statement now names `TopCat.ConstantSheaf.integralSheaf` instead of `unitSheaf` / `Leray.integralSheaf` / `constantIntegerSheaf` | 35 |
| statement now names the single `sheafification` instead of the `Leray` / `SheafificationPushforward` copy | 21 |
| statement now names the single `globalSectionsFunctor` instead of `sheafGlobalSectionsFunctor` / `topEvaluation` | 16 |
| statement now names `TopCat.DependentFunctionSheaf.*` instead of `TopCat.FunctionSheaf.*` | 5 |
| `_proof_1` renamed with its parent (`integralSheafEquivImageIso`) | 1 |

Two further names, `TopCat.SheafH1.globalSectionsFunctor` and `…_additive`, changed type as the
universe generalisation `{0} ⇝ {u}` made when the survivor moved to the new module; `envdiff`
classifies them as `PROOF-NAMING` (their use-sets are identical).

The `FAIL` verdict is the 78 changed types plus the 28 explained deletions: `envdiff` judges any
changed type unexplained unless it is passed with `--accept`.  Statement-spelling churn of this
kind is unavoidable when duplicate definitions are merged — it is the price of the packet — and
every changed name is accounted for above.

---

## Build

Foreground `lake build` per edited module, then, from the worktree root:

```
lake build Lib                                    done 0
lake build Solution S6Shortcuts S6 Challenge      done 0
lake build Lib.AxiomAudit                         done 0
python3 scripts/lib_stock_census.py --check       done 0   (stock declarations under Hopf/: 123)
```

`Lib.AxiomAudit` reports only `propext`, `Classical.choice`, `Quot.sound`.
`Lib.lean` lists every `Lib` module, including the two new ones.
