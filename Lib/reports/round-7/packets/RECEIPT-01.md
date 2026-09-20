# Round 7 checklist packet 01 — receipt

Worktree `/home/goblin/hopf-r7-p01`, branch `r7/packet-01`, base `9552305f`, Lean v4.33.0,
Mathlib v4.33.0.  Packet: `Lib/reports/round-7/packets/packet-01.md` (59 files).

**54 of the 59 files changed, 5 needed nothing.  No file is left undone.**

## Summary per work item

| item | total |
|---|---|
| 1. manuscript citations replaced | 3 files (5 document coordinates), plus 12 files of process narrative removed |
| 1'. `## References` blocks added (textbook name where the audit gave a twin) | 41 files |
| 2. docstrings added on public declarations | 287 in 22 files; every file in the packet is now fully documented |
| 3. universe pins `.{0}` generalised | **116 (corrected)** of 143, in 10 files; **27 (corrected)** left, each recorded as forced below |
| 4. `: Type` (level 0) binders widened | 17 of 74; 57 left, each recorded as forced below.  The packet's `: Type` binder counts for the 39 `Ext`/`DerivedCategory`/`SpectralObject`/`SpectralSequence`/`ThreeColumn*`/`CycleClasses` files are false positives of the audit grep: those binders are already `{C : Type u} [Category.{v} C]`-style and universe polymorphic |

### 1. Manuscript citations

| file | removed | replaced by |
|---|---|---|
| `Lib/Algebra/Group/DeterminingFamily.lean` | `Source: CENTER_NATIVE_GENERATION_TEXTBOOK.md, reviewed NG4–NG10`; `(NG5–NG6)`; `In the reviewed order (NG7–NG10)` | a `## References` block naming the folklore centrality criterion (`Subgroup.center`, `MonoidHom.ext` applied to `MulAut.conj`), and two docstrings restated as what the theorems say |
| `Lib/Algebra/Group/Prod.lean` | `Textbook source: CENTER_SIGNED_PAIR_SURJECTIVITY_TEXTBOOK.md, SP1–SP6` | a statement of what the lemma says, pointing at `AddMonoidHom.prod` / `AddMonoidHom.ker`; the licence header was also missing and was added |
| `Lib/Algebra/Module/IntegerPresentation.lean` | the whole `## Provenance` section (move from `Hopf/SphereTopology.lean`, lanes F0b and F10, the rename plan) | `## References`: Milnor, *Lectures on the h-cobordism theorem* §7; Lang, *Algebra* III; pointer to `Module.Presentation` |

Process narrative deleted (no document coordinate, but a project step or consumer named):
`PostnikovSlice.lean` (three "downstream naturality owner" sentences → a cross-reference to
`PostnikovSliceNaturality.lean`), `InjectiveResolutionHomology.lean` ("the restriction coherence
needed to … pass to germs and stalks"), `CycleClasses.lean` ("in the direction consumers use"),
`Generators.lean` ("independently of sheafification and degree-one arguments"),
`CoefficientNormalization.lean` ("the repository convention", "the fixed convention", "the
repository's small … convention"), `HomeomorphCoordinates.lean` ("the coefficient convention"),
`CoordinateChange.lean` ("the coordinate-level source of contragredient monodromy"),
`VanKampen/Basic.lean` and `VanKampen/PathValue.lean` ("It contains no proof-specific cover or
relator data" → what the file proves), `MayerVietorisShortExact.lean` (the copied preamble
`open Set Function Filter Manifold Topology`), `LeftHomologyData.lean` (bare title expanded).

### 2. Docstrings

| file | added | file | added |
|---|---|---|---|
| `VanKampen/PathValue.lean` | 91 | `TwoTermMappingCone.lean` | 9 |
| `VanKampen/Basic.lean` | 61 | `AcyclicResolutionFiniteCompatibility.lean` | 9 |
| `IntegerPresentation.lean` | 23 | `CochainTransgression.lean` | 8 |
| `DualEvaluation.lean` | 20 | `SingularCochains.lean` | 6 |
| `ChainCycleLift.lean` | 15 | `AcyclicResolutionH1.lean` | 4 |
| `InjectiveResolutionHomology.lean` | 11 | `CoefficientNormalization.lean` | 4 |
| `ExactAugmentedCochainComplex.lean` | 10 | `ThreeColumnPage.lean` | 4 |
| `TwoStepSplice.lean` | 2 | `TwoStepSpliceLowerNormalization.lean` | 2 |
| `Free.lean` | 2 | `Generators.lean` | 2 |
| `ShortExactAcyclicQuotient.lean` | 1 | `ShortExactDegreeOne.lean` | 1 |
| `TwoStepResolutionNaturality.lean` | 1 | `TruncationTriangle.lean` | 1 |

Total 287.  No `private` declaration was documented.  After the packet, a coverage check over all
59 files reports no undocumented public `theorem`/`def`/`abbrev`/`structure`/`instance`: the only
three hits it still prints (`ThreeColumnSpectralSequence.lean` l.17, `Degree1.lean` l.616,
`CoefficientNormalization.lean` l.69) are prose lines inside existing docstrings that begin with
the words "structure" or "class".

### 3. Universe pins

| file | pins before → after | what was generalised | what is forced |
|---|---|---|---|
| `Algebra/Homology/MayerVietorisShortExact.lean` | 23 → 0 | `ModuleCat.{0} ℤ` → `ModuleCat.{v} ℤ` in all 19 declarations | — |
| `AlgebraicTopology/SingularCochains/DualEvaluation.lean` | 24 → 0 | `AddCommGrpCat.{0}` → `.{w}` and `ModuleCat.{0} ℤ` → `.{v}` throughout | — |
| `Algebra/Homology/HomologicalComplex/CycleLift.lean` | 10 → 0 | `AddCommGrpCat.{0}` → `.{w}` | — |
| `Algebra/Homology/HomologicalComplex/ChainCycleLift.lean` | 9 → 0 | `ModuleCat.{0} ℤ` → `.{v}` | — |
| `…/Ext/InjectiveResolutionHomology.lean` | 7 → 0 (corrected) | `Category.{0}`/`HasExt.{0}`/`AddCommGrpCat.{0}` → `.{v}` | — |
| `…/DualEvaluation/HomeomorphCoordinates.lean` | 4 → 0 (corrected) | the coefficient object is now `AddCommGrpCat.of (ULift.{w} ℤ)` | — |
| `…/DualEvaluation/Free.lean` | 2 → 0 | `A : AddCommGrpCat.{w}`, `K : ChainComplex (ModuleCat.{v} ℤ) ℕ` | — |
| `…/DualEvaluation/CoordinateChange.lean` | 1 → 0 | `K : ChainComplex (ModuleCat.{v} ℤ) ℕ` | — |
| `AlgebraicTopology/SingularCochains.lean` | 36 → 7 (corrected) | 28: `precompose`, `moduleDual`, `dualComplexFunctor`, `dualComplex`, `dualMap`, `dualMap_id`, `dualMap_comp`, `dualHomotopy` now take `A : AddCommGrpCat.{w}` over `ModuleCat.{u} ℤ` | the 7 left are in `chains`, `pullback`, `pullback_id`, `pullback_comp`: forced by `ModuleCat.of ℤ ℤ`, the coefficient object fed to `AlgebraicTopology.singularChainComplexFunctor`, whose carrier `ℤ` lives in `Type 0`.  Attempting `ModuleCat.{u} ℤ` there gives `Application type mismatch: the argument ℤ has type Type … but is expected to have type Type u … in @ModuleCat.of ℤ Int.instRing ℤ` |
| `…/DualEvaluation/CoefficientNormalization.lean` | 20 → 13 | 7: `A : AddCommGrpCat.{w}`, `K L : ChainComplex (ModuleCat.{v} ℤ) ℕ` | the 13 left are the `ULift.{0} ℤ` block (`uliftIntCoefficientEquiv`, `uliftIntCohomologyEvaluation` and its four lemmas): forced by the normalization target being the literal `ℤ : Type 0` |
| `AlgebraicTopology/SingularCochains/Generators.lean` | 6 → 6 | none | forced by `TopCat.SingularSmallChains.chainLift` and `TopCat.SingularSmallChains.addHomToIntLinearMap` in `Lib/AlgebraicTopology/SingularSmallChains/Basic.lean` (outside this packet), whose targets are `Type 0`.  With `A : AddCommGrpCat.{w}`: `Type mismatch: (chainLift X n ?m).toAddMonoidHom has type ↑((chains X).X n) →+ ?m of sort Type but is expected to have type Cochains X A n of sort Type w` |
| `AlgebraicTopology/Hurewicz/Degree1.lean` | 1 → 1 | none | the single `.{0}` is inside the module docstring, which already explains the pin: the chain complex needs `singularChainComplexFunctor` coproducts indexed by the universe of the space |
| `…/Ext/CochainTransgression.lean` | 0 → 0 | the `TwoStepResolution` section now takes `[HasExt.{w} C]` with `w` independent of the hom universe `v` | the `CochainComplex` section keeps `[HasExt.{v} C]`: `cochainTransgression` compares the literal group `P ⟶ Hⁿ⁺¹K`, which lives in `AddCommGrpCat.{v}`, with a group of `Ext` classes.  First error when freed: `Application type mismatch: Ext P (cycles K n) 2 has type Type w … but is expected to have type Type v … in @AddCommGrpCat.of (Ext P (cycles K n) 2)` |

Total **116 generalised, 27 left (corrected)**, all four obstacles recorded above.
(The per-file "after" column already summed to 7 + 13 + 6 + 1 = 27; see the corrections
section at the end of this receipt.)

### 4. `: Type` (level 0) binders

| file | before → after | widened | forced |
|---|---|---|---|
| `…/DualEvaluation/CoefficientNormalization.lean` | 10 → 1 | `{B M : Type}` → `{B : Type w} {M : Type*}`, `{B M N : Type}` and `{M N : Type}` → `Type*`, `{B : Type}` → `{B : Type w}` | `X : Type` in `singularUliftIntCohomologyEvaluation_isIso_of_projective`, forced by `chains X` |
| `…/DualEvaluation/Free.lean` | 5 → 2 | `{L : Type}` → `{L : Type v}` in the general sections | `X : Type` and `{L : Type}` in the `Singular` section, forced by `chains X` |
| `…/DualEvaluation/HomeomorphCoordinates.lean` | 7 → 5 | `H : Type` → `Type*`, `L : Type` → `Type w` | `X Y : Type`, forced by `chains X` |
| `…/DualEvaluation/CoordinateChange.lean` | 2 → 0 | `{L : Type}` → `{L : Type v}` | — |
| `AlgebraicTopology/SingularCochains.lean` | 10 → 9 | `{M N : Type}` in `precompose` → `Type*` | `X Y Z : Type`, forced by `ModuleCat.of ℤ ℤ` as above |
| `AlgebraicTopology/SingularCochains/Generators.lean` | 8 → 8 | none | forced by `SingularSmallChains/Basic.lean` as above |
| `AlgebraicTopology/Hurewicz/Degree1.lean` | 30 → 30 | none | forced, and already explained in the file's module docstring |

The remaining 39 files of the packet carry the audit's `: Type` binder count only because the grep
counts `Type u`: every one of those binders is `{C : Type u} [Category.{v} C]`,
`{R : Type u} [Ring R]`, `{M : Type v}`, `{ι : Type*}` and similar, already polymorphic.

### Files that needed no change

`…/Ext/DegreeZero.lean`, `…/Ext/ExactFunctoriality.lean`,
`Algebra/Homology/HomologicalComplex/MapExtend.lean`,
`Algebra/Homology/HomotopyCategory/HomComplexSingle.lean`,
`AlgebraicTopology/Hurewicz/Degree1.lean`.
All five are verdict A, fully documented, free of manuscript citations, and their only listed work
item is the `: Type` false positive (Degree1's pins and binders are forced and already explained in
the file).  The first four have a Mathlib file rather than a textbook as their twin, so no
`## References` block was invented for them.

## Builds

```
lake build Lib
  Build completed successfully (9150 jobs).
lake build Lib Solution S6Shortcuts S6 Challenge Lib.AxiomAudit
  Build completed successfully (9191 jobs).
```

`Lib.AxiomAudit` and `Solution.lean` report only
`[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice]` and
`[propext, Classical.choice, Quot.sound]`; no other axiom occurs.
No `sorry`, `axiom`, or `admit` was introduced; no declaration was deleted.

## Environment diff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl`:

```
constants before 21719 after 21719 (keys 21713 21713)
lost 407 added 407 of which source declarations: 0 0
names with changed type 407 of which source: 314
module moves (source declarations, 1-to-1): 0
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

**0 source declarations lost, 0 added.**  All 314 changed source types are explained by the
universe generalisations of item 3; `changed_type_source` (the diff tool's "unexplained" bucket)
is 0, and every changed name is accounted for by the table below.

| where | changed types | explanation |
|---|---|---|
| `SingularCochains.DualEvaluation` | 67 | `AddCommGrpCat.{0} → .{w}`, `ModuleCat.{0} ℤ → .{v}` |
| `…Ext.InjectiveResolutionHomology` | 35 | `Category.{0}`/`HasExt.{0}`/`AddCommGrpCat.{0} → .{v}` |
| `HomologicalComplex.ChainCycleLift` | 20 | `ModuleCat.{0} ℤ → .{v}` |
| `MayerVietorisShortExact` | 19 | `ModuleCat.{0} ℤ → .{v}` |
| `AlgebraicTopology.SingularCochains` | 17 | `AddCommGrpCat.{0} → .{w}`, `ModuleCat.{0} ℤ → .{u}` in the duality half |
| `…DualEvaluation.CoefficientNormalization` | 14 | `A : AddCommGrpCat.{w}`, `ModuleCat.{v} ℤ`, `B : Type w` |
| `…DualEvaluation.Free` | 10 | `A : AddCommGrpCat.{w}`, `ModuleCat.{v} ℤ`, `L : Type v` |
| `…DualEvaluation.HomeomorphCoordinates` | 8 | `ULift.{w} ℤ`, `L : Type w`, `H : Type*` |
| `…DualEvaluation.CoordinateChange` | 2 | `ModuleCat.{v} ℤ`, `L : Type v` |
| `…SingularCochains.Generators`, `…Ext.CochainTransgression`, `…Ext.TwoStepResolutionNaturality`, `HomologicalComplex.CycleLift` | 1 each | **(corrected)** `Generators`: `pullback_simplex`, because it mentions `pullback`, which is now `pullback.{w}` — *not* the `Cochains` abbreviation, which is unchanged, and not `chains`, which was not generalised; `HasExt.{w}` in the `TwoStepResolution` section; `AddCommGrpCat.{w}` in the one public lemma of `CycleLift` (its seven `private` helpers are counted in the "28 private" row below, so this row's "1" is the public lemma only) |
| private declarations of the modules above (names mangled in the dump) | 28 | same generalisations |
| downstream modules (`SingularSmallChains.Basic`, `SingularCochains.Vanishing`, `Topology.Sheaves.SingularCochainSheaf.*`, `CategoryTheory.Sites.Leray.*`, `…Ext.CochainTransgressionHomology`, `…Ext.PostnikovD2*`, `…Ext.HomologyTwoStepResolutionExtend`) | 90 | not edited; their types now mention the generalised constants, so they carry explicit universe arguments where the level used to be fixed at 0.  Spot check: `@TopCat.SingularSmallChains.cochainRestriction : {X : Type} → [TopologicalSpace X] → {I : Type} → (A : AddCommGrpCat) → (U : I → Set X) → complex X A ⟶ dualComplex A (complex U)` — same statement, now polymorphic in the coefficient universe |

`prefix` was empty, so the diff covered the whole environment, not only `Lib`.

## Commits

`9552305f..067ee091`, 55 commits: 54 one-file commits (subject `Lib/<path>: <what>`) and one
cross-cutting documentation commit `067ee091` that renames the citation keys introduced by the
earlier commits of this packet (`hatcher2002 → hatcher02`, `weibel1994 → weibel94`,
`hartshorne1977 → hartshorne77`, `milnor1965 → milnor65`, `lang2002 → lang02`,
`gelfandManin2003 → gelfandManin03`, `cartanEilenberg1956 → cartanEilenberg56`,
`tomDieck2008 → tomDieck08`) to the short form the library already uses in 39 places for Hatcher
and 14 for Milnor.

```
41b7ecfb Lib/Algebra/Group/DeterminingFamily.lean: replace the manuscript citation by the standard statement
d00ecf24 Lib/Algebra/Group/Prod.lean: replace the manuscript citation, add the licence header
6852a6d0 Lib/Algebra/Homology/DerivedCategory/Ext/AcyclicResolutionFiniteCompatibility.lean: document nine declarations
9b68d615 Lib/Algebra/Homology/DerivedCategory/Ext/AcyclicResolutionH1.lean: cite Weibel 2.4.3, document four declarations
87b25ffb Lib/Algebra/Homology/DerivedCategory/Ext/CochainTransgression.lean: cite Weibel, document eight declarations, free the Ext universe
68225e79 Lib/Algebra/Homology/DerivedCategory/Ext/ExactAugmentedCochainComplex.lean: cite Weibel 2.4, document ten declarations
c2524413 Lib/Algebra/Homology/DerivedCategory/Ext/InjectiveResolutionHomology.lean: cite Weibel 2.7.6, document eleven declarations, generalise the universe pins
9205d04a Lib/Algebra/Homology/DerivedCategory/Ext/ShortExactAcyclicQuotient.lean: document extTwoEquivMiddleOfSubsingletonQuotient_apply
30cd568a Lib/Algebra/Homology/DerivedCategory/Ext/ShortExactDegreeOne.lean: document extZeroEquivKerPostcompG_apply
ca9aa550 Lib/Algebra/Homology/DerivedCategory/Ext/TwoStepResolutionNaturality.lean: document boundary_i
19b955a2 Lib/Algebra/Homology/DerivedCategory/Ext/TwoStepSplice.lean: document two declarations
d6b8f8f4 Lib/Algebra/Homology/DerivedCategory/Ext/TwoStepSpliceLowerNormalization.lean: document two declarations
566846bd Lib/Algebra/Homology/DerivedCategory/TruncationTriangle.lean: document truncationTriangleIso_hom_hom2
ed23e65d Lib/Algebra/Homology/HomologicalComplex/ChainCycleLift.lean: cite Hatcher 2.1, document fifteen declarations, generalise the ModuleCat universe
cbb282e7 Lib/Algebra/Homology/HomologicalComplex/CycleLift.lean: cite Hatcher 2.1, generalise the AddCommGrpCat universe
0d2f128d Lib/Algebra/Homology/HomotopyCategory/TwoTermMappingCone.lean: cite Weibel 1.5, document nine declarations
e002336a Lib/Algebra/Homology/MayerVietorisShortExact.lean: generalise the ModuleCat universe, drop the unused preamble opens
5fcbb858 Lib/Algebra/Homology/ThreeColumnSpectralSequence.lean: cite Weibel 5.2
6b1102c9 Lib/Algebra/Homology/ThreeColumnSpectralSequence/ThreeColumnPage.lean: document four declarations
85ced809 Lib/Algebra/Module/IntegerPresentation.lean: replace the provenance section by references, document all 23 declarations
c31bbc73 Lib/AlgebraicTopology/SingularCochains.lean: cite Hatcher 3.1, document six declarations, generalise the coefficient and module universes
9553ec8b Lib/AlgebraicTopology/SingularCochains/Generators.lean: cite Hatcher 3.1, document two declarations, drop the consumer sentence
164fa4e6 Lib/AlgebraicTopology/SingularCochains/DualEvaluation.lean: cite Hatcher 3.2, document twenty declarations, generalise all universe pins
1d6be2e4 Lib/AlgebraicTopology/SingularCochains/DualEvaluation/CoefficientNormalization.lean: cite Hatcher 3.2, document four declarations, generalise the universe pins
f10231da Lib/AlgebraicTopology/SingularCochains/DualEvaluation/CoordinateChange.lean: generalise the universe pin and the L binder
806032f4 Lib/AlgebraicTopology/SingularCochains/DualEvaluation/Free.lean: cite Hatcher 3.2, document two declarations, generalise the universe pins
c64d21ea Lib/AlgebraicTopology/SingularCochains/DualEvaluation/HomeomorphCoordinates.lean: cite Hatcher 3.1, generalise the universe pins and the Type binders
cf697f0e Lib/AlgebraicTopology/FundamentalGroup/VanKampen/Basic.lean: cite Hatcher 1.20, document all 61 declarations
55607666 Lib/AlgebraicTopology/FundamentalGroup/VanKampen/PathValue.lean: cite Hatcher 1.20, document all 91 declarations
2e469381 Lib/Algebra/Homology/DerivedCategory/Ext/AcyclicResolutionH1ExactFunctor.lean: cite Weibel 2.4.3 and Grothendieck Tohoku
a6669d94 Lib/Algebra/Homology/DerivedCategory/Ext/AcyclicResolutionH2H3.lean: cite Weibel 2.4.3
45d9a929 Lib/Algebra/Homology/DerivedCategory/Ext/AdjacentTwoSliceSplice.lean: cite BBD 1.3, Kashiwara-Schapira 10.1 and Verdier II
acb335e4 Lib/Algebra/Homology/DerivedCategory/Ext/ExactFunctorComparison.lean: cite Weibel 2.4 and Grothendieck Tohoku
10f3ec2b Lib/Algebra/Homology/DerivedCategory/Ext/InjectiveResolutionCoyoneda.lean: cite Weibel 2.7.6 and Hartshorne III.1
b53d4792 Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovD2Normalized.lean: cite BBD 1.3 and Deligne Hodge II 1.4
df4c7b07 Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovD2PageCoordinates.lean: cite BBD 1.3 and Deligne Hodge II 1.4
297c58d5 Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovD2PageSplice.lean: cite BBD 1.3 and Deligne Hodge II 1.4
22eb1168 Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovD2Splice.lean: cite BBD 1.3 and Verdier III
e31798e2 Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovTwoSliceSplice.lean: cite BBD 1.3 and Verdier III.4
b0d8bb6b Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovUpperEndpointConcreteNormalization.lean: cite BBD 1.3 and Verdier III.4
249a37fb Lib/Algebra/Homology/DerivedCategory/Ext/PostnikovUpperEndpointNormalization.lean: cite BBD 1.3 and Verdier III.4
22fef2ce Lib/Algebra/Homology/DerivedCategory/KInjectiveCohomology.lean: cite Spaltenstein 1988 and Weibel 10.4-10.7
34ab73c1 Lib/Algebra/Homology/DerivedCategory/PostnikovSliceNaturality.lean: cite BBD 1.3 and Kashiwara-Schapira 10.1
0733a118 Lib/Algebra/Homology/DerivedCategory/PostnikovTwoSlice.lean: cite Kashiwara-Schapira 10.1 and BBD 1.3
c4e14106 Lib/Algebra/Homology/DerivedCategory/PostnikovTwoSliceEndpoints.lean: cite BBD 1.3
8111427f Lib/Algebra/Homology/DerivedCategory/PostnikovTwoSliceShift.lean: cite BBD 1.1 and Verdier II
47e9623b Lib/Algebra/Homology/SpectralObject/MapHomologicalFunctor.lean: cite BBD 1.3 and Verdier II
6a9629ec Lib/Algebra/Homology/SpectralObject/Postnikov.lean: cite BBD 1.3 and Gelfand-Manin IV.4
03b24598 Lib/Algebra/Homology/SpectralObject/PostnikovD2.lean: cite BBD 1.3 and Deligne Hodge II 1.4
7d51141a Lib/Algebra/Homology/SpectralSequence/NatLowerEdge.lean: cite Weibel 5.2
774ab4a0 Lib/Algebra/Homology/ThreeColumnSpectralSequence/LowerTransfer.lean: cite Weibel 5.2
8004b012 Lib/Algebra/Homology/DerivedCategory/PostnikovSlice.lean: cite BBD 1.3, replace the 'owner' sentences by a cross-reference
e87a321b Lib/Algebra/Homology/ShortComplex/LeftHomologyData.lean: expand the module docstring
6baf37f4 Lib/AlgebraicTopology/Hurewicz/CycleClasses.lean: drop the consumer wording from one docstring
067ee091 Lib: use the repository's short citation keys in the references added this round
```

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-01.md` (ACCEPT WITH FINDINGS; no statement
weakened, no hypothesis added, every lift literally the old statement at level 0).  The corrections
below are to this receipt's text only; no Lean file was changed by them.  Numbers marked
"(corrected)" above were fixed in place; the original figures are quoted here because they were
also reported to the coordinator.

1. **Universe-pin counts (finding 3).**  The receipt said "119 of 143 generalised, 24 left".  The
   correct figures are **116 lifted, 27 left**, out of the same total of 143.  Three per-file
   "before" numbers were typed one too low and disagreed with the packet list the agent was given:
   `Ext/InjectiveResolutionHomology.lean` 6 → **7**, `DualEvaluation/HomeomorphCoordinates.lean`
   3 → **4**, `AlgebraicTopology/SingularCochains.lean` 35 → **36**.  With those, the per-file
   "before" column sums to 143 and the "after" column to 7 + 13 + 6 + 1 = 27, which is what the
   receipt's own forced column already said.  Nothing was mis-lifted; only the arithmetic was wrong.

2. **Generators envdiff row (finding 4).**  The receipt explained the one changed type in
   `…SingularCochains.Generators` by "the `Cochains` abbreviation now mentions the polymorphic
   `chains`".  That is wrong twice over: `chains` was *not* generalised (this receipt lists it as
   forced, and it is still `ChainComplex (ModuleCat.{0} ℤ) ℕ` at head) and `Cochains` is unchanged.
   The declaration whose type changed is `pullback_simplex`, because it mentions `pullback`, which
   is now `pullback.{w}` (confirmed by `Lib/reports/round-7/envdiff-merged-d950428a.json`, which
   lists `AlgebraicTopology.SingularCochains.pullback_simplex` in that module).  The table row above
   is corrected.

3. **`moduleDual` / `dualComplex` land in `max u w`, not `.{w}` (finding 6).**  The receipt said
   only "`A : AddCommGrpCat.{w}` over `ModuleCat.{u} ℤ`".  At head the signatures are

   ```
   moduleDual.{u_1,u_2}   : AddCommGrpCat.{u_2} → (ModuleCat.{u_1} ℤ)ᵒᵖ ⥤ AddCommGrpCat.{max u_1 u_2}
   dualComplex.{u_1,u_2}  : AddCommGrpCat.{u_2} → ChainComplex (ModuleCat.{u_1} ℤ) ℕ →
                              CochainComplex AddCommGrpCat.{max u_1 u_2} ℕ
   ```

   This is the forced level and `max 0 w = w`, so `complex X A : CochainComplex AddCommGrpCat.{w} ℕ`
   and every level-0 instance is literally the old statement.  But a consumer feeding
   `K : ChainComplex (ModuleCat.{v} ℤ) ℕ` with `v ≠ 0` gets a cochain complex in a universe different
   from `A`'s; the receipt should have said so.

4. **`: Type` binder counts (finding 9b) — recorded, not replaced.**  The receipt says "74 total, 57
   forced, 17 widened".  The reviewer's two independent regexes both give **72 total / 55 forced**
   (the 17 widened agrees).  This receipt never stated its counting rule (occurrences vs.
   declarations, `: Type)` vs. `: Type}` vs. `: Type` followed by a newline), so the two counts are
   not comparable and neither is adopted over the other: both are recorded here.  Under the round-8
   rule a binder line must read "found N, widened M, left K because …".

5. **Process-narrative file count (finding 9a).**  "12 files of process narrative removed" — the
   table names **11** files.

6. **No per-packet `envdiff.json`/`.txt` is in the repository (finding 5).**  The envdiff section
   above quotes tool output (407 lost/added, 314 changed source types, the per-module table) that
   cannot be re-run from the tree: `Lib/reports/round-7/packets/` holds only the ten receipts and
   ten packet lists, and the worktree the dumps were taken in is gone.  The only in-tree artefact is
   the round-wide `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}`, which mixes all ten
   packets (1,438 changed names, all classified `PROOF-NAMING`) and can confirm module membership
   only.  The per-module counts (67, 35, 20, 19, 17, 14, 10, 8, 2, 28, 90) are therefore
   **unverified**.  The round-8 rule — every receipt commits its `envdiff.json`/`.txt` beside itself
   — is now the standing rule for all rounds (`Lib/reviews/REVIEW-7-8.md` §4).

7. **Citations and docstrings.**  The reviewer's `[citation]`/`[docstring]` findings (the two literal
   "Exercise 1.3.x" / "2.4.x" placeholders, Weibel "Theorem 2.4.3", the
   `rectangleHorizontalVertical`/`VerticalHorizontal` docstrings,
   `commute_all_of_lattice_image_eq_zpow`, the loose Weibel 2.7.6 / Cartan–Eilenberg Ch. V
   pointers) are code fixes, not receipt fixes; they are listed in `Lib/reviews/REVIEW-7-8.md` §3
   and are the business of the packet-01 fix agent, not of this correction.
