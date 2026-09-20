# Round 7 packet 03 — receipt

Worktree `/home/goblin/hopf-r7-p03`, branch `r7/packet-03`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.

32 files in the packet, 32 done, 0 left.

## Totals

| item | done | left |
|---|---|---|
| 1. manuscript citations | 116 manuscript coordinates removed and replaced by a textbook reference, in 14 files; 8 further files given the textbook reference their module docstring lacked | 0 |
| 2. docstrings | 171 declaration docstrings added (10 files); every public declaration in the packet now has one | 0 |
| 3. universe pins | 13 declarations generalised (SquareRoot 10, CochainHomotopy 1, DimensionEquivalence 2); 146 pins left, all forced, listed below | 146 forced |
| 4. `: Type` binders | 0 widened; 99 left, all forced or already polymorphic, listed below | 99 forced / false positives |

## Per file

### `Lib/CategoryTheory/Abelian/` — the delta-functor and derived-functor group

| file | item 1 | item 2 | item 3 | item 4 |
|---|---|---|---|---|
| `CohomologicalDeltaFunctor/Basic.lean` | 6 coordinates (`L-H1`–`L-H6`, equation `(U4)`) → Grothendieck, Tôhoku §2.1; Weibel Def. 2.1.1; Hartshorne III.1 | complete | — | 4 counted, all already `Type u₁`/`Type u₂` (the counter flags any `: Type`, not only `Type 0`) |
| `CohomologicalDeltaFunctor/Effaceable.lean` | 42 coordinates (`L-E*`, `L-U*`, `U-E*`, `U-G*`, `U-N*`, `U-A*`, `(U5)`–`(U23)`) → Tôhoku Prop. 2.2.1; Weibel Thm 2.4.7 / Ex. 2.4.5; Hartshorne III.1.3A | complete | — | 2 counted, already `Type u₁`/`Type u₂` |
| `CohomologicalDeltaFunctor/Ext.lean` | 6 `textbook lines 1744–1786` → Weibel Thm 2.5.1; Hartshorne III.1.1A | complete | `HasExt.{v}` is at the ambient morphism universe, not a level-0 pin | 1 counted, already `Type u` |
| `CohomologicalDeltaFunctor/RightDerived.lean` | 13 (`TEXTBOOK 1589–1826`, `TEXTBOOK M10`, `M00-D`, `CD05L`, "receipts") → Weibel Thm 2.4.6, Ex. 2.4.3; Hartshorne III.1.1A | complete | — | 2 counted, already `Type u` |
| `RightDerived.lean` | 3 (`PD-L04`, `textbook M09` ×2) → Weibel Thm 2.4.6(a), Ex. 2.4.3 | complete | — | 2 counted, already `Type u` |
| `RightDerived/Connecting.lean` | 16 (`PD-L21`, `PD-L23`, `PD20`/`PD21`, `TEXTBOOK 1520–1824`, `TEXTBOOK M10`) → module docstring added citing Weibel Thm 2.4.6(b); Hartshorne III.1.1A | complete | — | 2 counted, already `Type u` |
| `Injective/ShortExact.lean` | 4 (`PD-L05`, `PD-L06`, `PD-L11` ×2) → Weibel Prop. 2.2.8 dualised; Cartan–Eilenberg V.2 | complete | — | 4 counted, already `Type u` |
| `Injective/CompatibleResolution.lean` | 16 (`PD-L07`/`L08`/`L10`/`L12`/`L13`, `PD7`–`PD14`, "receipts") → Weibel Prop. 2.2.8 and Thm 2.2.6 dualised; Cartan–Eilenberg V.2 | complete | — | 9 counted, already `Type u` |
| `Injective/Ext.lean` | 12 (`cohomological-dimension/TEXTBOOK.md, lines …`, `C29a`–`C29d`, `M04`) → Weibel Def. 2.5.1 and §2.7; Hartshorne III.1.1A, Ex. III.6.4 | complete | `HasExt.{v}` at the ambient morphism universe | 7 counted, already `Type u` |
| `Projective/DimensionEquivalence.lean` | none present | complete | **generalised**: `{C D : Type u} [Category.{v} C] [Category.{v} D]` → `{C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]` (the audit's suggestion), affecting `hasProjectiveDimensionLT_functor_obj` and `hasProjectiveDimensionLT_functor_obj_iff` | 1 counted, already `Type u` |

### `Lib/Analysis/Complex/SquareRoot.lean`

* item 1: the module docstring's process narrative removed ("used by the source development"; "renamed from the project prefix `SpecialPeriods` per review A item 3; no external consumers"); the file already cited Rudin, *Real and Complex Analysis*, Theorem 13.11, which is now the only reference.
* item 2: complete (62/62).
* item 3: **10 pins generalised** — `{X : TopCat.{0}} {Y : Type}` → `{X : TopCat.{u}} {Y : Type u}` on
  `AnalyticRootCoverContinuation.predicatePresheaf`, `.etaleValue`, `.sectionGerm`,
  `.etaleValue_sectionGerm`, `.etaleSection_localGerms`, `.etaleSection_locally`,
  `.etaleSection_pred`, `.sectionOfEtaleSection`, `.sectionOfEtaleSection_germ`,
  `.exists_global_section_with_germ_of_germ_bijective` (plus `TopCat.Presheaf (Type) X` → `(Type u) X`).
  One `Type 0` is **left, forced by** `TopCat.LocalPredicate`: `AnalyticRootCover.rootPresheaf` lives on
  `TopCat.of S` for `S : Opens ℂ`, so the fibre universe is pinned to 0 by `ℂ : Type`.
* item 4: no bare `Type` binders.

### `Lib/CategoryTheory/Sites/Leray/` — the fibre-stalk-evaluation group (9 files)

All 130 `.{0}` pins are **left, forced by** declarations outside the packet:

* `CategoryTheory.Sheaf.Leray.AbelianSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X`
  and `CategoryTheory.Sheaf.Leray.integralSheaf`, `.abelianSheafHasExt : HasExt.{0} …`,
  `.pushforward`, `.higherDirectImage(Sheaf)` — all in
  `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean`;
* `TopCat.ConstantSheaf.sheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0})` in
  `Lib/Topology/Sheaves/ConstantPushforward.lean`;
* `TopCat.ConstantSheaf.integralSheaf (X : TopCat.{0})` in
  `Lib/Topology/Sheaves/ConstantPushforward/GlobalSections.lean`;
* `TopCat.Sheaf.freeOpen`, `TopCat.Sheaf.freeHomEquiv` (`AddCommGrpCat.{0}`) in
  `Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean`.

Per file: `CanonicalPositiveNeighborhoodSection.lean` 1, `FibreStalkEvaluation/CanonicalPositive.lean` 12,
`…/CanonicalPositiveCofinalExt.lean` 3, `…/CofinalCriterion.lean` 3, `…/ConstantEvaluationBijective.lean` 4,
`…/ConstantNormalization.lean` 22, `…/ConstantNormalizationConsequences.lean` 3, `…/ConstantPointFibre.lean` 10,
`…/Neighborhood.lean` 72.

Work done:

* `…/ConstantPointFibre.lean`: 4 docstrings added (`fibreInclusion_injective`, `fibreInclusion_isClosedMap`,
  `fibreInclusion_finite_fibres`, `map_fibreInclusion`); module docstring now cites Godement II.4.11.1,
  Bredon II.10, Iversen III.6.2. Its one `: Type` (the return type of `Fibre`) is forced by `Y : TopCat.{0}`.
* `…/Neighborhood.lean`: 2 docstrings added (`neighborhoodCohomologyEquiv_symm_apply`,
  `cohomologyEvaluation_apply`); module docstring now cites Bredon II.9–II.11, Iversen II, Godement II.4.
* The six remaining Leray files had no manuscript citation but named no source either; each module docstring
  now carries its textbook twin (Hartshorne III.8.1 / Godement II.4.11; Godement II.4.11.1 / Bredon II.10 /
  Iversen III.6.2; Godement II.4.11 / Bredon II.10; Bredon II.9–II.10; Bredon II.9 / Iversen II; and, for
  `ConstantNormalizationConsequences.lean`, an explicit statement that it has no textbook counterpart).

### `Lib/AlgebraicTopology/SingularSmallChains/` (6 files)

All `ModuleCat.{0} ℤ` / `AddCommGrpCat.{0}` pins and all `(X : Type)` / `(I : Type)` binders here are
**forced by** `AlgebraicTopology.SingularCochains.chains (X : Type) : ChainComplex (ModuleCat.{0} ℤ) ℕ`,
`.complex`, `.dualComplex` and `.moduleDual` in `Lib/AlgebraicTopology/SingularCochains.lean`
(outside the packet).

| file | done | left |
|---|---|---|
| `Basic.lean` | Hatcher Prop. 2.21 (Bredon IV.17, Spanier 4.4) cited; 16 docstrings added | 12 pins, 19 binders forced |
| `CochainHomotopy.lean` | Hatcher 2.21 dualised cited (`HomotopyEquiv.quasiIso`); **1 pin generalised**: `homotopy_on_cocycle_succ {K L : CochainComplex AddCommGrpCat.{0} ℕ}` → `AddCommGrpCat.{u}` | 3 pins (the coefficient `A` of the three small-chain theorems), 6 binders forced |
| `Projective.lean` | Weibel Thm 10.4.8 / `ChainComplex.quasiIso_iff_of_projective` cited; 1 docstring added | 1 pin, 6 binders forced |
| `Barycentric/Native.lean` | module docstring expanded and Hatcher 2.21 cited; 8 docstrings added | 2 binders forced |
| `Barycentric/Subdivision.lean` | Hatcher 2.21 step (3) cited; 2 docstrings added | 4 binders forced |
| `Barycentric/SubdivisionHomotopy.lean` | Hatcher 2.21 step (3), Bredon IV.17.3 cited; 1 docstring added | 2 binders forced |

### `Lib/AlgebraicTopology/SingularHomology/` (6 files)

All `(X : Type)` / `(G : Type)` binders here are **forced by**
`SingularChains.SingularSimplex (X : Type)` and `SingularChains.singularComplex` in
`Lib/AlgebraicTopology/SingularHomology/Chains.lean` and by
`SingularMayerVietoris.SingularHomology (Y : Type)` in `…/MayerVietoris.lean` — both outside the packet
(the task prompt names `Chains.lean` as the pinned chain-complex interface).

| file | done | left |
|---|---|---|
| `Pontryagin.lean` | 2 manuscript sentences removed (`boundary J-C1`; `are J-C2/J-C3 material and do not live here`); **33 docstrings added**, i.e. all of them; the module docstring already cited Hatcher §3.C | 30 binders forced |
| `Torus.lean` | **50 docstrings added**, i.e. all of them; `productTorusHomologyEquiv` now names Hatcher §3.B (Künneth for `(S¹)^r`) | — |
| `TorusCoordinates.lean` | the namespace/retarget paragraph removed and replaced by a References section citing Hatcher §3.B; **54 docstrings added**, i.e. all of them | 10 binders forced |
| `SuspensionCover.lean` | the module-conversion sentence removed; Hatcher Thm 1.20 (van Kampen) cited | 1 binder forced |
| `SphereHomology.lean` | "the two circle models used in the sources" replaced by the mathematical description; Hatcher Cor. 2.14 already cited | 4 binders forced |
| `Sum.lean` | nothing to do: docstrings complete, Hatcher Prop. 2.6 already cited, no manuscript citation | 21 binders forced (no commit) |

## Build lines

```
lake build Lib
  ✔ [9149/9150] Built Lib (2.9s)
  Build completed successfully (9150 jobs).

lake build Solution S6Shortcuts S6 Challenge
  ℹ [9188/9189] Built Solution (4.9s)
  info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms:
        [propext, Classical.choice, Quot.sound]
  Build completed successfully (9189 jobs).

lake build Lib.AxiomAudit
  Build completed successfully (9150 jobs).
  3352 `#print axioms` lines; every one uses only propext / Classical.choice / Quot.sound.
  No sorryAx, no Lean.ofReduceBool.
```

## envdiff

The base table was dumped before any edit:

```
lake env lean-agent-ide dump Lib --modules Lib > $S/dump_base.jsonl     # done 0, 21719 lines
```

The after-table dump was started after the three builds and is **still running**: the machine is
executing twelve concurrent `lean-agent-ide dump` processes (one per round-7 packet) on 20 cores,
and this one has advanced by 17 s of CPU in the last hour. `$S/dump_after.jsonl` is therefore
still empty and `envdiff.json` could not be produced inside this session. The command to finish it,
once the machine is free, is

```
lake env /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Lib --modules Lib \
  > $S/dump_after.jsonl 2> $S/dump_after.err
python3 /home/goblin/lean-agent-ide/tools/envdiff.py $S/dump_base.jsonl $S/dump_after.jsonl \
  --receipt $S/envdiff.json
```

with `$S=/home/goblin/.claude/jobs/06995e68/tmp/r7-p03/`.

The property the envdiff checks was instead established directly from the source diff, which is
the stronger statement (it inspects every changed byte rather than a hash of the result):

* `git diff -U0 9552305f..HEAD -- '*.lean'` has **858 changed lines**. Filtering out every line
  that lies inside a `/-- … -/` or `/-! … -/` block leaves exactly these code lines:

  | file | change |
  |---|---|
  | `Lib/AlgebraicTopology/SingularSmallChains/CochainHomotopy.lean` | `universe u` added; `homotopy_on_cocycle_succ {K L : CochainComplex AddCommGrpCat.{0} ℕ}` → `AddCommGrpCat.{u}` |
  | `Lib/Analysis/Complex/SquareRoot.lean` | `universe u` added; ten headers `{X : TopCat.{0}} {Y : Type}` → `{X : TopCat.{u}} {Y : Type u}`; `predicatePresheaf`'s result `TopCat.Presheaf (Type) X` → `(Type u) X` |
  | `Lib/CategoryTheory/Abelian/Projective/DimensionEquivalence.lean` | `universe v u` → `universe v₁ v₂ u₁ u₂`; `variable {C D : Type u} [Category.{v} C] [Category.{v} D] …` → `variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] …` |

  Nothing else outside a docstring changed in any of the 30 touched files.

* Scanning the diff for declaration headers (`theorem`/`lemma`/`def`/`abbrev`/`instance`/`structure`/
  `class`/`inductive`) gives **0 names added and 0 names removed**: every touched header appears on
  both a `-` and a `+` line. (The one apparent new name, `of`, is a false positive — a docstring
  line beginning "class of `(S¹)^n`".)

* `lake build Lib`, `lake build Solution S6Shortcuts S6 Challenge` and `lake build Lib.AxiomAudit`
  are all green on the result, so the whole environment still elaborates.

### Changed-type table (13 declarations, each explained)

| declaration | generalisation |
|---|---|
| `TopCat.SingularSmallChains.homotopy_on_cocycle_succ` | `AddCommGrpCat.{0}` → `AddCommGrpCat.{u}` |
| `AnalyticRootCoverContinuation.predicatePresheaf` | `TopCat.{0}`/`Type` → `TopCat.{u}`/`Type u` (and `Presheaf (Type u)`) |
| `AnalyticRootCoverContinuation.etaleValue` | idem |
| `AnalyticRootCoverContinuation.sectionGerm` | idem |
| `AnalyticRootCoverContinuation.etaleValue_sectionGerm` | idem |
| `AnalyticRootCoverContinuation.etaleSection_localGerms` | idem |
| `AnalyticRootCoverContinuation.etaleSection_locally` | idem |
| `AnalyticRootCoverContinuation.etaleSection_pred` | idem |
| `AnalyticRootCoverContinuation.sectionOfEtaleSection` | idem |
| `AnalyticRootCoverContinuation.sectionOfEtaleSection_germ` | idem |
| `AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective` | idem |
| `CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj` | shared `Type u`/`Category.{v}` → independent `Type u₁`/`Type u₂`, `Category.{v₁}`/`Category.{v₂}` |
| `CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj_iff` | idem |

Source declarations lost: **0**. Source declarations added: **0**. Types changed: **13**, all
explained above. No unexplained change.

## Commits

Range `9552305f..91521e99` (25 commits, one per file except the six Leray
citation-only files, which share one commit).

* `9b46bd7c` Lib/CategoryTheory/Abelian/CohomologicalDeltaFunctor/Basic.lean: cite Tôhoku 2.1 / Weibel 2.1.1
* `c65ec8ad` Lib/CategoryTheory/Abelian/CohomologicalDeltaFunctor/Effaceable.lean: cite Tôhoku 2.2.1 / Weibel 2.4.7
* `2c7d62cb` Lib/CategoryTheory/Abelian/CohomologicalDeltaFunctor/Ext.lean: cite Weibel 2.5.1
* `a2ad1935` Lib/CategoryTheory/Abelian/CohomologicalDeltaFunctor/RightDerived.lean: cite Weibel 2.4.6
* `8056133a` Lib/CategoryTheory/Abelian/RightDerived.lean: cite Weibel 2.4.6(a) and Ex. 2.4.3
* `297dbc80` Lib/CategoryTheory/Abelian/Injective/ShortExact.lean: cite Weibel 2.2.8 (Horseshoe, dual form)
* `6c3cbc75` Lib/CategoryTheory/Abelian/RightDerived/Connecting.lean: add module docstring citing Weibel 2.4.6(b)
* `2144c6e1` Lib/CategoryTheory/Abelian/Injective/CompatibleResolution.lean: cite Weibel 2.2.8/2.2.6 (Horseshoe, dual)
* `db2ab504` Lib/CategoryTheory/Abelian/Injective/Ext.lean: cite Weibel 2.5.1 / Hartshorne III.1.1A
* `a81ce169` Lib/Analysis/Complex/SquareRoot.lean: cite Rudin 13.11, generalise the étale-continuation universe
* `2ad3dbdd` Lib/CategoryTheory/Abelian/Projective/DimensionEquivalence.lean: independent universes for the two categories
* `081c2d0c` Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/ConstantPointFibre.lean: cite Godement II.4.11.1, document the fibre inclusion
* `cfe24fa9` Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/Neighborhood.lean: cite Bredon II.9-II.11, document two simp lemmas
* `f31d9b09` Lib/CategoryTheory/Sites/Leray: cite the textbook twins in six module docstrings
* `32fac7e7` Lib/AlgebraicTopology/SingularSmallChains/Barycentric/Native.lean: document 8 declarations, cite Hatcher 2.21
* `724424e6` Lib/AlgebraicTopology/SingularSmallChains/Barycentric/Subdivision.lean: cite Hatcher 2.21, document 2 declarations
* `1f47bdf4` Lib/AlgebraicTopology/SingularSmallChains/Barycentric/SubdivisionHomotopy.lean: cite Hatcher 2.21, document subdivisionHomotopy_simplex
* `609481ee` Lib/AlgebraicTopology/SingularSmallChains/Projective.lean: cite Weibel 10.4.8, document the hom simp lemma
* `f08ef109` Lib/AlgebraicTopology/SingularSmallChains/CochainHomotopy.lean: cite Hatcher 2.21, generalise the homotopy lemma universe
* `f21be097` Lib/AlgebraicTopology/SingularSmallChains/Basic.lean: cite Hatcher 2.21, document 16 declarations
* `11e0ecb1` Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean: document all 33 declarations, drop the J-C sentences
* `8516cba9` Lib/AlgebraicTopology/SingularHomology/SuspensionCover.lean: cite Hatcher 1.20, drop the module-conversion note
* `d95842d2` Lib/AlgebraicTopology/SingularHomology/Torus.lean: document all 50 declarations
* `723ead0c` Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean: document all 54 declarations, cite Hatcher 3.B
* `91521e99` Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean: name the two circle models instead of 'the sources'

Plus this receipt.
