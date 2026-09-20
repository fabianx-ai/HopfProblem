# Round-8 receipt — `pins` (chokepoint universe pins)

Packet: `Lib/reports/round-7/judgement/chokepoint-pins.md`.
Branch `r8/pins`, base `4e15a034`.

Scope: lift the universe-zero pins on the chokepoint declarations the packet names, one commit
per chokepoint, rebuild the consumers, then re-run the round-7 checklist item "universe pins" on
the files the lifted chokepoints release.

`.{0}` pins in `Lib`: **1024 in 99 files before → 320 in 48 files after** (704 lifted, 51 files
cleared).  No renames; no rename map.

## 1. Chokepoints lifted

| chokepoint | file | commit | what it is now |
|---|---|---|---|
| `CategoryTheory.Sheaf.cohomologyAddCommGroup` | `Cohomology/AddCommGroup.lean` | `feba6a42` | `{X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : AddCommGroup (Sheaf.H.{u} F n)`.  The instance was **lifted, not deleted**, as instructed; `Ext.instAddCommGroup` supplies it at every `u`, `HasExt.{u}` coming from `IsGrothendieckAbelian.hasExt` |
| `TopCat.SheafH1.unitSheaf` (with `globalSectionsFunctor`, `h0GlobalIso`, `h0GlobalIso_naturality`, `AcyclicResolutionH1.globalComplex`, `extZeroGlobalIso`, `h1GlobalIso`) | `Cohomology/AcyclicResolutionH1.lean` | `63bdbb61` | `.{u}` throughout; `ULift.{u} ℤ` is the constant sheaf's value |
| `HasExt.{0}` private instance `abelianSheaf_hasExt` and `subsingleton_h1_of_isFlasque` | `H1Vanishing/Flasque.lean` | `f5a50893` | `HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X)`; the whole file `.{u}` |
| `OpenEmbeddingCohomology.openImage` and its namespace | `OpenEmbeddingCohomology.lean` | `6973220d` | `.{u}` |
| `TopCat.Sheaf.freeOpen`, `freeHomEquiv`, `OpenRestriction.freeOpen`, `OpenRestriction.cohomologyEquiv` | `OpenRestriction/Cohomology.lean` | `ccf092a2` | `.{u}` |
| `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv` | **`FiniteClosedPushforward.lean` (corrected; the receipt said `FiniteClosedPushforward/Exact.lean`)** — that declaration was in fact lifted by round-7 packet 08; `Exact.lean`'s own pin was its `variable {X Y : TopCat.{0}}`, which commit `b457a9fe` lifted | `b457a9fe` | `.{u}` |
| `TopCat.ConstantSheafCohomology.pullback` | `ConstantCohomologyPullback.lean` | `f59653c5` | `.{u}` |
| `TopCat.Sheaf.OpenRestriction.germ_stalkIso_hom_nearbyRestrictionUnit` (and `nearbyRestrictionUnit_app`) | `OpenRestriction/NearbyRestrictionGerm.lean` | `6f4277d9` | was pinned invisibly.  **(corrected)** the mechanism given here — "a bare `{X : TopCat}` binder and bare `AddCommGrpCat` arguments, which elaborate at universe 0 under this repo's `autoImplicit false`" — is **false**.  Bare binders alone become universe *parameters* (`theorem a0 {X : TopCat} (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat X) : True` elaborates as `@a0.{u_1,u_2}`), and `autoImplicit` is irrelevant to this.  What pins is **`TopCat.Presheaf.germ`**, whose `[Limits.HasColimits AddCommGrpCat.{?v}]` instance argument is resolved while `?v` is still a metavariable, and instance resolution assigns `?v := 0`: every statement containing `germ` comes out at `.{0}`, statements without it do not.  The observation "it was at universe 0" is right — the base statement re-elaborated verbatim has no universe parameters at all — so the lift to `.{u}` is a genuine lift whose `u = 0` instance is the old statement.  But the rule "bare `TopCat`/`AddCommGrpCat` ⇒ pinned" is the wrong detector in both directions: the three remaining bare `TopCat.Presheaf AddCommGrpCat X` occurrences at head (`HigherDirectImageSheafification.lean:97,102`, `ResolutionCohomologyPresheaf.lean:140`) are fully `.{u_1}`, while a `.{0}`-free statement can still be pinned through an instance argument.  **A census that greps `.{0}` cannot find this class**; `#check` with `pp.universes true` (or `#print`, looking for a missing `.{…}` on the constant) can.  Now `{X : TopCat.{u}}`, `AddCommGrpCat.{u}` |

Already lifted before this packet, verified rather than redone:
`TopCat.ConstantSheaf.sheaf`, `.integralSheaf`, `integralHomGlobalEquiv`,
`integralPushforwardHom_comp_bijective` (`ConstantPushforward.lean`,
`ConstantPushforward/GlobalSections.lean`) are `.{u}` since packet 08; `TopCat.Sheaf.pushforwardAdditive`
is `.{u}` since packet 07.  Their consumers in the Leray cluster are lifted below.

## 2. Files released and re-checked (checklist item "universe pins")

Every declaration of each file below is now `.{u}`.  Found by grepping the round-7 receipts for the
chokepoint names, then by rebuilding.

* `85312af3` — `Cohomology/{AcyclicResolution, AcyclicResolutionH1Naturality, ProjectiveDimension,
  ShortExactAcyclicQuotient, ShortExactDegreeOne, ShortExactDegreeZeroSections,
  RepresentedOpenProjectiveDimension, FlasqueAcyclic, MayerVietorisProjectiveDimension,
  MayerVietorisVanishing, HomeomorphProjectiveDimension, GodementResolution,
  DiscreteProjectiveDimension}.lean`, `FiniteClosedPushforward/Cohomology.lean`.
* `f59653c5` — `ConstantCohomologyPullback.lean`, `FiniteClosedPushforward/{AcyclicResolution,
  AcyclicResolutionH1, Composition}.lean`, `FiniteClosedOpenRestriction.lean`,
  `OpenFiniteClosedFactorization.lean`.
* `6f4277d9` — `OpenRestriction/StalkCriterion.lean` (round-7 recorded this one as blocked by a
  `whnf` timeout; the timeout was a consequence of the universe defaulting, and is gone).
* `a140e4b1` — the Leray cluster: `CanonicalPositiveNeighborhoodSection`,
  `FibreStalkEvaluation/{CanonicalPositive, CanonicalPositiveCofinalExt, CofinalCriterion,
  ConstantEvaluationBijective, ConstantNormalization, ConstantNormalizationConsequences,
  ConstantPointFibre, Neighborhood, OpenRestrictionComposition, Stalk}`,
  `HigherDirectImageSheafification`, `ResolutionAbutment`, `ResolutionCohomologyPresheaf`,
  `ResolutionPostnikov`, `ResolutionPostnikovD2`, `ResolutionPostnikovD2Coordinates`,
  `ResolutionPostnikovD2Transgression`, `ResolutionTransgression`,
  `SheafificationNeighborhoodGerm`, `SheafificationStalkCompatibility`; plus
  `Lib/Topology/Sheaves/{SheafificationLocal, SheafificationLocalGerm, NestedOpenCohomology}.lean`.

Two `: Type` binders were widened where the lift forced it, both recorded as forced by round 7:
`TopCat.SheafCohomology.GlobalSections`'s carrier ascription (`Type` → `Type u`) and
`ConstantPointFibre.Fibre : Type` → `Type u`.

Universe arguments the elaborator used to default to `0` are now written out.  They are the only
edits outside a universe annotation in this packet — **(corrected)** the receipt originally called
them "the only proof-text edits", but four of the `(C := AbelianSheaf Y)` insertions are inside
theorem *statements*, not proofs (`ResolutionTransgression.lean` at the branch tip, l.181–185,
217–221, 231–235, 267–271).  `C` is determined there by
`pushedResolution f I : CochainComplex (AbelianSheaf Y) ℕ`, so the elaborated term is unchanged and
the statement at `u = 0` is the same term; the sentence was inaccurate, not the work.  The list:
`(C := AbelianSheaf Y)` on `ExtTransgression.cochainTransgression`,
`ExtTransgression.homologyTwoStepResolution` and
`homologyTwoStepResolutionExtendUpNat_connectingTwo`;
`AddCommGrpCat.{u}` on `TopCat.Presheaf.stalkFunctor` / `TopCat.Sheaf.forget`;
`ULift.{u + 1}` for the Postnikov `E₂` page (was `ULift.{1}`);
`HasSmallLocalizedShiftedHom.{u + 1}` and `homEquivCoyonedaHomologyOfIsKInjective.{u + 1}`
in `ResolutionAbutment.lean` (were `.{1}`).

## 3. Chokepoints recorded and skipped

### `AlgebraicTopology.SingularCochains.chains` / `.complex` (packet priority 1)

The pin is `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ`, the coefficient object fed to
`AlgebraicTopology.singularChainComplexFunctor`.  The only way to state it at `ModuleCat.{u} ℤ`
is to replace the literal `ℤ` by `ULift.{u} ℤ`.  That version **elaborates**: with

```
abbrev chains (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)
```

(and the same substitution in `complex`, `pullback`, `pullback_id`, `pullback_comp`,
`pullbackHomotopy` and their `X Y Z : Type` binders) `Lib.AlgebraicTopology.SingularCochains`
builds clean and the file's 7 remaining pins and 9 `: Type` binders all go.
`HasCoproducts.{u} (ModuleCat.{u} ℤ)` is available, so the coproduct side is not the obstacle.

It is skipped because the coefficient object is no longer the literal `ℤ`, and four consumer
modules then need real proof rewrites (`lake build Lib` stops at):

```
Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean:67:2: Type mismatch
  (HomotopyEquiv.ofIso
        (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)
          (TopCat.of Unit))).trans
    (ChainComplex.alternatingConstHomotopyEquiv pointFreeModule)
has type
  HomotopyEquiv (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of Unit))
    ((ChainComplex.single₀ (ModuleCat ℤ)).obj pointFreeModule)
but is expected to have type
  HomotopyEquiv (chains Unit) ((ChainComplex.single₀ (ModuleCat ℤ)).obj pointFreeModule)
```

and

```
Lib/AlgebraicTopology/SingularSmallChains/Basic.lean:53:2: Type mismatch
  (ConcreteCategory.hom ((singularSet X).ιChainComplex (simplexIndex X n sigma))) 1
has type
  ↑(((singularSet X).chainComplex (ModuleCat.of ℤ ℤ)).X n)
but is expected to have type
  ↑((AlgebraicTopology.SingularCochains.chains X).X n)
```

followed by `LinearMap.toSpanSingleton ℤ`, `LinearMap.ext_ring` and `iota_functionChainHom`
failures in `SingularSmallChains/Basic.lean`, `SingularCochainSheaf/DegreeZeroFunctions.lean`
and `SingularCochainSheaf/Augmentation.lean`: the singular basis element is the literal `1 : ℤ`
there, and moving to `ULift ℤ` rewrites those proofs.  The attempt is kept out of tree; the
packet's remaining 26 `SingularCochainSheaf/*` files, `SingularCochains/{Generators, Vanishing,
PositivePrimitives}`, `DualEvaluation/CoefficientNormalization` (the `ULift.{0} ℤ` block),
`SingularSmallChains/{Basic, CochainHomotopy, Projective}` and
`Topology/Sheaves/{ConstantProductH1, ConstantProductH1Comparison,
ConstantProductH1FibreIndependence, ConstantProductPositiveFibreIndependence,
ConstantSheafH1}` stay pinned for exactly this reason — **280 of the 320 pins left (corrected; the
receipt said 271)**, or 287 counting `SingularCochains.lean`'s own 7.  **(corrected)** the
`SingularCochainSheaf/*` file count above is **32**, not 26 (`git grep -o -F '.{0}' 5ad9ec3c^2 --
'Lib/*.lean'` gives 32 files with pins in that directory, 207 pins).

**The obstruction is a protocol obstruction, not only a consumer-proof one (added on correction).**
Mathlib's `singularChainComplexFunctor` (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:30-38`)
is declared under `universe w v u`, `variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
[Preadditive C]` with result `C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ`, so the space universe `w` is tied
to the coproduct-index universe.  `HasCoproducts.{u} (ModuleCat.{u} ℤ)` synthesises;
`HasCoproducts.{u} (ModuleCat.{0} ℤ)` fails (it needs `UnivLE.{u,0}`); `(ModuleCat.of ℤ ℤ :
ModuleCat.{1} ℤ)` is a type error; and `ModuleCat.of ℤ (ULift.{0} ℤ) = ModuleCat.of ℤ ℤ` is not
`rfl`.  So for `X : Type u` the coefficient object must be an object of `ModuleCat.{u} ℤ`, which the
literal `ℤ` is not for `u > 0`, and **every** polymorphic form (`ULift.{u} ℤ`,
`AddCommGrpCat.of (ULift ℤ)`, `ModuleCat.{max u v}`) changes the `u = 0` object to `ULift.{0} ℤ` —
which the protocol ("statement at `u = 0` unchanged") forbids, independently of the four consumer
rewrites cited above.  Mathlib's own precedent for polymorphic ℤ coefficients is exactly `ULift.{w} ℤ`
(`Sheaf.H`).  The protocol-clean route is therefore **a new polymorphic `chains` beside the pinned
one plus a `u = 0` comparison isomorphism — an addition, not a lift**, correctly outside this packet.
The same verdict applies to `SingularChains.singularComplex` and, by consequence, to `Coproduct.lean`.

### `SingularChains.singularComplex` (`AlgebraicTopology/SingularHomology/Chains.lean`)

The same obstacle in the homology-side interface: `(TopCat.toSSet.obj (TopCat.of X)).chainComplex
(ModuleCat.of ℤ ℤ)` with `(X : Type)`, and `chainLift` / `chainMap_ext` reading off the value at
`1 : ℤ`.  It forces the **9 `.{0}` occurrences on 8 lines (corrected; the receipt's "8 pins" is a line
count, while the headline 1,024 → 320 are occurrence counts)** of
`AlgebraicTopology/SingularHomology/Coproduct.lean`
(`ModuleCat.{0} ℤ` in `singularChainsFiniteBiproducts`, `HasFiniteBiproducts`) — the packet's
"Mathlib `ModuleCat.hasLimits` at `max v w`" item: the coproduct instance is not what pins the
file, the literal-`ℤ` chain complex is.  Skipped for the same reason.

### `Cohomology/SphereTwo.lean`

Lifted, built, and reverted.  `hasExt_of_enoughInjectives.{0,0,1}` lifts to `.{u,u,u+1}` without
trouble, but the theorem's hypothesis is a homeomorphism `B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ
(Fin 3)) 1`, and

```
Lib/Topology/Sheaves/Cohomology/SphereTwo.lean:64:4: Type mismatch
  SphereTwo.hasCoveringDimensionLE_two_of_homeomorph ?m.127
has type
  ∀ (U : ?m.128 → Opens ?m.125), IsOpenCover U → ∃ κ V x, IsOpenCover V ∧ OpenCover.MultiplicityLE V (2 + 1)
but is expected to have type
  ∀ (U : ι✝ → Opens ↑B), IsOpenCover U → ∃ κ V x, IsOpenCover V ∧ OpenCover.MultiplicityLE V (2 + 1)
```

`TopologicalSpace.SphereTwo.hasCoveringDimensionLE_two_of_homeomorph` goes through
`HasCoveringDimensionLE.of_homeomorph {X Y : Type u}`, one universe for both spaces, and the
sphere is in `Type 0`.  This is the obstacle round 7 already recorded for
`Lib/Topology/Dimension/SphereTwo.lean`; widening it needs a cross-universe transport lemma in
`Covering.lean`, i.e. a proof rewrite.  The file's 23 pins stay.

### `Lib/AlgebraicTopology/Hurewicz/Degree1.lean`

Its single `.{0}` is inside the module docstring, explaining the `ModuleCat.{0} ℤ` coefficient
pin; it is accurate and untouched.

## 4. Lost names

None.  `envdiff` reports `lost 682 added 681 of which source declarations: 0 0`.  All 682/681 are
auxiliary proof constants (`_proof_n`, `_eq_n`), explicitly "not judged" by the tool.  One of them,
`CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationIso._proof_5`, is lost without
a replacement: the universe-explicit form of `higherDirectImageResolutionStalkIso` in
`HigherDirectImageSheafification.lean` produces one side goal fewer.  No source name moved module.

## 5. Builds

```
lake build Lib                                  Build completed successfully (9150 jobs).  rc=0
lake build Solution S6Shortcuts S6 Challenge    Build completed successfully (9189 jobs).  rc=0
lake build Lib.AxiomAudit                       Build completed successfully (9150 jobs).  rc=0
python3 scripts/lib_stock_census.py --check     rc=0
```

`Lib.AxiomAudit` reports only `propext`, `Classical.choice`, `Quot.sound` (1724 declarations with
all three, 115 with `propext, Quot.sound`, 15 with `propext`, 1 with `propext, Classical.choice`).

## 6. Envdiff

`Lib/reports/round-8/pins/envdiff.json` (copy of the receipt file).

```
constants before 38593 after 38592 (keys 38491 38490 )
lost 682 added 681 of which source declarations: 0 0 ; names with changed type 681 of which source: 398
auxiliary lost/added/changed (not judged): 682 681 283
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

All 398 changed source types are the universe generalisations of this packet and their dependents.
The largest groups are `FibreStalkEvaluation/Neighborhood` (25), `ResolutionTransgression` (24),
`OpenRestriction/Cohomology` (22), `OpenEmbeddingCohomology` (17), `ResolutionCohomologyPresheaf`
(16), `ResolutionPostnikov` (14), `NestedOpenCohomology` (14).  **(corrected)** of the 398 changed-type source names, **40 live in modules this branch did not
edit**, in three groups, not two: `SingularCochainSheaf/*` (29 names), `Cohomology/SphereTwo`
(2 names) and — omitted from the receipt as first written — `ConstantProductH1` (1),
`ConstantProductH1Comparison` (1), `ConstantProductH1FibreIndependence` (1),
`ConstantProductPositiveFibreIndependence` (5) and `ConstantSheafH1` (1), **9 names**.  All three
groups are dependents whose statements mention a lifted declaration; those files themselves were not
edited (they are listed in §3 as staying pinned, so the omission is only in this reconciliation).

## 7. Commits

```
feba6a42 Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean: lift cohomologyAddCommGroup to .{u}
63bdbb61 Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1.lean: lift the H1 acyclic-resolution interface to .{u}
f5a50893 Lib/Topology/Sheaves/H1Vanishing/Flasque.lean: lift flasque H1 vanishing to .{u}
6973220d Lib/Topology/Sheaves/OpenEmbeddingCohomology.lean: lift the open-embedding cohomology comparison to .{u}
ccf092a2 Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean: lift open-restriction cohomology to .{u}
b457a9fe Lib/Topology/Sheaves/FiniteClosedPushforward/Exact.lean: lift the finite-closed pushforward exactness to .{u}
85312af3 Lib/Topology/Sheaves/Cohomology: lift the files released by cohomologyAddCommGroup
f59653c5 Lib/Topology/Sheaves: lift ConstantSheafCohomology.pullback and the finite-closed cluster
6f4277d9 Lib/Topology/Sheaves/OpenRestriction: lift the nearby-restriction germ chokepoint to .{u}
a140e4b1 Lib/CategoryTheory/Sites/Leray: lift the Leray cluster to .{u}
```

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r8-pins.md` (ACCEPT WITH FINDINGS; the work is sound —
the reviewer's whole-diff residue check, normalising universe annotations and comparing removed
against added lines per file, leaves over all 54 `.lean` files only the `universe u` lines in 46
files, the seven `(C := AbelianSheaf Y)` insertions and one dropped docstring word, so **every
`u = 0` instance is literally the old statement**; nothing deleted, no hypothesis added, the merge
preserved every lift on what survived; the headline 1,024 / 99 → 320 / 48 reproduces exactly).
These corrections are to this receipt's text only; no Lean file was changed by them.

1. **Chokepoint 8's mechanism was wrong (finding 1), corrected in the §1 table.**  The "invisible
   pin" is real, but it is **not** a bare-binder effect and **not** anything to do with
   `autoImplicit`: bare binders elaborate as universe parameters.  What pins
   `germ_stalkIso_hom_nearbyRestrictionUnit` is `TopCat.Presheaf.germ`'s
   `[Limits.HasColimits AddCommGrpCat.{?v}]` instance argument, resolved while `?v` is still a
   metavariable and assigned `?v := 0`.  Consequence for tooling: a `.{0}` grep census cannot find
   this class of pin, and "bare `TopCat`/`AddCommGrpCat` ⇒ pinned" is false in both directions
   (three bare occurrences at head are fully polymorphic).  The detector that works is `#check` with
   `pp.universes true`; a census script that dumps universe parameters per declaration — the envdiff
   dumps already carry the types — would have found this chokepoint without a round-7 build failure,
   and would *prove* "every declaration is now `.{u}`" instead of asserting it.  The corrected
   mechanism also goes to `lean-agent-ide` (`spec/dump.md`, `Lib/reviews/REVIEW-7-8.md` §5).

2. **§3 counts (finding 2), corrected in place.**  `SingularCochainSheaf/*` has **32** files with
   pins (207 pins), not 26; the set of files §3 lists as staying pinned carries **280** pins (287
   with `SingularCochains.lean`'s own 7), not "271 of the 320"; and `Coproduct.lean` has 8 pinned
   *lines* but **9** occurrences, while the headline 1,024 / 320 are occurrence counts.  None of this
   affects soundness — it affects a reader's ability to reconcile 320.  State the grep once and use
   it throughout.

3. **§3's `ULift ℤ` obstruction is also a protocol obstruction (added to §3).**  The receipt argued
   from four consumer proofs that read the literal `1 : ℤ`.  Independently of those, no
   `ModuleCat.{u} ℤ` object has carrier literally `ℤ` for `u > 0`, so every polymorphic form changes
   the `u = 0` object to `ULift.{0} ℤ` — which the protocol forbids.  The clean route is an
   **addition**: a polymorphic `chains` beside the pinned one, plus a `u = 0` comparison
   isomorphism.  Correctly outside this packet either way.

4. **"They are the only proof-text edits in this packet" (finding 4), corrected in §2.**  Four of
   the seven `(C := AbelianSheaf Y)` insertions are inside theorem *statements*
   (`ResolutionTransgression.lean` l.181–185, 217–221, 231–235, 267–271).  `C` is determined by
   `pushedResolution f I`, so the elaborated term and the `u = 0` statement are unchanged; only the
   sentence was inaccurate.

5. **§6 envdiff reconciliation omitted a third group (finding 3), corrected in §6.**  Of the 398
   changed-type source names, 40 live in modules this branch did not edit: `SingularCochainSheaf/*`
   (29) and `SphereTwo` (2), both named, **plus 9 in the five `ConstantProduct*`/`ConstantSheafH1`
   files**, which were not.  All are dependents of lifted declarations.
   (`envdiff.json`'s `changed_type_proof_naming` list carries names only; adding the module, as the
   `lost`/`added` entries have, would make this reconciliation checkable directly.)

6. **"One commit per chokepoint" holds for chokepoints 1–6 only (finding 5).**  Chokepoint 7
   (`ConstantSheafCohomology.pullback`) shares `f59653c5` with five consumer files, and chokepoint 8
   shares `6f4277d9` with `StalkCriterion.lean`.  The §1 table makes this visible; the sentence
   should not have been unqualified.

7. **Two packet items were already clean and the receipt does not say so (finding 6).**  The packet
   lists `TopCat.LocalPredicate` over ℂ (`Analysis/Complex/SquareRoot.lean`, "1 pin") and "`HasExt`
   pinned to the hom universe in `cochainTransgression`".  At the base both files have **zero**
   `.{0}` (`Ext.{v}` in `cochainTransgression` is a universe parameter, not a pin).  Both items were
   stale in the packet, and a receipt should say which of its inputs it found to be wrong rather
   than pass over them.

8. **One location was wrong (raised by the packet-08 reviewer), corrected in the §1 table.**
   `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv` lives in `FiniteClosedPushforward.lean`,
   not `FiniteClosedPushforward/Exact.lean`, and was lifted by round-7 packet 08; `Exact.lean`'s own
   pin was its `variable {X Y : TopCat.{0}}`, which `b457a9fe` lifted.  The two receipts now agree.
