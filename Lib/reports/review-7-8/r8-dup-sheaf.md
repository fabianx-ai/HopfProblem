# Review of Lib/reports/round-8/dup-sheaf/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — all 28 deletions have the named twin with the same statement
(nine of them literally the `n = 0` / `n = 1` instance, verified by elaboration; no hypothesis
added anywhere, no metrizability introduced), the three unifications are definitional (`rfl`),
the rename map is complete and correctly oriented; the findings are receipt-completeness nits
(three envdiff `PROOF-NAMING` names and the `AxiomAudit.lean` edit unmentioned) and one
inaccurate docstring.

Branch `r8/dup-sheaf`, base `4e15a034`, merge `124b7f25`; commits `e8161fd1`, `910fe5d5`,
`0d8e2b19`, `a093890f` (4, as stated). Twins were read at head `39f1d12b`; none of the twin
files (`GlobalSections.lean`, `Sheafification.lean`, `DependentFunctionSheaf.lean`,
`ConstantPushforward/GlobalSections.lean`, `GlobalUnitPositive.lean`, `GlobalUnitPredicates.lean`,
`GlobalKernelSmall.lean`, `LocalExactPositive.lean`) was touched by a later branch
(`git log 124b7f25..39f1d12b -- <files>` is empty). Scratch elaboration:
`/home/goblin/.claude/jobs/06995e68/tmp/review-pass/r8-dup-sheaf/Check.lean` (1 `lake env lean`
run, exit 0, all `example`s and `rfl`s accepted).

## Findings

1. `[incomplete]` **Envdiff `PROOF-NAMING` list has five names, the receipt explains two.**
   `envdiff.json` → `changed_type_proof_naming` =
   `TopCat.SheafH1.globalSectionsFunctor`, `…globalSectionsFunctor_additive`,
   `TopCat.SheafH1.h0GlobalIso`, `TopCat.SingularCochainSheaf.cochainPullbackComplex`,
   `…cochainPullbackComplex_f`. The receipt ("Two further names … changed type as the universe
   generalisation") accounts only for the first two. The other three are downstream of the same
   move (`h0GlobalIso` names `globalSectionsFunctor`; `cochainPullbackComplex` names
   `complexSheaf`, which unfolds through the renamed `sheafification`), so they are harmless, but
   "reconciled line by line" requires listing them. Should be added to the Envdiff section.

2. `[incomplete]` **`Lib/AxiomAudit.lean` was edited (+14/−~30 `#check`/`#print axioms` lines,
   119 diff lines) and the receipt never says so.** The edit is correct — every removed line is a
   deleted name or a renamed one re-added under the new name, `SmallKernelGlobal`/`smallKernelGlobal`/
   `initialComplex_exact` move to their new module sections, the two new modules get sections —
   but a reader of the receipt sees only "`lake build Lib.AxiomAudit done 0`" and would not know
   the audit file itself changed. One sentence in the Build section would fix it.

3. `[docstring]` **`GlobalUnitPredicates.lean` module docstring names the wrong module for one
   predicate.** It says the four conditions "are discharged in `GlobalKernelSmall.lean` and
   `BarycentricSmallChains.lean`". `GlobalKernelLocallySmall` and `SmallKernelGlobal` are
   (`GlobalKernelSmall.lean:137,142`), `HasSmallChainEquivalences` is
   (`BarycentricSmallChains.lean:34`), but `GlobalUnitSurjective` is discharged by
   `globalCochainUnit_surjective` in `SingularCochainSheaf/GlobalSections.lean:82`, which
   `GlobalKernelSmall.lean` does not contain. The receipt advertises this docstring ("a docstring
   saying where each is discharged"). Fix the sentence.

4. `[nit]` **`FunctionSheaf.forgetIso` twin has a different (definitionally equal) target.**
   Deleted: `presheaf X A ⋙ forget AddCommGrpCat ≅ TopCat.presheafToType X A`.
   Twin at `fun _ => A`: `… ≅ TopCat.presheafToTypes X (fun x => (fun _ => A) x)`.
   `TopCat.presheafToType X A = TopCat.presheafToTypes X (fun _ => A)` is `rfl` (checked in the
   scratch file; Mathlib's `g ∘ i.unop` vs `fun x => g (i.unop x)`), so the twin is the same
   proposition up to unfolding — but it is not "the same statement" syntactically as the table
   implies. No consumer used `forgetIso` outside `isSheaf`. Worth a footnote, nothing more.

5. `[nit]` **Receipt says `CategoryTheory.Sheaf.Leray.integralSheaf` lived in
   `Sites/Leray/ResolutionTransgression.lean` — correct — but `Leray.sheafification(_additive)`
   are not located in the receipt at all.** They were in
   `Sites/Leray/HigherDirectImageSheafification.lean:116,121` (base). Purely a locating aid.

Nothing `[unsound]` or `[wrong receipt]` was found. In particular the specific worry in the
assignment — that a metrizability-free degree-one statement might have been replaced by a
metrizability-needing positive-degree one — does not materialise: none of the nine `_succ`/general
twins carries `[MetrizableSpace X]`; the metrizability-needing declarations
(`constantSheafGlobalIso`, `constantSheafCohomologyIsoSingular`, `resolution_isAcyclic`) are
exactly the ones the receipt refused to use as twins (items 1–2 of "Recorded and left").

## The 28 deletions, one by one

Deleted statements from `git show 4e15a034:<path>`; twins from head. "Instance" = literally the
twin applied at the stated argument, checked by an `example` in the scratch file (E) or by
reading (R).

**Item 7 (9).** All nine lived in `GlobalUnitH1.lean`, `GlobalUnitH1Criterion.lean`,
`LocalExactH1.lean`, `GlobalKernelSmall.lean` at `X : TopCat.{0}`, `A : AddCommGrpCat.{0}`.

| deleted (base statement) | twin (head statement) | check |
|---|---|---|
| `globalCochainComparison_homology_isIso_one [NormalSpace X] [ParacompactSpace X] (hsmall : HasSmallChainEquivalences X) : IsIso (homologyMap (globalCochainComparison X A) 1)` | `globalCochainComparison_homology_isIso_succ [NormalSpace X] [ParacompactSpace X] (hsmall) (n) : IsIso (homologyMap … (n+1))` at `n = 0` | E, same |
| `globalUnitSurjective [NormalSpace X] [ParacompactSpace X] (n) : GlobalUnitSurjective X A n` (body: `globalCochainUnit_surjective X A n`) | `globalCochainUnit_surjective [NormalSpace X] [ParacompactSpace X] : Function.Surjective (globalCochainUnit X A n)` (`GlobalSections.lean:82`; `GlobalUnitSurjective` is `def … := Function.Surjective …`) | E, same |
| `complexSheaf_exactAt_one (hLC : LocallyContractibleSpace X) : (complexSheaf X A).ExactAt 1` | `complexSheaf_exactAt_succ (hLC) (n) : (complexSheaf X A).ExactAt (n+1)` at `0` | E, same |
| `exists_restriction_primitive_one` (private; `c : … .X 1`, `hc : d 1 2 c = 0` ⊢ `∃ V ≤ U, x ∈ V, b : (complex V A).X 0, d 0 1 b = (presheaf X A 1).map … c`) | `exists_restriction_primitive_succ … (n)` (private, `LocalExactPositive.lean:69`) at `0` | R, same |
| `SmallKernelGlobalOne : Prop := ∀ U, (∀ x, x ∈ U x) → ∀ phi : … .X 1, (cochainRestriction A …).f 1 phi = 0 → globalCochainUnit X A 1 phi = 0` | `SmallKernelGlobal (n) : Prop` (`GlobalUnitPredicates.lean`) at `1` | E (`rfl` against the pasted body) |
| `smallKernelGlobalOne : SmallKernelGlobalOne X A` | `smallKernelGlobal (n) : SmallKernelGlobal X A n` at `1` | E |
| `globalCochainComparison_cycle_lift_one (hunitOne : GlobalUnitSurjective X A 1) (hkernelTwo : … 2) (hkernelReverseOne : SmallKernelGlobalOne X A) (hsmall) (s : (globalCochainComplex X A).X 1) (hs : d 1 2 s = 0) : ∃ phi, d 1 2 phi = 0 ∧ globalCochainUnit X A 1 phi = s` | `…cycle_lift_succ (n) (hunit : … (n+1)) (hkernelNext : … (n+2)) (hkernelReverse : SmallKernelGlobal X A (n+1)) …` at `0` | E |
| `globalCochainComparison_boundary_detect_one (hunitZero : … 0) (hkernelOne : … 1) (hsmall) (phi : .X 1) (hphi : d 1 2 phi = 0) (s : .X 0) (hs : d 0 1 s = globalCochainUnit X A 1 phi) : ∃ psi : .X 0, d 0 1 psi = phi` | `…boundary_detect_succ (n) …` at `0` | E |
| `globalCochainComparison_homology_isIso_one_of_small_chains (hunitZero) (hunitOne) (hkernelOne) (hkernelTwo) (hkernelReverseOne : SmallKernelGlobalOne X A) (hsmall) : IsIso (homologyMap … 1)` | `…_succ_of_small_chains (n) … (hkernelReverse : SmallKernelGlobal X A (n+1)) …` at `0` | E |

The `_succ` statements themselves were not changed by the branch (`git diff 4e15a034 124b7f25^2 --
GlobalUnitPositive.lean` only removes the two moved declarations; `LocalExactPositive.lean` only
gains the moved `initialComplex_exact`/`exists_restriction_constant` and the survivor's spelling of
`sheafification`). `#print axioms` on `…_isIso_succ` and `complexSheaf_exactAt_succ`:
`propext, Classical.choice, Quot.sound`. Consumers `ConstantSheafH1.lean`,
`ConstantProductH1FibreIndependence.lean`, `ResolutionH1.lean` changed only by appending `0` /
switching the import — no new instance arguments (receipt: "they already had the instances it
needs" — verified).

**Item 8 (9).** `FunctionSheaf.lean` (base, 109 lines) vs `DependentFunctionSheaf.lean` (head).
All nine (`presheaf`, `presheaf_obj`, `presheaf_map_apply`, `forgetIso`, `isSheaf`, `sheaf`,
`extendByZero`, `restrict_extendByZero`, `sheaf_isFlasque`) are line-for-line the dependent
version with `A x.1` in place of `A`, same universe `u`, same `@[simp]` attributes (the three
`@[simp]` removals in the hygiene grep are the deleted file's; the twins keep `@[simp]`), same
`instance` for `sheaf_isFlasque`. Definitional identity at the constant family: the scratch file
re-declares the deleted `presheaf` verbatim and proves
`FSpresheaf X A = TopCat.DependentFunctionSheaf.presheaf X (fun _ => A) := rfl` and
`(DependentFunctionSheaf.presheaf X (fun _ => A)).obj U = AddCommGrpCat.of (U.unop → A) := rfl`
— so consumers' `rfl`-style proofs (`zeroCochainEvaluationHom`, `zeroCochainEvaluationInv`, the
`AddCommGrpCat.ofHom (zeroCochainEvaluate U.unop A)` fields) still typecheck, as the branch diff
of `DegreeZeroFunctions.lean` / `DegreeZeroAcyclic.lean` confirms (name substitution only, no proof
edits). `forgetIso`: see finding 4. Importers of `FunctionSheaf` at base: exactly the two consumers
plus `Lib.lean`/`AxiomAudit.lean` (`git grep -l FunctionSheaf 4e15a034`).

**Item 9 (10).**

| deleted (base) | twin | check |
|---|---|---|
| `TopCat.SheafH1.unitSheaf : abbrev := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))` (`X : TopCat.{0}`) | `TopCat.ConstantSheaf.integralSheaf (X : TopCat.{u}) : abbrev := sheaf X (AddCommGrpCat.of (ULift.{u} ℤ))`, `sheaf` now `@[reducible] def := (constantSheaf …).obj A` | E: `integralSheaf X = (constantSheaf …).obj (of (ULift ℤ))` by `rfl` **and** by `with_reducible rfl` |
| `CategoryTheory.Sheaf.Leray.integralSheaf (X : TopCat.{0}) : abbrev := TopCat.ConstantSheaf.integralSheaf X` | same survivor | R: it *was* the survivor |
| `TopCat.SheafH1.constantIntegerSheaf` (private abbrev, same body as `unitSheaf`) | same survivor | R |
| `TopCat.SheafCohomology.constantIntegerSheaf` (private abbrev, same body) | same survivor | R |
| `TopCat.SheafH1.globalSectionsFunctor (X : TopCat.{0}) : def := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)` + `_additive` instance (`map_add := by intros; rfl`) | `TopCat.Sheaf.globalSectionsFunctor (X : TopCat.{u})`, character-identical body at `u`; `_additive` identical | R; rename-map entry, universe lift `{0}→{u}` stated in the receipt; at `u = 0` literally the old statement |
| `TopologicalSpace.OpenCover.SetOpenCover.sheafGlobalSectionsFunctor (X : TopCat.{u})` + `_additive` | same survivor | R: character-identical body |
| `TopCat.Sheaf.FiniteSupport.topEvaluation (X : TopCat.{u}) := TopCat.Sheaf.forget AddCommGrpCat X ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)` | same survivor | E: `globalSectionsFunctor X = forget ⋙ evaluation.obj (op ⊤)` by `rfl`; consumer `globalSectionsIsoOfSkyscraperBiprodIso` changed by name substitution only |
| `TopCat.SheafificationPushforward.sheafification (X : TopCat.{u}) : abbrev := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` | `TopCat.Sheaf.sheafification`, identical body | E: `rfl` |
| `CategoryTheory.Sheaf.Leray.sheafification` (same body, `HigherDirectImageSheafification.lean:116`) + `_additive` | same survivor + `TopCat.Sheaf.sheafification_additive` (identical `inferInstanceAs` body) | R |

`TopCat.SingularCochainSheaf.sheafification(_additive)` is the moved copy (rename-map entry, not
a deletion) — consistent with envdiff's "2 `…SingularCochainSheaf.Sheaf → …Sheaves.Sheafification`"
module move.

## Claims checked

| claim | status | how |
|---|---|---|
| 4 commits, one per item + receipt; messages describe the commit; trailers present | verified | `git log 4e15a034..124b7f25^2`; `git show -s --format=%B` ×4 (`Co-Authored-By`, `Claude-Session` on all four) |
| 28 lost source names = exactly the three tables | verified | python over `envdiff.json`: lost∖added = 48 names, 20 are `_proof_n`/`eq_1` auxiliaries, the remaining 28 are exactly the 10+9+9 listed |
| "No source name is added … the 13 added-only keys are all `._proof_n`" | verified | same script: 13 added-only, all `._proof_N` |
| 78 changed-type source names; every one a survivor respelling | verified for the names, causes sampled | all 78 names listed; grep of the whole branch diff after filtering the survivor/deleted tokens leaves only the moved bodies and the two consumer `0` arguments (see below); dumps carry only type hashes so the 35/21/16/5/1 split could not be recomputed exactly |
| `PROOF-NAMING`: "two further names" | **refuted (five)** | finding 1 |
| constants 38593 → 38558 | verified | `envdiff.json["constants"]` |
| module moves 3/1/1/2/2, ambiguous 0 | verified | `envdiff.json["moves"]`, `["ambiguous"]` |
| Rename map: 10 entries, direction after→base | verified | `rename.txt`; every left name present at head and every right name absent from `*.lean` at head (`git grep` of all deleted/old names outside `Lib/reports` returns only the unrelated `cochainRestriction_homologyMap_isIso_one`); MERGE.md §rename agrees on the orientation |
| `unitFreeTopIso` is not a duplicate | verified | base `RepresentedOpenProjectiveDimension.lean:81`: `unitSheaf X ≅ freeOpen ⊤`, an iso, not the sheaf |
| `TopCat.ConstantSheaf.sheaf` made `@[reducible]` for `Sheaf.H` | verified (reducibility) / not tested (necessity) | branch diff of `ConstantPushforward.lean`; Mathlib `Sites/SheafCohomology/Basic.lean:59` `abbrev H n := Ext ((constantSheaf J AddCommGrpCat).obj (of (ULift ℤ))) F n` as quoted; `with_reducible rfl` passes at head |
| `GlobalSections` (`ShortExactDegreeZeroSections.lean`) left because it is a `Type` abbrev | verified | head line 40: `abbrev GlobalSections (F) := (F.obj.obj (op ⊤) : Type u)` |
| `freeOpenFunctor` identical three times, out of packet | verified | `git grep` at head: three `abbrev freeOpenFunctor` with the same 3-line body; packet item 9 text names `presheafToSheaf aliased three times`, not `freeOpenFunctor`. Leaving it is within scope; the record is accurate |
| Item 8: "two consumers", "line-for-line identical proofs" | verified | `git grep -l FunctionSheaf 4e15a034`; side-by-side read |
| Not done 1: `constantSheafGlobalH1Iso` needs only `hLC`; `constantSheafGlobalIso … 0` needs `[MetrizableSpace X]`; `resolution_isAcyclic` uses `isFlasque_of_metrizable`; `ResolutionPositive.lean` imports `GlobalResolutionH1.lean` | verified | head `GlobalResolutionH1.lean:53`, `ComparisonPositive.lean:41–42`, `ResolutionPositive.lean:12,85–91` |
| Not done 2: `h1Comparison` metrizability-free; `constantSheafCohomologyIsoSingular` needs it | verified | head `ComparisonH1.lean:36–37`, `ComparisonPositive.lean:65–66` |
| Not done 3: `nullhomotopic_pullback_closed_one` = `…_succ … 0`, unused after the packet | verified | statements compared (`PrimitivesH1.lean:328`, `PositivePrimitives.lean:137`); `git grep` at head: only its own file and `AxiomAudit` |
| Not done 4: `hasSmallChainEquivalences_barycentric` for every `X : TopCat.{0}` | verified | `BarycentricSmallChains.lean:34` |
| Files deleted/created as stated; `GlobalUnitH1Criterion.lean` → `GlobalUnitPredicates.lean` | verified | `git diff -M --summary` (git sees delete+create; content is the four predicates) |
| `Lib.lean` lists the two new modules, drops the deleted ones | verified | branch diff of `Lib.lean`; still present at head (`Lib.lean:271–272`) |
| No `Hopf` import in `Lib` | verified | `git grep "import Hopf" 39f1d12b -- Lib/`: hits only in `Lib/docs/*.md`, `Lib/reports/*.md`, log `.txt` |
| Hygiene | verified | branch diff: no `sorry`, `axiom`, `maxHeartbeats`, `unsafe`, `native_decide`; one `@[reducible]` added (documented); `noncomputable section` lines are the two new modules' preambles; `private` removed only with the deleted files; no `@[simp]` change on surviving declarations |
| `AxiomAudit` axioms only `propext, Classical.choice, Quot.sound` | verified for the twins | `#print axioms` on four twins in the scratch file |

Residual-diff check: filtering the whole branch diff (minus deleted/new files and reports) for
changed lines not containing any survivor/deleted token leaves only: the bodies of the deleted
definitions, `variable (X)`→`variable {X : TopCat.{0}}` in `AcyclicResolutionH1.lean`, the
appended `0` arguments in the two H¹ consumers, `X A 1 U`→`X A n U` in `smallKernelGlobal`,
and the rewritten docstring sentence in `ProjectiveDimension.lean` (which now correctly says
`H F a` is definitionally `Ext (TopCat.ConstantSheaf.integralSheaf X) F a`).

## Not checked

* The counterfactual "without `@[reducible]` the `calc` in `hom_surjective_of_global_surjective`
  no longer elaborates" — would need a non-reducible copy of the whole `Ext`-side setup in a
  scratch file; only the positive direction (it is reducible now and `with_reducible rfl` sees
  through it) was tested.
* The exact 35/21/16/5/1 cause split of the 78 changed types: the dumps referenced by
  `envdiff.json` hold only `typeHash`, so I could not diff types; I relied on the residual-diff
  filter above, which shows no changed line that is not a survivor respelling.
* The three universe-lifted spellings at head of `integralSheafFreeTopIso`,
  `integralSheaf_hasProjectiveDimensionLT_iff_*` (`TopCat.{u}`): those lifts came from `r8/pins`
  and the merge, not this branch (on the branch they are still `TopCat.{0}`); not this receipt's
  claim.
* `lake build` results are taken from the receipt; I did not rebuild (forbidden), but the
  integration tree at the same head elaborated the scratch imports cleanly.

## Tool notes

* `envdiff.json` should carry the before/after *types* (or the pretty-printed signatures) for
  `changed_type_*` entries, not only hashes; then "every changed type is a respelling" would be
  checkable mechanically instead of by a diff filter.
* The receipt's Envdiff section should paste the `changed_type_proof_naming` list verbatim (five
  names) rather than summarise it ("two further names") — the discrepancy in finding 1 is exactly
  the kind of thing a verbatim paste prevents.
* The deletion tables would be faster to verify with the base file path *and line* for each
  deleted declaration and the head path:line for the twin; item 9's `Leray.sheafification` had to
  be located by `git grep`.
* Listing every edited non-library file (`Lib.lean`, `Lib/AxiomAudit.lean`) in the receipt would
  save a reviewer the "why is `AxiomAudit.lean` in the diff stat" detour.
