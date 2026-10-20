# Review of Lib/reports/round-7/packets/RECEIPT-01.md

**Verdict: ACCEPT WITH FINDINGS** — the work is sound (no statement weakened, no hypothesis added, every universe lift is the literal old statement at level 0, hygiene clean), but the receipt's arithmetic on universe pins is wrong in three places, one envdiff explanation names the wrong declaration, no per-packet `envdiff.json` exists in the repo, and two added textbook references contain literal `x` placeholders for the exercise number.

Reviewed: branch `r7/packet-01`, `git log 9552305f..c214c907^2` (56 commits incl. the receipt commit), `git diff 9552305f c214c907^2` (54 `.lean` files + receipt), compared with head `39f1d12b`. One scratch elaboration in `/home/goblin/hopf-lib-integration` (`review-pass/r7-packet-01/Check.lean`).

## Findings

1. **[citation] Placeholder exercise numbers shipped verbatim.** Two `## References` blocks copy the audit's "x" placeholder into the library and both survive at head:
   - `Lib/Algebra/Homology/DerivedCategory/Ext/CochainTransgression.lean:27` (commit `87b25ffb`): `[weibel94], Exercise 1.3.x and §2.4`
   - `Lib/Algebra/Homology/DerivedCategory/Ext/ExactFunctorComparison.lean:27` (commit `acb335e4`): `[weibel94], Exercise 2.4.x.`
   These are not references. Replace with the actual number or drop the exercise and keep the section (§1.3 / §2.4).

2. **[citation] "Theorem 2.4.3" of Weibel is (to my knowledge) an exercise, not a theorem.** `AcyclicResolutionH1.lean`, `AcyclicResolutionH1ExactFunctor.lean`, `AcyclicResolutionH2H3.lean` (commits `9b68d615`, `2e469381`, `a6669d94`) cite "Weibel, Theorem 2.4.3" for "acyclic resolutions compute derived functors". In Weibel §2.4 the numbered theorems are 2.4.6/2.4.7 (δ-functor properties); the F-acyclic-resolution statement is **Exercise 2.4.3**. The parallel citation Hartshorne III, Prop. 1.2A (in `AcyclicResolutionH1.lean`) is the correct textbook theorem for this result. I am fairly, not fully, sure of the Weibel numbering; someone with the book should confirm. Fix: "Exercise 2.4.3" or cite Hartshorne III.1.2A alone.

3. **[wrong receipt] Universe-pin counts do not add up.** Receipt: "119 of 143 generalised, 24 left". Actual (`grep -o '\.{0}'` per file, base vs branch):
   - `Ext/InjectiveResolutionHomology.lean`: receipt "6 → 0", actual **7 → 0** (the packet list itself says ×7).
   - `DualEvaluation/HomeomorphCoordinates.lean`: receipt "3 → 0", actual **4 → 0** (packet says ×4).
   - `SingularCochains.lean`: receipt "35 → 7", actual **36 → 7** (packet says ×36).
   - Totals: 143 → 27 in the 59 files, i.e. **116 lifted, 27 left**. The receipt's own per-file "forced" column already sums to 7 + 13 + 6 + 1 = 27, contradicting its "24 left". Nothing was mis-lifted; the numbers are just wrong.

4. **[wrong receipt] Wrong explanation of the Generators envdiff entry.** Receipt: "`…SingularCochains.Generators` … 1 each … the `Cochains` abbreviation now mentions the polymorphic `chains`". `chains` was **not** generalised (still `ChainComplex (ModuleCat.{0} ℤ) ℕ` at head, receipt itself lists it as forced) and `Cochains` is unchanged. The declaration whose type changed in `Generators.lean` is `pullback_simplex`, because it mentions `pullback`, which is now `pullback.{w}` — confirmed by `Lib/reports/round-7/envdiff-merged-d950428a.json` (`lost: AlgebraicTopology.SingularCochains.pullback_simplex` in module `…Generators`) and by `#check @pullback_simplex` at head (`pullback.{0} A f`).

5. **[incomplete] No `envdiff.json`/`.txt` for this packet exists in the repository.** The brief says the diff is "beside the receipt"; `Lib/reports/round-7/packets/` holds only the ten receipts and ten packet lists. The receipt quotes the tool output (407 lost/added, 314 changed source types, per-module table) but none of it is checkable line by line. The only artefact is the round-wide `envdiff-merged-d950428a.json` (1438 changed, all packets together), from which I could spot-check only module membership (finding 4). The per-module counts (67, 35, 20, 19, 17, 14, 10, 8, 2, 28, 90) are therefore **unverified**.

6. **[incomplete] `moduleDual`/`dualComplex` now land in `AddCommGrpCat.{max u w}`, not `.{w}`.** The receipt says only "`A : AddCommGrpCat.{w}` over `ModuleCat.{u} ℤ`". At head:
   ```
   moduleDual.{u_1,u_2} : AddCommGrpCat.{u_2} → (ModuleCat.{u_1} ℤ)ᵒᵖ ⥤ AddCommGrpCat.{max u_1 u_2}
   dualComplex.{u_1,u_2} : AddCommGrpCat.{u_2} → ChainComplex (ModuleCat.{u_1} ℤ) ℕ → CochainComplex AddCommGrpCat.{max u_1 u_2} ℕ
   ```
   This is the correct (forced) level, and `max 0 w = w` so `complex X A : CochainComplex AddCommGrpCat.{w} ℕ` and every level-0 instance is literally the old statement. But a downstream user feeding `K : ChainComplex (ModuleCat.{v} ℤ) ℕ` with `v ≠ 0` gets a cochain complex in a different universe than `A`; the receipt should say so.

7. **[docstring] `rectangleHorizontalVertical` / `rectangleVerticalHorizontal` docstrings contradict the file's own naming.** `PathValue.lean` (commit `55607666`) defines `squareHorizontal F s := t ↦ F (s, t)` ("the horizontal path", per its docstring) and `squareVertical F t := s ↦ F (s, t)`. Then
   ```
   /-- The path from `(s, a)` to `(t, b)` in the square that goes vertically first and then horizontally. -/
   def rectangleHorizontalVertical (s t a b) := ((squareHorizontal id s).subpath a b).trans ((squareVertical id b).subpath s t)
   ```
   The first leg is `squareHorizontal`, so under the file's convention it goes *horizontally* first — as the name says. The docstring says the opposite (and symmetrically for `rectangleVerticalHorizontal`). Either fix the two docstrings or say explicitly that "horizontal" in these two names means the first coordinate. Low severity: the theorems are stated on the definitions, not the prose.

8. **[docstring] `DeterminingFamily.commute_all_of_lattice_image_eq_zpow` docstring understates the hypothesis.** Docstring: "`φ … have image contained in the powers of the single element `c = φ (ofAdd ![1, 2, -4, 0])`". The actual hypothesis is the specific formula `hpow : ∀ z, φ (ofAdd z) = c ^ z 0` (exponent = the 0-th coordinate). "Contained in the powers of `c`" is a strictly weaker paraphrase; a reader would expect the theorem to hold under the weaker hypothesis. Nit.

9. **[nit] Minor receipt inaccuracies.** (a) "12 files of process narrative removed" — 11 files are named in the table. (b) `: Type` binders: receipt "74 total, 57 forced"; my two regexes both give 72 total / 55 forced (17 widened agrees). (c) `changed types … 1 each` for `CycleLift`: the merged envdiff lists 12 lost names for that module (7 `private` helpers with `_proof_*` auxiliaries plus the public lemma) — consistent with the receipt's separate "28 private" row, but the "1 each" row is then double-counting wording.

10. **[nit] Loose citations (not wrong, but not the stated result).** `InjectiveResolutionHomology.lean`/`InjectiveResolutionCoyoneda.lean` cite Weibel **Thm 2.7.6** for "Ext computed by an injective resolution"; 2.7.6 is "Ext is balanced" — the injective-resolution computation is Weibel's *definition* of Ext (§2.5/§2.7), and 2.7.6 is the theorem that it agrees with the projective one. `CochainTransgression.lean` cites Cartan–Eilenberg "Chapter V" (Derived functors) for the two canonical SESs of a complex — vague. Acceptable, but a reader looking up 2.7.6 will not find the statement documented.

## Claims checked

| claim | status | how |
|---|---|---|
| 55 commits `9552305f..067ee091`, one per file + one cross-cutting | verified | `git log --oneline 9552305f..c214c907^2` = 56 (55 + receipt commit); every commit subject names one file except `067ee091` |
| 54 of 59 files changed | verified | `git diff --stat`: 54 `.lean` files + receipt |
| commit messages describe the commit | verified (sample of 12) | e.g. `cbb282e7`, `e002336a`, `d00ecf24`, `87b25ffb`, `164fa4e6`, `55607666`, `85ced809`, `41b7ecfb`, `0d2f128d`, `c2524413`, `1d6be2e4`, `c31bbc73` — content matches subject; docstring counts in subjects match `+/--` counts |
| 287 docstrings added, per-file table | verified | `git diff -U0 … \| grep -c '^+\s*/--'` = 294 added, 7 replaced (DeterminingFamily 2, CoefficientNormalization 2, InjectiveResolutionHomology 1, Prod 1, CycleClasses 1) → 287 net; per-file numbers match the table |
| no `private` declaration documented | verified | no added `/--` line precedes a `private` in the diff |
| after the packet, no undocumented public decl in the 59 files (incl. `lemma`, which the receipt's list omits) | verified | own awk pass over all 59 files at `c214c907^2`: single hit is the prose line `ThreeColumnSpectralSequence.lean:17` |
| 41 `## References` blocks added | verified | `grep -c '^+## References'` = 41 |
| 5 document coordinates removed (3 files) | verified | DeterminingFamily (NG4–NG10, NG5–NG6, NG7–NG10), Prod (SP1–SP6), IntegerPresentation (`## Provenance`, lanes F0b/F10) |
| 119 pins lifted / 24 forced | **refuted** | 116 / 27; see finding 3 |
| 17 `: Type` binders widened / 57 forced | partly | 17 verified; 55 forced by my count |
| lifts keep the statement at level 0, no hypothesis added | verified (all 12 lifted files read in full diff) | `MayerVietorisShortExact`, `DualEvaluation`, `CycleLift`, `ChainCycleLift`, `InjectiveResolutionHomology`, `HomeomorphCoordinates`, `Free`, `CoordinateChange`, `SingularCochains`, `CoefficientNormalization`, `CochainTransgression`, `Generators`: every change is `.{0}`→`.{v/w/u}` or `Type`→`Type v/w/*` plus `universe` lines; no binder added; scratch `#check` with `pp.universes` on `moduleDual`, `dualComplex`, `complex`, `pullback`, `uliftIntCohomologyEvaluation`, `cohomologyEvaluationAlongCoefficient`, `connectingTwo`, `cochainTransgression`; `example … = dualComplex A (chains X) := rfl` at level 0 |
| `CochainTransgression`: `TwoStepResolution` section takes `HasExt.{w}` independent of `v`; `cochainTransgression` keeps `HasExt.{v}` and takes no second instance | verified | file structure at head: `variable [HasExt.{w} C]` l.109 inside `namespace TwoStepResolution` (ends l.116); `variable [HasExt.{v} C]` l.175 in `section CochainComplex`; `#check @cochainTransgression` shows exactly one `HasExt.{u_1,u_1,u_2}` |
| forced: `chains`/`pullback*` pinned by `ModuleCat.of ℤ ℤ` | verified by reading | Mathlib `singularChainComplexFunctor : C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ` needs `w`-indexed coproducts in `C`; with coefficient object `ModuleCat.of ℤ ℤ : ModuleCat.{0}` both `X : Type` and `.{0}` are forced |
| forced: `Generators.lean` by `SingularSmallChains.chainLift` / `addHomToIntLinearMap` | verified by reading | `chainLift (X : Type) … {M : Type} … : (chains X).X n →ₗ[ℤ] M` at `9552305f:…SingularSmallChains/Basic.lean:54`; `M : Type` pins the cochain target to `Type 0` |
| forced: the `ULift.{0} ℤ` block in `CoefficientNormalization` | verified by reasoning | `cohomologyEvaluationAlongCoefficient` is a morphism in `AddCommGrpCat.{max v w}` so `B` must be `Type w`; `B = ℤ : Type 0` forces `w = 0`, hence `A = ULift.{0} ℤ`. (`ULift.moduleEquiv` itself is polymorphic; the pin comes from the categorical hom, which is the right reason, not quite the one the receipt gives) |
| forced: `Degree1.lean` single `.{0}` is in the module docstring | verified | `grep -n '\.{0}'` → line 27, inside `/-! … -/` |
| `CochainTransgression` `.{v}` obstruction (`cochainTransgression` compares `P ⟶ Hⁿ⁺¹K` in `AddCommGrpCat.{v}` with Ext) | verified by reading | statement at head lines 179–183; `Ext.addEquiv₀` target is the literal hom group |
| envdiff: 0 source lost/added, 314 changed types explained | **unverifiable** | no per-packet envdiff in repo (finding 5); merged round-7 envdiff has `changed_type_source: 0`, `VERDICT PASS` for the whole round |
| envdiff Generators row explanation | **refuted** | finding 4 |
| files that needed no change (5) | verified | not in `git diff --name-only`; `DegreeZero`, `ExactFunctoriality`, `MapExtend`, `HomComplexSingle`, `Degree1` |
| no `sorry`/`axiom`/`admit`; no `maxHeartbeats`, `unsafe`, `native_decide`, `@[simp]` change, `noncomputable` added, `private` removed | verified | grep over `+`/`-` lines of the branch diff: only hits are the 7 `private` helpers in `CycleLift.lean` whose universe changed (still private) |
| `Lib` imports no `Hopf` | verified | `git grep 'import Hopf' 39f1d12b -- Lib/` hits only `Lib/docs/*.md` prose |
| commit trailers | verified | all 56 commits carry `Co-Authored-By` and `Claude-Session` |
| short citation keys `hatcher02`, `weibel94`, … already used in the library | verified | `hatcher02` in `MayerVietorisShortExact.lean` and elsewhere; but no `.bib` exists anywhere in the repo, so no key resolves (pre-existing convention, see tool notes) |
| builds and axiom audit | not checked | needs a build; `#print axioms` on two lifted theorems in the scratch file: `propext`, `Classical.choice`, `Quot.sound` only |

Docstrings sampled and checked against their declarations (36; all correct except findings 7–8): `SingularCochains`: `moduleDual_additive`, `dualMap_id`, `dualMap_comp`, `pullback_id`, `pullback_comp`, `homotopyEquivCohomologyIso_hom`; `DualEvaluation`: `mapPositiveCocycles_val`, `cycleClass_boundaryCycle`, `boundaryCycle_val`, `positiveCocycleValue_zero/add`, `evaluationOfPositiveCocycle_zero/add`; `ChainCycleLift`: `next_nat`, `cycle_condition`, `shortCycleClass_eq_zero_iff`, `cycleClass_eq_iff`, `mapCycles_val`; `InjectiveResolutionHomology`: `positiveShortComplex_f_apply`, `positiveQuotientToExt_surjective/injective/bijective`; `CochainTransgression`: `first_shortExact`, `second_shortExact`, `cyclesComplex_exact`, `iCycles_toCycles`; `AcyclicResolutionH1`: `connecting_apply`, `toCycles_ι`, `first_shortExact`; `ExactAugmentedCochainComplex`: `i_p`, `unfactoredStep_exact`, `step_shortExact`, `toAcyclicResolution_Z_zero/i_zero`; `AcyclicResolutionFiniteCompatibility`: `stepToFirst_τ₃`, `stepToKernelFirst_τ₁/τ₃`, `toAcyclicResolutionH2_trunc/tail`, `toAcyclicResolutionH3_firstTail/secondTail`; `TwoTermMappingCone`: `twoTermPointIsoNegOne_hom`, `twoTermPointIsoZero_hom`, `mappingCone_single_isZero_X`; `IntegerPresentation`: `ofEquiv`, `adjoin`, `adjoin_mulVec`, `adjoin_coefficient`, `adjoin_matrix_injective`; `VanKampen/Basic`: `LocalPathValue`, `PathValue`, `TwoOpenCover`, `chart`, `basedLoop`, `pathDifference`, `basedLoop_trans`, `pathClass_induction_of_open_cover`, `hom_ext`, `Compatible`; `VanKampen/PathValue`: `closePath`, `closePath_trans`, `localValue`, `fundamentalGroupHom(_mk)`, `IsPrimitive`, `exists_path_subdivision`, `squareHorizontal/Vertical`, `rectangle*`, `lift`, `lift_mk_of_mem`, `localValue_map_loop`, `value_squareHorizontal_homotopy`; `Prod`: `surjective_signed_prod_of_surjective_ker`; `DeterminingFamily`: both theorems.

Citations sampled (14): Hatcher §3.1 / Thm 3.2 (UCT, evaluation half) — correct; Hatcher Thm 1.20 (van Kampen) and tom Dieck §2.6 — correct; Hatcher §2.1 — correct; Weibel §1.5 (mapping cone) — correct; Weibel §5.2 (first-quadrant/finitely many columns terminology) — correct; Weibel §§10.4–10.7 (K-injective, derived Hom, Ext/RHom) — correct; Spaltenstein 1988 — correct; BBD §1.3 (t-structures) and Kashiwara–Schapira §10.1 — correct; Verdier Ch. II (triangulated, octahedron) — correct; Grothendieck Tôhoku §2 (δ-functors) — correct; Hartshorne III §1 / Prop. 1.2A — correct; Lang *Algebra* III — correct; Weibel "Theorem 2.4.3" — see finding 2; "Exercise 1.3.x/2.4.x" — finding 1; Weibel 2.7.6, CE Ch. V — finding 10.

## Not checked

* The two `lake build` lines and the `Lib.AxiomAudit`/`Solution.lean` axiom report (needs a build; the head is built, so the claim is at least consistent with the head compiling).
* The per-module envdiff numbers and the "90 downstream types changed" row (no per-packet envdiff artefact; only the merged round diff is in the repo).
* The three "forced" claims for `SingularCochains`, `Generators`, `CoefficientNormalization` were verified by reading the pinned Mathlib/`SingularSmallChains` signatures and by universe reasoning, not by attempting the failing elaboration the receipt quotes (budget: one elaboration used).
* Section numbers I cannot confirm from memory: Deligne *Hodge II* §1.4, Gelfand–Manin IV.4, Verdier Ch. III §4, Milnor h-cobordism §7 Thm 7.6 (plausible; the audit cited the same).
* Docstrings not in the sample above (the remaining ~250 of 287, mostly `VanKampen/*` one-liners on `abbrev`s and `@[simp]` lemmas); I read all of them in the diff and none looked wrong, but I only checked the 36 listed against the actual declaration text.
* Round-8 changes to these files (`IntegerPresentation` rename of `HomologyTransport.*`, `AbCycleClass` de-duplication, `LowerTransfer` island rename) were noted but not reviewed here — they belong to the round-8 receipts.

## Tool notes

* Put the packet's `envdiff.json`/`.txt` beside the receipt (as the brief assumes). Without it the receipt's central "314 changed types, all explained" claim is a bare assertion, and the one explanation I could test (finding 4) was wrong.
* The receipt's per-file pin table should be produced by the same `grep` the audit used, not typed by hand: three "before" numbers disagree with the packet list the agent was given, and the totals disagree with the table.
* A "forced" claim is much more convincing when it names the *type* that pins the level (`chainLift … {M : Type}`, `ModuleCat.of ℤ ℤ`, the `AddCommGrpCat.{max v w}` hom) than when it quotes an error message; the error messages given are consistent but not self-explanatory.
* The reference keys (`[hatcher02]`, `[weibel94]`, …) follow Mathlib's `references.bib` convention, but no `.bib` exists in this repository; a `Lib/docs/references.bib` (or a note that the keys are Mathlib's) would let a reader resolve them and would have caught the "1.3.x" placeholders on review.
* The coverage script the receipt describes omits `lemma`; it happened not to matter (my pass including `lemma` found nothing), but the script should include it.
