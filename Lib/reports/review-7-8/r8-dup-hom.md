# Review of Lib/reports/round-8/dup-hom/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — every deletion has a surviving twin of equal or greater strength and the 17 ported van Kampen statements are the monolith's statements verbatim (modulo `Cocone.` and line wrapping), but table B names a wrong twin for one deleted lemma (the named twin has six extra hypotheses; the real twin is a different, more general lemma), and several numbers in the receipt are off.

Scope: branch `r8/dup-hom`, base `4e15a034`, tip `1e0cf7ac^2` (= `6ea8d226`), 6 commits; after-state compared at `39f1d12b`. `Pushout.lean` and `Surjectivity.lean` are byte-identical between the branch tip and `39f1d12b`, so later branches did not touch the ported material.

## Findings

1. **[wrong receipt] Table B names the wrong twin for `CoverNaturality.smallConnecting_naturality`.** The receipt (§1 item 4 and §4 table B) says the twin is `SingularMayerVietoris.connectingHomomorphism_naturality_of_sequenceMap` and that the deleted lemma is "an instance of" it. It is not. Deleted (`git show 4e15a034:Lib/AlgebraicTopology/SingularHomology/Naturality.lean`, l.209):
   ```
   theorem CoverNaturality.smallConnecting_naturality … (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
       (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
       (singularHomologyMap (mapOn f (U ∩ V) (U' ∩ V') …) n).comp (smallConnectingMap U V n) =
         (smallConnectingMap U' V' n).comp (homologyLinearMap (smallMap U V U' V' f hU hV) (n + 1))
   ```
   Named twin (head, `Naturality.lean`):
   ```
   theorem SingularMayerVietoris.connectingHomomorphism_naturality_of_sequenceMap … (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
       (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
       (φ : chainSequence U V ⟶ chainSequence U' V') (hφ : …) (n : ℕ) :
       (homologyLinearMap φ.τ₁ n).comp (connectingHomomorphism U V hU hV hcover n) =
         (connectingHomomorphism U' V' hU' hV' hcover' n).comp (singularHomologyMap f (n + 1))
   ```
   The named twin needs `IsOpen U/V/U'/V'` and two cover equations that the deleted lemma does not have, and it is about `connectingHomomorphism` (the singular-level map), not `smallConnectingMap` (the chain-level map). It does not imply the deleted statement. The *actual* twin is `SingularMayerVietoris.connectingMap_naturality` (`MayerVietoris.lean:656`, general short-exact sequences) applied to `chainSequenceMapOfMapsTo` — which is exactly what the deleted proof term was. I re-proved the deleted statement (with `mapOn`/`smallMap` respelled to `intersectionRestriction`/`smallMapOfMapsTo`) from that lemma in one term (`r8-dup-hom/Scratch.lean`, elaborates cleanly), so nothing is lost from the library; the receipt's twin entry is wrong and the sentence "two of those twins … are the more general statements, so the deleted declarations are instances of them" is only right for `comparison_naturality`. Table B should read `CoverNaturality.smallConnecting_naturality` → `SingularMayerVietoris.connectingMap_naturality` (instance at `chainSequenceMapOfMapsTo`).

2. **[nit / wrong receipt] "1823 lines"** for the deleted monolith: `wc -l` on `git show 4e15a034:…/VanKampen.lean` gives 1810, and the branch diff records 1810 deletions. The figure is copied from the packet.

3. **[nit] §3 double-counts the added names.** "the 16 ported pushout declarations plus `TwoOpenCover.pushoutToFundamentalGroup_of` and `TwoOpenCover.fundamentalGroup_eq_one`" — `pushoutToFundamentalGroup_of` is already one of the 16 listed under item 1. The total 32 = 17 + 3 + 1 + 11 is correct only when it is counted once (checked against `envdiff.json` `added`: 37 entries, 5 of them `_proof_` auxiliaries).

4. **[nit] "Character-for-character identical"** for the 17 ported statements holds only modulo whitespace: three signatures (`pushoutToFundamentalGroup_comp_of/_ofU/_ofV`) and two docstrings were re-wrapped to fit 100 columns after the `Cocone.` segment lengthened the names, and the `fundamentalGroup_eq_one` docstring says "charts" where the original said "opens". Token-for-token (whitespace collapsed) they are identical; I checked all 17 mechanically. Proofs are byte-identical; no hypothesis added, no `sorry`.

5. **[nit] File/line references off.** "`PostnikovD2PageSplice.lean:12`" — the import of `SpectralObject.PostnikovD2` is line 11. "431 `#check`/`#print axioms` lines" in `AxiomAudit.lean` — 426 lines mention `FundamentalGroup.VanKampen.Cocone` at the base; immaterial to the argument (the monolith is indeed probed nowhere: the only non-`Cocone` `VanKampen` probe is `exists_stageCharacter` from `FiniteStarCharacter`).

6. **[nit / incomplete] Rename map covers only the 17 ports and one rename.** The 13 table-B and 5 table-C pairs are also old-name→new-name correspondences of surviving content; listing them in `rename.txt` would have let the envdiff tool show them as bijections instead of 18 lost + 18 added. The receipt's choice to treat them as deletions-with-twins is defensible under the protocol, but it makes the envdiff harder to read.

No `[unsound]` finding. No `sorry`, `axiom`, `maxHeartbeats`, `unsafe`, `native_decide` in the branch diff; the one `+@[simp]` is the ported `pushoutToFundamentalGroup_of`, which was `@[simp]` in the monolith; the five `private` removals are the documented promotions in table C; `noncomputable section` appears only in the two new modules; no `import Hopf` under `Lib/` (only in `Lib/docs/*.md` prose). All six commits carry both trailers.

## Claims checked

| claim | status | how |
|---|---|---|
| 6 commits, messages describe the commits, trailers present | verified | `git log --format=%B 4e15a034..1e0cf7ac^2` |
| Monolith `VanKampen.lean` deleted; 21 modules re-imported to `VanKampen.Surjectivity`; `Lib.lean` just drops the import | verified | branch diff: 21 `+import …Surjectivity`, 22 `-import …VanKampen` (22nd is `Lib.lean`) |
| 16 pushout declarations ported to `Pushout.lean`, statements identical modulo `Cocone.` | verified (modulo whitespace, finding 4) | monolith l.1624–1737 with `s/TwoOpenCover/Cocone.TwoOpenCover/` diffed against `Pushout.lean` l.95–212; whitespace-collapsed diff empty |
| Ported proofs unchanged, no added hypotheses | verified | same diff; proof bodies byte-identical |
| `twoOpenCover_fundamentalGroup_eq_one` ported as `Cocone.TwoOpenCover.fundamentalGroup_eq_one`, same statement | verified | monolith l.1795–1810 vs `Surjectivity.lean` l.183–199, token diff empty; `#check` and `#print axioms` in scratch: `[propext, Classical.choice, Quot.sound]` |
| `twoOpenCover_pathConnectedSpace` already had twin `Cocone.TwoOpenCover.pathConnectedSpace` | verified | `#check` in scratch: `∀ … (D : Cocone.TwoOpenCover X), PathConnectedSpace X` |
| `Cocone.TwoOpenCover` is field-for-field the deleted `TwoOpenCover` | verified | monolith l.104–113 vs `VanKampen/Basic.lean:132–141`: `U V cover pathConnectedU pathConnectedV pathConnectedIntersection base baseU baseV`, same types |
| `Cocone.LocalPathValue`, `Cocone.PathValue` field-for-field the monolith structures | verified | monolith l.34–74 vs `Basic.lean:58–101` |
| Table A: 228 suffixes each with a `Cocone.` twin of the same statement | verified for all 183 non-auto-generated suffixes | script `cmpA.py`: 162 signature matches; 18 are structure projections (covered by the structure comparison); 3 are the structures themselves (compared by hand); 45 auto-generated (`casesOn`, `noConfusion`, `congr_simp`, …) not compared |
| 11 changed-type names are exactly the `TwoOpenCover` → `Cocone.TwoOpenCover` substitution, plus two call-site rewrites | verified | `git diff 4e15a034 1e0cf7ac^2 -- Hopf/ …SuspensionCover.lean`: all non-import hunks are that substitution, three `FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc` → `Cocone.` requalifications, and `Hopf/Proof/Hurewicz.lean` using `D.pathConnectedSpace`/`D.fundamentalGroup_eq_one` |
| Table B: 13 `CoverNaturality` declarations deleted, twins same or stronger | 12 verified, 1 refuted (finding 1) | read both blocks of base `Naturality.lean` (l.55–280, 470–770); `mapOn`=`coverRestriction` by `rfl` (scratch); `comparison_naturality` re-proved from `_of_comm` (scratch); `intersection_left/right` are the twins with sides swapped and a definitionally equal restriction map; `connecting_naturality(_apply)` identical modulo `mapOn`↔`intersectionRestriction` |
| Kept `CoverNaturality` block (swap, reversing, chart-transported forms) survives | verified | head `Naturality.lean`: 17 `CoverNaturality.*` declarations remain, incl. `reversingIntersectionMap`, `connecting_reversing_naturality` used by `LinearSphereAction.lean` |
| 9 call sites rerouted in `OnePointCover`, `LocalContributionsNaturality`, `SurgeryCollapse` | verified | branch diff of the three files: 5 `mapOn` + 4 `connecting_naturality_apply` removed |
| Table C: five `private` helpers in `CycleLift.lean` identical to the `AbCycleClass.lean` copies | verified | base `CycleLift.lean` l.39–95 vs head `AbCycleClass.lean` l.43–110; statements and proofs identical (universe variable renamed `w`→`v`); the two remaining privates (`shortHomologyMap_surjective_of_cycle_lifts`, `_injective_of_boundary_detection`) stay in `CycleLift.lean` |
| `ab_homologyπ_comp_abHomologyIso_hom`, `shortCycleClass`, `shortHomologyMap_cycleClass` moved out of `InjectiveResolutionHomology.lean` with the same names | verified | branch diff of that file (35 lines removed, one import added); envdiff `moves`: 3, ambiguous 0 |
| Table D: the two `homotopy_on_cocycle_succ` copies have the same statement as `CochainComplex.homotopy_on_cocycle_succ` | verified | base `PositivePrimitives.lean:123`, base `CochainHomotopy.lean:40`, head `CocycleEvaluation.lean:39`; only bound-variable names differ (`c`/`x`); `#print axioms` standard |
| `AxiomAudit.lean` probes the lemma once instead of twice | verified | branch diff of `AxiomAudit.lean` |
| Envdiff: lost 335 / added 37 / changed 12; every lost source name in a table or in the changed-type list | verified | script over `envdiff.json`: 263 lost names are in tables A–D or the 11 changed-type names; the remaining 72 are `_proof_N`, `eq_1`, `match_1` auxiliaries of deleted definitions (receipt: "auxiliary … not judged: 116") |
| `rename.txt` is written `old new` (base→after) and is a no-op on the after dump; MERGE.md reversed it | verified | `rename.txt` 18 lines, first column = base names; `MERGE.md:109–115`; `INTEGRATION-8.md:34` confirms the shared rules had the direction backwards |
| Item 5: no declaration added/removed/changed; docstrings only | verified | branch diff of `Sum.lean`/`Coproduct.lean` is 13 added docstring lines |
| Item 6 kept-both reason: `positiveHomologyExtIso` (ℕ-graded, degree `n+1`, `Iso` in `AddCommGrpCat`) vs `coyonedaHomologyExtAddEquiv` (ℤ-graded `(n : ℤ)`, `AddEquiv`) are different statements | verified | `InjectiveResolutionHomology.lean:298`, `InjectiveResolutionCoyoneda.lean:48` |
| Item 10 refutation: `ArbitraryCoverMesh.lean` imports the three mesh files and uses their lemmas; two-set tails conclude `⊆ U ∨ ⊆ V` vs `∃ i, ⊆ U i`; extra `[Nonempty K]` | verified | import chain `ArbitraryCoverMesh → MeshSubdivision → MeshAffine → MeshLebesgue`; 3 uses of `meshFactor`/`eventually_meshFactor_pow_mul_lt`/`simplex_formalSubdivision_iterate_diam`; `[Nonempty K]` at `ArbitraryCoverMesh.lean:38`; `⊆ U ∨` conclusions in all three mesh files |
| Item 10 blocker: `CochainHomotopy.lean` imports `Basic.lean`; consumers at `GlobalUnitH1Criterion.lean:92,135` | verified at base | `git show 4e15a034:…GlobalUnitH1Criterion.lean` l.92,135 use `smallCochain_cocycle_lift_exact_one` / `smallCochain_boundary_of_restriction_boundary_one`. **Note:** that file was deleted later in round 8 (`0d8e2b19`, `dup-sheaf`), so this blocker no longer exists at `39f1d12b` and the `_one` lemmas can be retired by the next seat. |
| Item 11 refutation: `TwoStepResolution` = `AcyclicResolutionH1` + `epi_g`; `Hom` structures differ (bundled `ShortComplex` hom vs `τ₁ τ₂ τ₃` with `cat_disch`); `AcyclicResolution.trunc` has `g` a differential | verified | `CochainTransgression.lean:46–54`, `AcyclicResolutionH1.lean:74–81`, `TwoStepResolutionNaturality.lean:39–46`, `AcyclicResolutionH1Naturality.lean:49–52`, `AcyclicResolution.lean:221–228` (`trunc_X₃ : X₃ = R.X (n+2)`) |
| Item 11: `Ext/PostnikovD2*` imports `SpectralObject/PostnikovD2` | verified (line 11, not 12) | `PostnikovD2PageSplice.lean:11` |
| Item 3 sub-claim: `Coproduct.homologyBiproductEquiv` is not under `Barycentric/*`; near-twin `homologyBiprodEquiv` is `K ⊞ L` at universe `u` vs `⨁ K`, `[Fintype ι]`, universe 0 | verified | `grep` in `Barycentric/` empty; `MayerVietoris.lean:768`; `Coproduct.lean:383` |
| Item 2 decline: 57 importers of `Chains.lean`; PR trio "kept verbatim"; `ChainHomology` halves have no counterpart in the trio | verified | 57 files `import Lib.AlgebraicTopology.SingularHomology.Chains`; header line 6 of `SimplexPaths`/`CycleClasses`/`Degree1`: "Kept verbatim except for import paths"; of 40 sampled `SingularChains.*` names the 35 `ChainHomology.*` ones have no twin in the trio, the 5 others (`Chains`, `Cycles1`, `Opchains`, `Simplex`, `SingularH1`) do |
| Item 3 decline: `MayerVietoris.lean` copy typed on `SingularChains.*`, Barycentric copy on arbitrary covers `U : I → Set X` | verified by sample | `MayerVietoris.lean:2179` `realizedChain_mem_small` (two-set) vs `Barycentric/RealizationSupport.lean:73` (`U : I → Set X`); `CrossProduct.lean` has 1097 `SingularMayerVietoris.` references, `CubeChainDecomposition.lean` 144 |
| "167 source declarations", "149 names agreed" | roughly consistent | 165 top-level `def/theorem/abbrev/structure` lines in the monolith; 183 non-auto table-A suffixes − 16 ports − 18 projections = 149 |

**On the item-2 refusal (the assignment asked for a judgement).** The reason holds. The obstruction is not size alone: the `ChainHomology.*` half (35 names in `Chains.lean`, none with a counterpart in the PR trio — checked) is a different presentation (explicit `Opchains` quotient, `ℤ`-`LinearMap`s) of what `Degree1.lean` does with `ModuleCat` morphisms and abstract opcycles, and the trio's "kept verbatim" header forbids adapting it, so the bridge has to be built on the `SingularChains` side and then threaded through 57 importers. That is a multi-day rewrite, not a de-duplication, and the receipt neither hides it nor half-does it. Declining and recording the plan is the right call for this seat; the risk is only that it stays undone.

## Not checked

* The build lines (`lake build Lib`, `Solution`, `AxiomAudit`, census ratchet) — trusted; I ran one `lake env lean` on a scratch file importing the four touched modules (all `#check`s, `#print axioms` and three `example`s succeed at `39f1d12b`).
* The exact pair counts of item 2 (35/63/4/56/12) and item 3 (124 declarations, 5 two-set specialisations, 944/124/20/2 references) — sampled only; the qualitative claims behind them hold.
* "23 external uses against 9" — `CoverNaturality.*` has 14 use lines outside `Naturality.lean` at the base (9 of deleted names, 5 of kept ones); I did not count the `SingularMayerVietoris` side.
* The 45 auto-generated names in table A (`casesOn`, `noConfusion`, `congr_simp`, …) — follow from the structures/definitions being identical.
* Docstrings: the branch adds 8 docstrings in `Pushout.lean` and 6 in `AbCycleClass.lean`/`CocycleEvaluation.lean`; I read all 14 against their declarations (the Hatcher Thm 1.20 / Prop 2.21 citations are the right results) and found nothing wrong, but this branch is not a docstring packet, so no wider sample.

## Tool notes

* The receipt's own note on `--rename` direction is correct and MERGE.md acted on it; the round-8 rules were wrong, per `INTEGRATION-8.md:34`. A reviewer still has to read `rename.txt` to see which way it goes — a header line stating the direction would help.
* The tool's `auxiliary` bucket (116 lost) is where 72 of the 335 lost names went; the receipt's "263 by the name filter" sentence explains this but a reviewer has to reconstruct it. An explicit "auxiliaries of deleted definitions, not listed" line with the count per parent declaration would close that gap.
* Twin tables should give a file:line for the twin and, where the twin is "stronger", the instantiation (which arguments to pass). Finding 1 would have been caught by the author when writing the instantiation.
* `MERGE.md:69` attributes "`dup-hom`'s four `sphereMap_*`/`homology_relative_sign` declarations" in `LinearSphereAction.lean` to this branch; this branch never touches that file (`git diff 4e15a034 1e0cf7ac^2 --stat -- …LinearSphereAction.lean` is empty; the file's round-8 history is `513197b9`/`1a7358c0` on `dfiles-a`). That is a MERGE.md error, for the merge reviewer.
