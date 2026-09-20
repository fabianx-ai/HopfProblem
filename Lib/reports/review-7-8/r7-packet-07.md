# Review of Lib/reports/round-7/packets/RECEIPT-07.md

**Verdict: ACCEPT WITH FINDINGS** — the work is sound (no deletion, rename, hypothesis change, sorry or axiom; the one universe lift keeps the u = 0 statement literally; the 30 changed types are all attributable to this packet's generalisations), but the receipt has several small false counts, three manuscript equation labels survived the citation sweep, and two textbook citations are doubtful.

Scope note: branch `r7/packet-07`, base `9552305f`, tip `64eda8f2^2 = e400452c` (33 commits: 32 file commits `538f7987..acd98e17` plus the receipt commit `e400452c`, which the receipt correctly does not count). Head compared against is `39f1d12b`. Later branches touched four of the packet's files: `CubeBoundaryThreeLebesgue.lean` (b67b67df, round 8 fold of `MeshScale`), and the three `AcyclicResolution*.lean` files (round 8 `r8/pins` lifted them to `.{u}`, consistent with this receipt's "forced by `cohomologyAddCommGroup`" claim).

## Findings

1. `[incomplete]` Manuscript equation labels survive in declaration docstrings of two files whose module docstrings the receipt claims to have re-cited "(C11)--(C14)" and "(C7)--(C8)". At the branch tip and at head:
   - `Lib/Topology/Sheaves/Cohomology/Cech/CochainSheafResolution.lean:1009` — "This is equation (C13), transported through the canonical comparison"
   - `Lib/Topology/Sheaves/Cohomology/Cech/CochainSheafResolution.lean:1042` — "This is the normalized form of equation (C14). -/"
   - `Lib/Topology/Sheaves/Cohomology/Cech/DegreeZero.lean:699` — "This is equation (C8), valid without separation or paracompactness hypotheses. -/"
   Base had 3 and 2 such labels in these files; the packet removed only the module-docstring ones (commits 480b2350, f0f79db6). `(C8)`, `(C13)`, `(C14)` refer to nothing in `Lib`. The receipt's item-1 column for both files reads as if the sweep were complete. Also `Lib/Topology/Dimension/CubeBoundaryThreeDimension.lean:261` still says "assemble the previously proved receipts" (manuscript jargon). These three docstrings should be rewritten and the word "receipts" replaced.

2. `[citation]` `Lib/Topology/Homotopy/PuncturedPlaneCyclic.lean:30` (commit 66440d10) cites "Hatcher, Theorem 1.7 and Example 1.22 (π₁(S¹) ≅ ℤ, and the deformation retraction of ℂ ∖ {0} onto S¹)". Theorem 1.7 is right. As far as I recall, Example 1.22 in §1.2 is one of the van Kampen examples (linked circles / torus knots), not the deformation retraction of ℝ² ∖ {0} onto S¹, which Hatcher treats in Chapter 0 (and uses in §1.1 without a numbered example). I am not certain of the number; someone with the book should check. The same "Ex. 1.22" was suggested by the audit twin column in `packet-07.md`, so the packet copied it rather than verified it.

3. `[citation]` `AcyclicResolution.lean:24` and `AcyclicResolutionH1.lean:28` (commits ec925b79, 812a4b02) cite "Weibel, Theorem 2.4.6" for "acyclic resolutions compute derived functors". In Weibel that statement is, to my recollection, Exercise 2.4.3 (left-derived case; the right-derived analogue is in §2.5); Theorem 2.4.6 is about the δ-functor structure of `L_*F`. Medium confidence; should be checked against the book. Hartshorne III.1.2A, cited alongside, is correct for the statement.

4. `[wrong receipt]` Header table: "`: Type` binders widened: 7 declarations; 58 + 1 left, forced". The per-file rows themselves list more than 59 left: Wang 58, SphereTwo 1, BasedDiskLifting 2 ("0 of 2"), and the `(κ : Type)` in the result type of `FiniteBrickRefinement.toCriterion`. Counting `: Type)`/`: Type}` at the branch tip: Wang 58, SphereTwo 1, BasedDiskLifting 2, CubeBoundaryThreeDimension 1 — 62, not 59. The "7 widened" figure is correct (Wang 61 → 58, CubeBoundaryThreeDimension 5 → 1).

5. `[wrong receipt]` `AcyclicResolutionH1.lean` row says "0 of 15" pins left; the file has 16 `.{0}` occurrences at the branch tip (the packet list said ×16, and 5 + 16 + 8 = 29 is what the header's "29 `.{0}` pins left" needs). Nit.

6. `[wrong receipt]` `OverBase.lean` row: "40 added (all declarations) + 21 structure fields". The branch tip has 62 new `/--` docstrings in that file: 40 declaration docstrings and 22 field docstrings (`ThreefoldGluing.Data` has 12 fields, `SpecialPeriods.Threefold.Star.Input` has 10, all documented). Nit; the 245 total is unaffected since it excludes fields.

7. `[incomplete]` No `envdiff.json`/`.txt` for this packet exists beside the receipt (`Lib/reports/round-7/packets/` holds only `RECEIPT-NN.md` and `packet-NN.md`; the only envdiff artefact for round 7 stage 2 is `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}`). The receipt quotes a tool run ("lost 56 added 56 ... changed type 56, of which source: 30, VERDICT PASS") that cannot be re-inspected. I verified the 30 named constants against the merged envdiff instead (all 30 are present in `changed_type_proof_naming`, none in the source-lost/added lists), which is weaker than checking the packet's own run.

8. `[nit]` `[docstring]` `AcyclicResolution.lean:56` — "Positive-degree vanishing ... is *exactly* acyclicity for the constant sheaf": the theorem `isAcyclicFor` is one implication (`IsAcyclic R → R.IsAcyclicFor (unitSheaf X)`), proved by `h`, so the two are definitionally equal, but the docstring reads as an iff.

No `[unsound]` finding.

## Claims checked

| claim | status | how |
|---|---|---|
| 32 files, one commit per file, `538f7987..acd98e17`, order as listed | verified | `git log 9552305f..64eda8f2^2`; `git show --name-only` per commit: every one of the 32 touches exactly one `.lean` file; receipt commit `e400452c` is extra and uncounted |
| Commit messages describe the commit | verified (2 read in full, 32 subjects) | `git log --format=%B` for acd98e17, 538f7987; subjects for all |
| "No declaration deleted, renamed, or given a new hypothesis" | verified | diff is docstrings/comments plus the 8 binder/universe edits; no `theorem`/`def` line removed; envdiff source lost/added = 0 |
| No `sorry`/`axiom`/`admit`/`maxHeartbeats`/`unsafe`/`native_decide`, no `@[simp]`/`noncomputable`/`private` added or removed | verified | grep of `+`/`-` lines of `git diff 9552305f 64eda8f2^2 -- Lib/` (the only hits are the receipt's own prose) |
| Commit trailers | verified | 33/33 commits carry `Co-Authored-By` and `Claude-Session` |
| No `import Hopf` in `Lib/` | verified | `grep -rn "import Hopf" Lib/` → only prose in `Lib/docs/*.md` |
| Docstrings added (item 2): 245 = 5+40+51+100+4+2+1+21+2+3+4+7+4+1 | verified | net new `/--` per file from the diff matches every per-file figure (OverBase 62 = 40 + 22 fields, see finding 6) |
| 297 declaration docstrings/comments with a manuscript label stripped | partly | 362 removed lines carry a `Textbook`/`Lemma n.m`/`(Cnn)`/`CD-nn`/`T0n`/`L-0n`/`Q-x`/`lines nnnn`/`GP`/`receipt` marker; multi-line comments make the unit count uncountable from the diff. Order of magnitude consistent; per-file counts 26 / 27 / 213 / 16 spot-checked for CubeBoundaryThree (26 `/--` lines changed) and Cells (119 `/--` + `/-` comments changed) |
| 30 module docstrings re-cited or added | verified | all 32 files diff in their header; `EquivariantCoveringLift` and `AcyclicResolutionH1Naturality` only add a `## References` block, which is what the receipt says |
| `pushforwardAdditive` lifted `.{0}` → `.{v}`, no hypothesis added, statement at u = 0 unchanged | verified | diff of `AddCommGrpPushforward.lean`; head `#check` shows `∀ {X Y : TopCat.{u_1}} (f : X ⟶ Y), (pushforward AddCommGrpCat.{u_1} f).Additive`; scratch `example {X Y : TopCat.{0}} (f : X ⟶ Y) : (pushforward AddCommGrpCat.{0} f).Additive := pushforwardAdditive f` elaborates; `#print axioms` = propext, Classical.choice, Quot.sound |
| Changed types 2–11 caused by using `pushforwardAdditive` in their statement | verified (mechanism) | `OpenFiniteClosedFactorization.lean:170`, `FibreStalkEvaluation/OpenRestrictionComposition.lean:201,207` apply `TopCat.Sheaf.pushforwardAdditive` explicitly; `ShortComplex.map` needs the `PreservesZeroMorphisms` instance derived from it. Head `#check pushforward_exact` is now `.{u_1}` (round 8), so the branch-state type could not be re-elaborated |
| Changed types 12–16 (Wang `E : Type` → `Type*`) and 17–30 (`FiniteBrickRefinement` `ι : Type r`) | verified | diffs of `Wang.lean`, `CubeBoundaryThreeDimension.lean`; all 30 names present in `envdiff-merged-d950428a.json` `changed_type_proof_naming` (the 14 `FiniteBrickRefinement*` names enumerated) |
| Nothing else changed type because of this packet | partly | only the merged envdiff exists (finding 7); `CategoryTheory.Sheaf.Leray.pushforwardAdditive` also changed type in the merge but comes from commit 7c5050a3 of another packet |
| SphereTwo `{B : Type}` forced by `of_homeomorph {X Y : Type u}` | verified | `Covering.lean:184-188` (`HasCoveringDimensionLE` quantifies `ι κ : Type u` with `X : Type u`), `of_homeomorph {X Y : Type u}`; sphere lives in `Type`; head `#check` confirms both |
| BasedDiskLifting `{X Y : Type}` forced by `Hurewicz.homotopyMap {X Y : Type}` | verified | `Lib/AlgebraicTopology/Hurewicz/Naturality.lean:83` |
| Wang's 58 remaining binders forced by `SingularHomology (Y : Type)`, `twoPunctureSet {X : Type}`, `cylinderPuncture {E : Type}` | verified (existence of pins) | `MayerVietoris.lean:928`, `LocalDegree.lean:79,393`; the "40+ cascading errors" build claim not reproduced |
| AcyclicResolution pins forced by `cohomologyAddCommGroup` pinned at `.{0}` | verified | `git show 9552305f:Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean:30-33`; round 8 lifted that instance and then these files (85312af3, 63bdbb61), corroborating the obstacle |
| `toCriterion` result keeps `(κ : Type)` because of `HasCoveringDimensionLE Boundary` | verified | definition of `HasCoveringDimensionLE`; `Boundary : Type` |
| `hδ : 0 < δ` kept in `subset_cover_of_diam_lt_of_ball_cover` | verified | diff of `LebesgueNumber.lean` |
| Proof narratives moved into comments (BasedDiskLifting ×2, LocallyZeroCochain ×1) | verified | diffs |
| Wang: 100 public declarations documented, one `private` helper undocumented | verified | 100 new `/--`; only `private` is `sum_range_shift_of_endpoints_eq` (line 410), no docstring |
| Later branches did not undo this packet's edits | verified | `git log 64eda8f2..39f1d12b -- <files>`; `pushforwardAdditive` still `.{v}` at head |

Docstrings sampled and checked against their statements (36): Wang — `mk_add_int`, `homologyNorm`, `homologyNorm_apply`, `homeomorph_symm_pow_eq`, `radialCylinderHomeomorph`, `puncturedCylinderHomeomorph`, `cylinderLink`, `punctured_cylinder_endpoint_relation` (degree `n ≠ 0`, slice 1 = slice 0 + link), `radialCylinderDiffeomorph` (`Sⁿ` with `finrank = n+1`), `inverseMonodromy_period`, `lowerSection`/`upperSection` and `_val` (times 1/4, 3/4), `uTime`/`vTime` (intervals `(1/4,3/4)`, `(-1/4,1/4)` match `uStrip_val`/`vStrip_val`), `vStrip_val` (`f^(k+1)`, consistent with `mk_add_int` and `vStrip_zero`), `vStrip_one` (`(k+1)`-st lower section), `uPath_apply`/`vPath_apply` (`(k+1/4)/m → (k+3/4)/m → (k+5/4)/m`), `quarterLift_period`, `boundaryOne_arcPrefix`, `uCrossChain_boundary` (upper − lower), `vCrossChain_boundary` (lower (k+1) − upper k), `differenceCycle_val`, `vCrossChainSum_boundary` (sign), `differenceCycle_class_coordinates` and `coverSmallCycle_boundaryCoordinates` (`(-N b, N b)`, consistent with the section coordinate lemmas), `coverSmallCycle` (degree n+1), `sub_cross_boundary_mem_range_circleSection`; Čech — `ConnectingHom` module docstring (`Ȟ^q(F₃) → Ȟ^{q+1}(F₁)`, paracompact Hausdorff), `BoundaryPresentation.lift_eq`/`descended_eq` (which sheaf morphism, which degree), `DegreeZero.globalToZeroCochain_π`, `globalToZeroCycles_isIso`, `CochainSheafResolution.toIntersectionSectionsSheaf_app`, `face_prependIndex_zero`, `terminalAugmentation_π`, `CoveringDimensionVanishing` module docstring (`a > n` vs multiplicity `n+1`); Dimension — `Covering` module docstring (`n+1` members), `SphereTwo.hasCoveringDimensionLE_two` ("more than three members"), `brickOpens_multiplicityLE_three`, `hasCoveringDimensionLE_two`; Gluing — `Data.source_eq`, `transition_inter`, `inclusion_eq_iff`, `Star.Input.target_eq`, `transition_none_some`; PuncturedPlaneCyclic — `upperHeightMap`, `slitSets_inter`, `meridianHalfCircle`, `overlap_has_two_components`. All match their statements except the nit in finding 8.

Citations checked (my own knowledge): Hatcher Thm 1.7, Prop 1.31, Prop 1.34, Prop 1.39 (with 1.31 gives the file's criterion), §4.1 (compression lemma / Whitehead), Example 2.48 (mapping torus) — correct; Munkres Lemma 27.5, §41, §50 — correct; Hartshorne III.1.2A, III.2.5, III Lemma 4.1, III Lemma 4.2, II.1, III.8 — correct; Hurewicz–Wallman Ch. IV / Thm IV 1, Ch. V — correct; Bredon III.4 (Čech) — correct; Hatcher Ex. 1.22 and Weibel Thm 2.4.6 — doubtful (findings 2, 3). Not verifiable by me: Godement II.4, II.4.7, II.5.1–5.3, 5.2.3, 5.7, 5.8, 5.9–5.10, 5.12 numbering (II.5.12 as the covering-dimension vanishing theorem and 5.2.3 as flasque Čech-acyclicity agree with how these are usually cited); Engelking 1.6, 1.8, 1.8.2, 1.8.3, 1.8.6 numbering; Mathlib `gaugeRescaleHomeomorph` and `precise_refinement` exist under those names.

## Not checked

- The packet's own `envdiff` run (no artefact in the repo); the "lost 56 / added 56 are all `_proof_n`" sentence is unverifiable.
- The build-failure claims used as obstacles ("`SphereTwo.lean:40:2: Type mismatch`", "`BasedDiskLifting.lean:61:66`", "`Wang.lean:79:43`", "`AcyclicResolutionH1.lean:53:4` failed to synthesize") — I confirmed the pinned upstream binders exist, not that widening fails exactly there.
- `FlasqueAcyclic.lean` index-universe obstacle ("needs `AddCommGrpCat.{max u v}` products throughout the ordered-Čech interface").
- The remaining ~209 added docstrings (mostly PuncturedPlaneCyclic, OverBase, CochainSheafResolution) beyond the 36 read; the 213 relabelled comments in `CubeBoundaryThreeCells.lean` beyond the ~40 read (all read ones are pure prefix removal).
- Branch-state types of the 10 Leray/FiniteClosedPushforward constants (need a build at `acd98e17`).

## Tool notes

- Commit the packet's envdiff JSON/TXT beside the receipt; a receipt that quotes tool output without the artefact cannot be reconciled line by line, and the merged file mixes ten packets.
- The receipt's header totals disagree with its own rows (findings 4–6); a script that sums the per-file table would have caught all three.
- A grep for `\(C[0-9]+\)`, `CD-`, `Textbook`, `receipt` over the packet's files after the last commit would have caught finding 1; the sweep evidently only looked at module docstrings for the Čech files.
- Citations copied from the audit's twin column (`packet-07.md`) inherit its errors; the receipt should say which citations were checked against the book and which were taken from the audit.
