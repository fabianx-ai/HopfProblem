# Fix round for the monolith-wave reviews (`fix/waves`)

Fixes of `Lib/reviews/REVIEW-WAVES.md` §3, from the findings of `wave-reviews/W1.md` and `W2.md`.
Branch `fix/waves`, base `08aa22ea` (= `lib/integration`), worktree `/home/goblin/hopf-fix-waves`.
Model: Claude Opus 5.5 (`claude-opus-5-5`). Start 2026-10-01 23:03 CEST, end 2026-10-01 23:51 CEST.
Scratch: `/home/goblin/.claude/jobs/06995e68/tmp/fix-waves/` (logs, dumps, `hashcheck.py`, `conly.py`).

## Per finding

| finding | what was done | commit |
|---|---|---|
| W1-1 code | 14 effective `attribute [local instance] SingularHomology.integerLinearMapModule SingularHomology.integerTensorModule in` prefixes restored with the base text and position (prefix, blank line, docstring), from `e669bc93:…/PrismOperator.lean` lines 289, 313, 590, 748, 3639–3741: `suspensionOne_apply`, `suspensionTwo_apply`, `squareHomologyClass_const` (`HurewiczMap`), `Hurewicz.Prism.prismOperator_apply` (`Basic`, was `…DegreeTwo.SimplyConnected.prismOperator_apply`), `lowerProductTriangle_fst/_snd`, `upperProductTriangle_fst/_snd`, `leftProductDegenerate_fst`, `bottomProductDegenerate_snd`, `lowerSquareTriangle_zero/_one`, `upperSquareTriangle_zero/_one` (`TwoTriangles`). The two before `timeSlice` and `squareAffineTriangle` bound to a `/-! ### -/` header at the base and were vacuous: not added. 63 base occurrences = 61 now + 2 vacuous. Diff: +42 lines, 0 removed. | `f04032e6` |
| W1-1 receipt | `wave-1/prism.md` corrected in place | `5f643949` |
| W2-1 code | `set_option maxSynthPendingDepth 3` restored in `Collar/RangeTransport.lean` where the base monolith had it: file-wide, after the module docstring, before `open Set Function Filter Manifold Topology` (`3760f829:Lib/Geometry/Manifold/Collar.lean:59`). Diff: +2 lines. The other seven pieces do not need it (hash table below). | `5a03b3bc` |
| W2-1 receipt | `wave-2/collar.md` corrected in place (false proof-numbering explanation; real cause; restored) | `c5c15a34` |
| W1-4 | ten doubled docstrings: second copy deleted, first kept verbatim (rewrapped where `-/` pushed it past 100 columns) | `3cff6245` |
| W1-5 | `cancel_realized_higher_minimum`: `?` replaced by "`r` of any index"; hypotheses on `f₀`, `V`, `G` listed; no-connection restricted to critical points other than `q`, `p`, `r` | `65dea84e` |
| W1-10 | `exists_transverse_sheet_of_circle_placement`: `hγ`, `hβ` added; `remove_connections_of_nonincreasing_indices`: every conjunct of the conclusion, including `V = S.field` near every critical point | `9e81fee6` |
| W1-8 | `minimal_excellent_morse_minimum_count_one`: statement first, then "(cf. Milnor, *Lectures on the h-cobordism theorem*, Theorem 8.1 (index 0))" | `979a2965` |
| W1-9 | Godement pointer dropped from `ComparisonPositive.lean` module docstring; Bredon III §1 and Warner 5.32 stay | `4faba5f4` |
| W1-7 | "Hatcher, Example 0.2 / Proposition 2.22" → "cf. Hatcher, *Algebraic Topology*, Chapter 0" in `PuncturedBall` (module docstring and `sphereHomotopyEquiv`) and `DiskCollapse` (module docstring). Proposition 2.22 dropped in both places: neither sentence states the good-pair quotient isomorphism (the `DiskCollapse` sentence is the homeomorphism `D/∂D ≅ OnePoint N`) | `ec96e418` |
| W1-6 | 18 piece module docstrings (the 18 listed in W1-6), the `Subdivision` facade and `Hurewicz.cubeChain_eq_sum_simplices`: Theorem 4.32 cited for the statement only, the argument described as this development's own and pointed to `Lib/docs/C.md` (exists at `08aa22ea`; sections given only where the base facades gave them: §8 straightening, §3 Kuhn, §§3 and 10–11 cube chain) | `78f20eac` |
| W2-5 | `squareRelInterior`: cites `square_relInterior_coherent` with `N > 0`, `h = 2 / N`; `edgeEndpoints`: cites the private `edge_endpoints_coherent`, states `0 < h` | `c546deb1` |
| W2-6 | `GeneralPosition.exists_patch_step`: `dim E + dim E' < dim G`, `g` smooth, finite dimensions, Lindelöf `X × Y`, finite patch family; `ImageComplement.circle_nullhomotopies`: `g` smooth, `Y` compact, `N` boundaryless Hausdorff; `exists_smooth_nonzero_approx`: `M` σ-compact Hausdorff boundaryless | `24c63352` |
| W2-7 | `TriangleRiemannNormalization.discCoordinate`: "the complex number `e x`, of norm at most one" for a homeomorphism `e : K ≃ₜ closedBall (0 : ℂ) 1`; Ahlfors and "affine" dropped | `a86bc165` |
| W2-4 | `wave-2/morselemma.md` corrected in place: common cause `MorsePerturbation.coordinateGradient._proof_1..3` → `SmoothMorseLemma.Bilinear._proof_1..3` (verified: present in the `uses` diff of all 35, wave-2 base dump vs `dump_head3`; 14 of them also renumber other `_proof_n`) | `ff5a9c4f` |
| W2-2 | `wave-2/cube3.md` corrected in place: four declarations, five modifiers (`square_zero_mem` added; `coordinateNonconstant` has `public` and `@[expose]`) | `cac021a1` |
| W1-12 | `wave-1/residue.md`: the lift example is the `A : AddCommGrpCat.{0}` special case; `LiftCheck.lean` untouched | `c1bafcf0` |
| W1-2, W1-3, W1-13, W2-3 | already corrected in both `MERGE.md` at `08aa22ea`; nothing to do | — |
| W1-11, W2-9, W2-8, W2-10 | naming / nits, owner's call or no action asked; see Left | — |

Comment-only check (`conly.py <commit>`: both sides with `/- -/` and `--` comments stripped, blank lines
dropped, compared per file): `3cff6245 65dea84e 9e81fee6 979a2965 4faba5f4 ec96e418 78f20eac c546deb1
24c63352 a86bc165` → `code-diff files 0` each. `f04032e6` 3 and `5a03b3bc` 1 (the A commits, added lines
only: 14 × the two prefix lines, 15 blank lines, 1 `set_option` line).

## Hash check of A

`dump_after.jsonl` = `lake env …/lean-agent-ide dump Solution Lib --modules Hopf,Lib` at `a86bc165`
(38,373 constants); `dump_after_ren.jsonl` = the same with `--rename Lib/reports/wave-1/rename_all.txt`.

| constant | base (wave-2 `dump_head.jsonl`, `3760f829`) | before fix (`wave2/final/dump_head3.jsonl`) | after fix |
|---|---|---|---|
| `DiskFraming.exists_smooth_frame_near_starConvex` | 3226562774 | 3622023359 | **3226562774** |
| `DiskFraming.exists_smooth_frame_on_neighborhood_closedBall` | 995586449 | 3798691450 | **995586449** |

Collar (`Lib.Geometry.Manifold.Collar.*`, `typeHash` by name against the wave-2 base dump; private names
matched by user-facing name): 296 constants, 294 matched, 9 differ, 2 unmatched — all auxiliary:

- `DiskFraming.SmoothRangeTransportOn.trans._proof_8` differs and `…trans._proof_9` is new;
- `SphereCoordinates.ofLinearIsometry._proof_3 … _proof_10` differ and `…_proof_11` is new.

Explanation: in the monolith the later declaration reused an auxiliary proof first abstracted by an
earlier one (base `ofLinearIsometry._proof_3/_4` use `DiskFraming.SmoothRangeTransportOn.symm._proof_3`);
in a piece that does not elaborate that earlier declaration first (`SphereCoordinates` imports `Mathlib`
only), Lean abstracts it afresh under the later name, which shifts the numbering by one. The parents'
hashes (`ofLinearIsometry` 3080496248, `trans`) are equal to the base. These differences were present
before the fix and are unchanged by it; no `set_option` can restore them, so no other piece gets the
option. Every non-auxiliary constant of the eight pieces has its base hash.

Prism (`Lib.AlgebraicTopology.Hurewicz.PrismOperator.*`, `typeHashPublic` of the renamed after-dump
against the wave-1 base `dump_head.jsonl`, `e669bc93`): 679 constants, 657 matched, 58 differ, 22 unmatched.
Non-auxiliary differences: exactly the 10 planned lifts (`squareTriangles_diagonal`,
`lower/upperSquareTriangle_outerFace`, `subdivisionLowerSquareTriangle_based`,
`subdivisionUpper{Negative,Positive}SquareTriangle_based`, `homotopyTrans_{compContinuousMap,const,congr}`,
`tetrahedronSimplexBlendMap`). The other 48 differences and all 22 unmatched names are `_proof_n`,
`eq_1` or `_abel` auxiliaries; the 17 differing `eq_1` lemmas differ from the base only in auxiliary
`uses` (non-auxiliary `uses` diff empty for each), i.e. through renumbered abstracted proofs. The restored
prefixes change no hash (envdiff below: the fix changes exactly the two `DiskFraming` types), as the
review predicted (the 14 are theorems whose statements do not use the local instances).

Full output: scratch `hashcheck.txt`; reproduce `python3 <scratch>/hashcheck.py`.

## envdiff (`fixes/envdiff.txt`, verbatim; base = `wave2/final/dump_head3.jsonl`, the head before the fixes)

```
constants before 38373 after 38373 (keys 38271 38271 )
lost 2 added 2 of which source declarations: 0 0 ; names with changed type 2 of which source: 2
  PROOF-NAMING DiskFraming.exists_smooth_frame_near_starConvex
  PROOF-NAMING DiskFraming.exists_smooth_frame_on_neighborhood_closedBall
auxiliary lost/added/changed (not judged): 2 2 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

0 source lost, 0 source added; changed types = exactly the two `DiskFraming` names (the "lost 2 added 2"
are those two keyed by their old and new hash, `envdiff.json` `lost`/`added`). The class
`PROOF-NAMING` is the tool's; the change is the instance-path restore of A.2.

## Check lines (logs in scratch, at `a86bc165`; the later commits touch only `Lib/reports/`)

```
step1_lib.log       lake build Lib                                   Build completed successfully (9419 jobs).  done 0
step2_solution.log  lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9480 jobs).  done 0
step3_audit.log     lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit  Build completed successfully (9421 jobs).  done 0
                    3302 "depends on axioms" + 12 "does not depend on any axioms" = 3314 probe lines;
                    axioms seen: propext 3302, Quot.sound 3292, Classical.choice 3172; sorryAx 0
                    (same counts as wave2/final/step3_audit.log)
step4_census.log    python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648  done 0
grep -rnE '^(public )?import Hopf' Lib/ --include=*.lean | wc -l    0
```

`lake build Lib` warnings: 18, all in files rebuilt for comment edits or downstream
(`Hurewicz/{CubeChainDecomposition/{IntervalSplit,Concatenation},Straightening,CubeSphere,HopfDegree,Naturality}`,
`SingularHomology/LocalContributions`), same count as `wave2/final/step1_lib.log`; none in `PrismOperator/`
or `Collar/`.

## Commits (`08aa22ea..` this receipt)

```
3cff6245 Lib/Geometry/Manifold/Morse: delete the second copy of ten doubled docstrings
65dea84e Lib/Geometry/Manifold/Morse/SurgeryCollapse/MinimumReduction: state cancel_realized_higher_minimum exactly
f04032e6 Lib/AlgebraicTopology/Hurewicz/PrismOperator: restore 14 attribute [local instance] … in prefixes
5a03b3bc Lib/Geometry/Manifold/Collar/RangeTransport: restore set_option maxSynthPendingDepth 3
9e81fee6 Lib/Geometry/Manifold/Morse: add the two omitted hypotheses and conclusions to docstrings
979a2965 Lib/Geometry/Manifold/Morse/SurgeryCollapse/MinimumReduction: cite Milnor 8.1 as cf., not as the theorem's name
4faba5f4 Lib/Topology/Sheaves/SingularCochainSheaf/ComparisonPositive: drop the Godement pointer
ec96e418 Lib/Geometry/Manifold/Morse/SurgeryCollapse: cite Hatcher, Chapter 0 instead of Example 0.2
78f20eac Lib/AlgebraicTopology/Hurewicz: cite Hatcher, Theorem 4.32 for the statement only
c546deb1 Lib/Topology/Dimension/CubeBoundaryThreeCells/Cells: cite the lemmas that prove presentation independence
24c63352 Lib/Geometry/Manifold/Morse/SurgeryWindows: state the dimension and smoothness hypotheses in three docstrings
a86bc165 Hopf/Proof/Analysis/Complex/RiemannMapping/TriangleNormalization: describe discCoordinate as defined
5f643949 Lib/reports: correct the verbatim claim of wave-1/prism.md
c5c15a34 Lib/reports: correct the proof-numbering explanation of wave-2/collar.md
ff5a9c4f Lib/reports: correct the cause of the 35 hash changes in wave-2/morselemma.md
cac021a1 Lib/reports: correct wave-2/cube3.md to four declarations widened for dead code
c1bafcf0 Lib/reports: note that the residue lift example is the A : AddCommGrpCat.{0} special case
```

## Left

1. **The 36 dead private lemmas of cube3** (owner's call); deleting `square_intrinsic_face` and
   `square_unit_mesh_endpoint_case` would let the four declarations of W2-2 go private again.
   `cat Lib/reports/wave-2/cube3/notneed.txt`
2. **Misnamed groups** (REVIEW-WAVES §2 finding 6, W1-11, W2-9; owner's call): `SingularHomology.formalMap_*`
   (lemmas about `SingularMayerVietoris.formalMap`), `SingularHomology.integerTrilinear*`,
   `chainTrilinearLift`, `formalChains_trilinear_ext`, `Hurewicz.Prism.straightenedTwoCycle{,_class}`, the
   nine names declared into Mathlib's `Real`/`expNegInvGlue` namespaces.
   `grep -rnE 'SingularHomology\.(formalMap_|integerTrilinear|chainTrilinearLift|formalChains_trilinear_ext)|Hurewicz\.Prism\.straightenedTwoCycle|^(theorem|lemma|def) (Real|expNegInvGlue)\.' Lib --include=*.lean`
3. **Collar auxiliary renumbering** (not fixable by context, see hash check): `trans._proof_8/_9`,
   `ofLinearIsometry._proof_3 … _11`. `python3 /home/goblin/.claude/jobs/06995e68/tmp/fix-waves/hashcheck.py | grep -A12 COLLAR`
4. **Other old docstrings in the two `Hopf/Proof/…/RiemannMapping` modules** (W2-7 names them as vague; only
   `discCoordinate` was in the fix list), e.g. `punctureMap` ("obtained by removing the basepoint
   direction"). `grep -n '^/--' Hopf/Proof/Analysis/Complex/RiemannMapping/*.lean`
5. **Statement-level 4.32 citations kept** (not proof attributions): `PrismOperator/DegreeTwo` ("Thm 4.32, at
   `n = 2`"), `HurewiczInverse`/`SubdivisionTriangleClass` (first/second half of the `n = 2` case),
   `CubeChainDecomposition/Cycle` ("§4.2, before Theorem 4.32"); `Subdivision/CubeClass` keeps its unchecked
   "cf. Hatcher, §4.1"; `MinimumReduction`'s module docstring keeps "Cf. Milnor, … Theorem 8.1 and its
   corollary". `grep -rn '4\.32\|§4\.1\|Theorem 8\.1' Lib/AlgebraicTopology/Hurewicz Lib/Geometry/Manifold/Morse/SurgeryCollapse --include=*.lean`
6. **Facade `References` sections** of `PrismOperator.lean`, `Subdivision.lean`, `CubeChainDecomposition.lean`
   lost their base `Lib/docs/C.md` pointers in wave 1; not restored (the pieces now carry the pointer).
   `git diff e669bc93 HEAD -- Lib/AlgebraicTopology/Hurewicz/{PrismOperator,Subdivision,CubeChainDecomposition}.lean | grep -n 'C.md'`
7. **Tool requests** of REVIEW-WAVES §4 (`split_module.py` blank-line extension, `envdiff` instance-path and
   lift classes): not this seat's.
8. Untouched by rule: `NEXT_STEPS.md`, `Lib.lean`, `TEXTBOOK.md`, `DECOMPOSITION.md`, `CORRESPONDENCE.md`,
   `MERGE.md` files. `git diff --name-only 08aa22ea HEAD -- NEXT_STEPS.md Lib.lean TEXTBOOK.md DECOMPOSITION.md CORRESPONDENCE.md 'Lib/reports/*/MERGE.md'` (empty)
