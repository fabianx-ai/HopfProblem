# Review of Lib/reports/round-7/packets/RECEIPT-02.md

**Verdict: ACCEPT WITH FINDINGS** — the code changes are sound (pure `.{0}` → `.{u}` lifts with
unchanged statements, correct docstrings and citations, clean hygiene), but two of the receipt's
"not done, because …" reasons are refuted by elaboration, the totals row is arithmetically wrong,
and the envdiff reconciliation rests on artefacts that no longer exist anywhere.

## Findings

1. **[wrong receipt] [incomplete] Coproduct.lean: "the pin is not a local fix" is false.**
   Receipt l.81-100 says `Coproduct.singularChainsFiniteBiproducts` cannot be stated at
   `ModuleCat.{u} ℤ` because `HasFiniteBiproducts.of_hasFiniteProducts` gets stuck on a universe
   constraint, and "every declaration of the file needs that instance … so the pin is not a local
   fix". The stuck constraint reproduces (my scratch `CoproductTest.lean`, same error text), but
   the instance is obtainable at a bare `u` by a different proof term:
   ```lean
   example : HasFiniteBiproducts (ChainComplex (ModuleCat.{u} ℤ) ℕ) := Abelian.hasFiniteBiproducts
   ```
   elaborates with `import Lib.AlgebraicTopology.SingularHomology.Coproduct` (scratch
   `CoproductTest2.lean`, l.8, no error; `Abelian (ChainComplex (ModuleCat.{u} ℤ) ℕ)` is found by
   `inferInstance`). Both pinned instance theorems (`singularChainsFiniteBiproducts` l.62 and
   `homologyFiniteBiproducts` l.317, branch head) use the failing proof term, and the seven other
   pins (l.323-424, `K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ`) are abstract homological algebra
   over `⨁ K`, not tied to `singularComplex`. The fix is a one-token change of the proof term in
   two places. What should happen: the item is re-opened, or the receipt states the real reason
   (the author only tried `of_hasFiniteProducts` and an explicit `HasFiniteProducts` instance). I
   did not test whether the seven downstream declarations then go through.

2. **[wrong receipt] [incomplete] PositivePrimitives / Vanishing: the coefficient pins are not
   "forced by the interface".** Receipt l.18-20 and l.31-32 say the remaining
   `AddCommGrpCat.{0}` pins are forced by `SingularCochains.complex`, `.chains`, `.dualComplex`,
   `.pullback` "which are pinned at `ModuleCat.{0} ℤ` / `AddCommGrpCat.{0}`". Only `chains` is
   pinned. `Lib/AlgebraicTopology/SingularCochains.lean` has
   `dualComplex (A : AddCommGrpCat.{w}) (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)` (l.82),
   `complex (X : Type) (A : AddCommGrpCat.{w}) : CochainComplex AddCommGrpCat.{w} ℕ` (l.122),
   `pullback (A : AddCommGrpCat.{w})` (l.126), `pullbackHomotopy (A : AddCommGrpCat.{w})` (l.160),
   `homotopyEquivCohomologyIso (A : AddCommGrpCat.{w})` (l.175). Scratch `CoefficientTest.lean`
   (rc=0, importing `Lib.AlgebraicTopology.SingularCochains.Vanishing`) restates
   `cohomology_subsingleton_of_homotopyEquiv` and `cohomology_subsingleton_iff_of_homeomorph`
   with `(A : AddCommGrpCat.{w})` and the *identical* proof bodies, and
   `pointCocycle_boundary` at `.{w}` given its exactness input — all elaborate. So at least
   Vanishing l.61/72/82 and PositivePrimitives l.73/83/89/104/111/149/158 (the `A :
   AddCommGrpCat.{0}` binders) are not forced by the imported interface; the genuinely forced ones
   are the `ModuleCat.{0} ℤ` pins on `pointFreeModule`/`single₀` (via `chains`) and the two
   `ULift.{0} ℤ` in Vanishing (via `LocalUCT`). Whether the private helpers
   `pointChainHomotopyEquiv`/`dualPointSingle_exactAt` lift is untested (private, unreachable from
   a scratch file) but nothing in their statements needs `A` at universe 0. Relatedly, both new
   module docstrings say "stated for an arbitrary coefficient group" while every statement takes
   a universe-0 group.

3. **[wrong receipt] Totals row does not add up** (receipt l.192). "101 of 126, 25 left (9
   Coproduct, 15 PositivePrimitives, 7 Vanishing)": 9+15+7 = 31, not 25; the per-file numbers
   give done = 2+36+5+4+5+29+22 = 103 (the receipt drops PositivePrimitives' 2) and total =
   17+7+36+5+4+9+5+29+22 = 134. Correct row: 103 of 134, 31 left. The per-file numbers themselves
   are right (verified by counting `.{0}` before/after in each file).

4. **[incomplete] The envdiff section cannot be checked against anything.** There is no
   `envdiff.json`/`.txt` beside the receipt; the only round-7 envdiff in the repo is the merged
   `Lib/reports/round-7/envdiff-merged-d950428a.json`, in which `changed_type_source` is empty and
   all 1028 changed names sit under `changed_type_proof_naming` (so the 233 cannot be isolated).
   The receipt cites `dump_base.jsonl`/`dump_after.jsonl` from the worktree `/home/goblin/hopf-r7-p02`,
   which no longer exists; the job dir `…/tmp/r7-p02/` holds only `*.bak` files and the axiom log.
   The receipt's arithmetic is internally consistent (97 direct + 136 downstream = 233; the 11
   direct names I spot-checked are in the merged `changed_type_all`), but "0 lost, 0 added, 233
   explained" is unverifiable. Also the per-file "36 of 36 / 29 of 29 / 22 of 22 generalised" are
   `.{0}` *occurrence* counts while the envdiff table's 35 / 27 / 19 are *declaration* counts
   (`shortMap` carries two pins, `homologyBiprodEquiv_desc` three, ModuleHomology's old module
   docstring two); the receipt lists 35 names under "all 36" without saying so.

5. **[wrong receipt] [nit]** Receipt l.168: "the namespace `FirstHurewicz.ChainHomology` does not
   exist". It does not exist in `Lib`, but `Hopf/LibShims.lean:39-41` has
   `namespace FirstHurewicz export SingularChains (ChainHomology.shortCycleClass …)`, which creates
   exactly those aliases. The docstring rewrite is still right (Lib must not document Hopf-side
   aliases); the stated reason is inexact.

6. **[nit]** Receipt l.14: "all 6 public declarations already had one; the 5 missing ones are
   private". PositivePrimitives has 4 public declarations (all documented) and 7 private ones, 2
   documented and 5 not. Six docstrings and five gaps are right; the public/private split is not.

7. **[nit]** Receipt l.104: "about a third of the file is in that namespace" — 113 of 218
   declarations of CrossProduct.lean are `PeriodTorusHigherHomology.*` (over half). Immaterial to
   the deletion, which is correct.

8. **[citation] [nit, unsure]** CircleProduct.lean module docstring now cites Hatcher "§2.2
   (Mayer–Vietoris, and the torus example)". I recall the Mayer–Vietoris examples in §2.2 being
   `Sⁿ`, the Klein bottle and a few others; I cannot confirm a torus example there. Everything
   else cited (Thm 2.10, Cor 2.11, Cor 2.14, Thm 2A.1, Prop 2.6, Thm 3.2, §3.1, §3.B) is the
   stated result.

Hygiene: no `sorry`, `axiom`, `maxHeartbeats`, `unsafe`, `native_decide`; no `@[simp]` added or
removed; no `noncomputable` added; no `private` removed (the only `private` line in the diff is
the universe change on `cochainMap_d_succ`). `grep -rn "import Hopf" Lib --include=*.lean` is
empty at head. All 12 commits carry `Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>`
plus a `Claude-Session:` trailer — not the repo's usual trailer, recorded as instructed, not a
finding.

## Claims checked

| claim | status | how |
|---|---|---|
| 12 commits, 11 file commits + receipt, one commit per file, hashes as listed | verified | `git log 9552305f..f46bda99^2`; subjects match files; `git diff --stat` = 11 .lean + receipt |
| PositivePrimitives: 2 of 17 pins lifted (`homotopy_on_cocycle_succ`, `cochainMap_d_succ`) | verified | `.{0}` count 17→15; diff |
| PositivePrimitives: remaining 15 "forced by complex/chains/dualComplex/pullback pinned at .{0}" | **refuted** | `SingularCochains.lean` l.82/122/126/160/175 are `.{w}`; scratch `CoefficientTest.lean` rc=0 (finding 2) |
| Vanishing: 0 of 7, forced by the same interface and `uliftIntCohomologyEvaluation` | **partly refuted** | 3 `A : AddCommGrpCat.{0}` pins lift with identical proofs; the 2 `ULift.{0}` and the 2 depending on `pointCochain_exactAt_positive` not tested |
| Vanishing: 2 citations replaced ("FREE owner", "repository's coefficient convention") | verified | diff |
| Chains: 36 of 36 lifted, all in `ChainHomology.*`, statements otherwise unchanged | verified | `.{0}` 36→0; read every hunk; only `.{0}`→`.{u}` and `universe u` |
| Chains list of "36" names | partly | list has 35 names; 36 is the occurrence count (`shortMap` ×2) |
| CirclePaths: 88 docstrings added (88/88), 5 pins lifted | verified | `^/--` 0→88, 88 declarations; `.{0}` 5→0 |
| CircleProduct: 4 pins; Cor 2.11 was cited for Künneth and is now §3.B / §2.2 / Cor 2.14 | verified | diff; Cor 2.11 is homotopy-invariance of homology, Cor 2.14 is `H̃(Sⁿ)` |
| Coproduct: 0 of 9, obstacle "not a local fix" | **refuted** | `Abelian.hasFiniteBiproducts` elaborates at `.{u}` (finding 1); the stuck constraint itself reproduces |
| Coproduct: 2 narrative sentences removed; finiteness stated against Prop 2.6 | verified | diff; Prop 2.6 is `H_n(⊔X_α) ≅ ⊕H_n(X_α)` |
| CrossProduct: 4 narrative pieces deleted, 5 pins lifted | verified | diff; `.{0}` 5→0 |
| FirstHurewicz: 16 docstrings, Thm 2A.1 | verified | `^/--` 0→16; all 16 read against statements; 2A.1 is `π₁^{ab} ≅ H₁` for path-connected `X` |
| HomotopyInvariance: 3 docstrings name Thm 2.10 / Cor 2.11 / Mathlib lemma; 0 of 8 binders, forced | verified | diff; `TopCat.Homotopy.singularChainComplexFunctorObjMap` exists in Mathlib; `SingularMayerVietoris.SingularHomology (Y : Type)` (MayerVietoris.lean:928) forces `Type` |
| MayerVietoris: 29 of 29 lifted, l.600-930 block | verified | `.{0}` 29→0; every hunk in that range; 27 declarations (`homologyBiprodEquiv_desc` ×3) |
| ModuleHomology: old docstring named 8 declarations not in the file; rewritten; 22 of 22 | verified / partly | `git show 9552305f:…ModuleHomology.lean` l.14-42; `.{0}` 22→0 (19 declarations + `shortMap` ×2 + 2 in old docstring); "namespace does not exist" see finding 5 |
| ModuleHomology `ℤ` not generalised because `shortCycleModule` is in Chains.lean | verified | Chains.lean `shortCycleModule … : Module ℤ (ShortCycle S)`, statements use `→ₗ[ℤ]` |
| 104 docstrings added, 13 citations, 0 of 13 binders | verified (counts) | 88+16; 2+1+2+4+1+3; 2+3+8 |
| 101 of 126 pins, 25 left | **refuted** | 103 of 134, 31 left (finding 3) |
| Docstring names cited in module docstrings exist | verified | grep for 27 names (`pointCochain_exactAt_positive`, `sigmaHomologyEquiv_symm_single`, `crossProductTriangle`, …) at branch head |
| Mathlib file/lemma citations exist (`AlternatingConst.lean`, `ShortComplex/ModuleCat.lean` `moduleCatHomologyIso`, `QuasiIso.lean` `quasiIsoAt_iff_isIso_homologyMap`) | verified | grep in `.lake/packages/mathlib` |
| Axiom audit: 3352 lines, 4 axiom sets | verified | `…/tmp/r7-p02/ax.log`, `axiom_full.log` |
| envdiff: 0 lost / 0 added / 233 explained | **unverifiable** | no per-packet artefact exists (finding 4) |
| No later branch changed the semantics of these files | verified | `git log f46bda99..39f1d12b -- <11 files>`: only `a3c05a72` (Coproduct docstring note) and `ecf64466` (moves `homotopy_on_cocycle_succ` out to `CochainComplex.homotopy_on_cocycle_succ`) |

Docstrings checked against their statements (63): CirclePaths — `circleTranslation`,
`circleTranslation_apply`, `circleTranslationHomotopy` (`(1-t)·a`), `circleTranslation_singularHomologyMap`,
`positiveLoop`, `positiveCircleCross` (`H_n(X) → H_{n+1}(S¹×X)`), `crossProductEdge_boundary_of_right_cycle`,
`crossProductEdge_path_boundary` (`{y}×b − {x}×b`, sign checked), `const_prodMk_id_eq_crossInsertLeft`,
`biprodElement`, `biprod_lift_f_apply`, `biprodElement_desc`, `biprodElement_boundary`,
`biprod_lift_eq_boundary`, `twoChainMiddle`, `twoChainMiddle_rightMap`, `twoChainMiddle_boundary`
(`∂a = ι z`, `∂b = −ι z`), `connectingHomomorphism_twoChain`, `circleProjection_positiveCircleCross`,
`quarterIntersection`, `threeQuarterIntersection`, `uPath`, `vPath`, `uCirclePath_apply`, `vCirclePath_apply`,
`quarterLoop`, `uCirclePath_trans_vCirclePath`, `quarterTranslation_zero`, `quarterLoop_eq_translation`,
`arcSumCycle`, `quarterIntersectionSection_component`, `quarterIntersectionSection_toU`,
`intersectionDifferenceCycle` (`¾-push − ¼-push`, class `(−[b],[b])`),
`intersectionDifferenceCycle_class_coordinates`, `uCrossChain_boundary`, `vCrossChain_boundary` (sign),
`circleConnecting_positiveCircleCross_cycleClass`, `circleBoundaryCoordinates_positiveCircleCross`,
`circleBoundary_positiveCircleCross` (left inverse), `circleProductHomologyEquiv_positiveCircleCross`
(`(0,b)` in `H_{n+1}(X) × H_n(X)`), `circleProductHomologyEquiv_symm_eq_section_add_cross`,
`positiveCircleCross_naturality`, `positiveCircleCross_arcSum_cycleClass`. FirstHurewicz — all 16
(`inverseHurewiczMap : H₁ → π₁^{ab}`, left/right inverse orientation, `triangleFacePath` = cast of
`simplexPath (σ ∘ face i)`, `singularH1EquivOfPi1_hurewiczFunction` = `(e g).toAdd`).
HomotopyInvariance — 3; PositivePrimitives — `homotopy_on_cocycle_succ` (`f c = d(h c) + g c`) and
the module docstring's "totally disconnected" route (matches Mathlib's
`singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` used in the proof); Vanishing — the
UCT remark on `uliftIntCohomology_subsingleton_of_projective_of_homology`. No wrong direction,
degree, sign or invented name found.

## Not checked

* The envdiff table (233 rows) — no per-packet dump or envdiff artefact exists (finding 4).
* `lake build` outputs — not rerun (forbidden); the axiom log was read instead.
* Whether *all* of Coproduct.lean and the private helpers of PositivePrimitives lift once the
  instance / coefficient universe is generalised; I tested the instance and three public
  theorems only (4 elaborations total).
* The `: Type` binder counts (2 / 3 / 8) — my grep counts `: Type)`/`: Type}` more broadly (4 / 6 /
  25); the packet's counting rule is not stated, so I did not adjudicate.
* The claim of 17 (Chains) and 100 (MayerVietoris) forced `X : Type` binders — not counted.
* Hatcher's "torus example" in §2.2 (finding 8) — from memory only.
* Docstrings in files where the receipt added none (MayerVietoris, CrossProduct, Chains, …) — out
  of the packet's scope; not sampled.

## Tool notes

* A packet receipt that reconciles an envdiff must ship the `envdiff.json`/`.txt` (and ideally
  the two dump files) beside itself; a table of counts with the source dumps in a deleted
  worktree is not reviewable. The merged `envdiff-merged-d950428a.json` puts every changed name
  under `changed_type_proof_naming` and leaves `changed_type_source` empty, so it cannot stand in.
* "Forced by X" claims should quote the pinned signature of X. Both refuted reasons here would
  have been caught by the author had the receipt required pasting the signature
  (`complex (X : Type) (A : AddCommGrpCat.{w})` is one grep away).
* "Obstacle recorded" should list what was tried; here the Coproduct entry did, and that is
  exactly what made it easy to see that the abelian route was not tried.
* State whether per-file "N of N" counts are occurrences or declarations; the receipt mixes the
  two between its per-file sections and its envdiff table.
* Scratch files used: `/home/goblin/.claude/jobs/06995e68/tmp/review-pass/r7-packet-02/{CoproductTest,CoproductTest2,CoefficientTest}.lean`, `branch.diff`.
