# Integration review 7 — the cleanup round after the textbook audit (2026-09-20/21)

Coordinator: Claude Fable 5.1 (this seat); work by Opus 5 agents in seeded worktrees, one branch each,
merged in arrival order. Base: `46c22597` (hand-off head after the audit and the Jev runs). Source of the
work list: `Lib/reports/textbook-audit/AUDIT.md` (cross-cutting findings 2, 3, 6, 8, the per-file table)
and `NEXT_STEPS.md`. Owner decision 2026-09-20: this work goes to Opus 5 agents, not to the external
seats; integrations are per-commit history, never one squash.

## 1. Stage 1: the scriptable block (merged at `9552305f`)

| branch | what | receipt |
|---|---|---|
| `r7/preamble` | `set_option maxSynthPendingDepth` removed from 108 of 110 files; the stock 22-namespace `open scoped` block removed from 96 files and narrowed per file by 1,565 single-file compiles (no file needs BigOperators, Fin.NatCast, MatrixGroups, Modular, Pointwise, RealInnerProductSpace or TensorProduct); 90 unused `universe u v` lines and 137 unused `local notation` lines deleted. 1,074 lines removed. Envdiff PASS, 0 source declarations changed. **Finding:** `maxSynthPendingDepth 3` is not cosmetic: in four files (`Cousin`, `Collar`, `Morse/Birth`, `SquareRoot`) removing it changed the stored instance path for `NormedSpace ℝ ℝ` (a defeq but different type term), invisible to the build, caught by the environment diff; restored there. | `Lib/reports/round-7/preamble/RECEIPT.md` |
| `r7/names` | 28 `_mo1973_NNNN` names stripped (86 occurrences, 12 files, 0 collisions; map `names/rename.txt`); `Sites/Leray/DegreeZero.lean` and `LinearAlgebra/Dual/Contragredient.lean` deleted (**`DegreeZero.lean` a true Mathlib duplicate; `Contragredient.lean` is not (corrected)** — five of its seven declarations have no twin at all and `contragredient`'s named twin `Representation.dual` has a different type, linear maps rather than linear equivalences; neither file has consumers, and the five twin-less deletions are dead code, recorded as a protocol exception in the names receipt) and `MorseCancellation.range_tanh` replaced by `Real.tanh_bijOn`; the 13 modules missing from `Lib.lean` imported (443 of 443); the `Hopf/` halves of 12 `center-solution` extraction commits cherry-picked as 10 commits (one already applied, two forced into one by the stock/proof split; the first also removed the duplicate `SpecialPeriods.Threefold.Star.Input` that made a joint `Solution`+`Lib` dump abort). **Not done, with reasons:** `Cohomology/AddCommGroup.lean` (the `Ext` group instance is load-bearing for instance search on `Sheaf.H`), `Sheaves/SheafificationLocal.lean` (proves three facts where Mathlib has two), `GroupTheory/SplitExtension.lean` (Mathlib's needs the conjugation action, the consumer has an independent homomorphism), `hasDerivAt_tanh`/`contDiffAt_artanh` (not in this Mathlib: upstream candidates, the audit was wrong). Envdiff: every lost name accounted for in the receipt. | `Lib/reports/round-7/names/RECEIPT.md` |

Checks at `9552305f`: `lake build Lib` 9,150 jobs, chain 9,189, `Lib.AxiomAudit` 3,352 probes all standard, census 123.

## 2. Stage 2: the checklist packets (merged at `d950428a`)

Ten packets (`Lib/reports/round-7/packets/packet-NN.md`, 261 files with counted work: manuscript-only citations, docstring coverage under 30%, `.{0}` universe pins, `: Type` binders), one Opus agent each, one commit per file **except in packets 01 and 03 (corrected)** — packet 01's `067ee091` ("use the repository's short citation keys") touches 17 `.lean` files, and packet 03's `f31d9b09` touches six Leray files (disclosed in RECEIPT-03); the other eight packets comply — receipts `RECEIPT-NN.md`. Rules: no statement changed beyond a universe or binder generalisation, no hypotheses added, nothing deleted; a generalisation that cascades is recorded with its forcing declaration and left.

| packet | files | citations | docstrings added | pins lifted / forced | binders widened / forced | envdiff (own branch) |
|---|---:|---:|---:|---|---|---|
| 01 Algebra/Homology, Ext, cochains | 59 | 5 coordinates, 41 reference blocks | 287 | **116 / 27 (corrected)** | 17 / 57 (the receipt's rule is unstated; a reviewer's regex gives 72 total / 55 forced) | PASS, **314 changed source types of 407 explained (corrected; the receipt says "407 of which source: 314" — the other 93 are auxiliaries the tool does not judge)** |
| 02 SingularHomology core | 11 | 13 | 104 | **103 / 31 (corrected)** | 0 / 13 | PASS, 233 explained (unverifiable: no per-packet envdiff in the tree).  Two "forced" reasons refuted on review: `Coproduct.lean` lifts via `Abelian.hasFiniteBiproducts`, and the `PositivePrimitives`/`Vanishing` coefficient pins are not forced by the cochain interface |
| 03 Pontryagin, Torus, Abelian, Leray stalks | 32 | 116 coordinates | 171 | 13 / 146 | **0 widened; forced count inconsistent in the receipt, 106 by its rows (corrected — "61" appears nowhere in RECEIPT-03, which says "99 left" while its own rows give 34 false positives + 106 forced = 140)** | source-level check (dump starved); 13 explained |
| 04 Leray, Morse, Immersion | 18 | 18 module docstrings | 335 | 26 / **80 (corrected)** | 13 / — (six un-widened `: Type` binders in `AdaptedWindows.lean` were neither widened nor listed) | PASS, 129 explained; the +1 auxiliary is `…higherDirectImageResolutionSheafificationIso._proof_5` |
| 05 Whitney, Transversality | 4 | 3 module docstrings | 385 | 0 / 0 | 0 / 0 | PASS, 0 changes |
| 06 Whitney rest, exterior powers, group theory | 15 | 9 files | **392 (corrected)** | **0 (corrected) / 1** | 6 / — | PASS, 8 explained.  **(corrected)** the receipt's "6 pins lifted" and "6 binders widened" are the same six edits counted twice: `TransvectionReduction.lean` has no universe pin at base |
| 07 Dimension, Čech, Wang, gluing | 32 | 30 module + 297 declaration docstrings | 245 | 1 / 29 | 7 / **62 (corrected)** | PASS, 30 source of 56 explained |
| 08 Čech, pushforward | 32 | 42 (a per-file column sum, not a figure the receipt states) | **35 (corrected)** | **108 / 226 (corrected)** | 0 / 8 | PASS, 233 explained.  **(corrected)** the five `ConstantProduct*`/`ConstantSheafH1` files are forced by `SingularCochains.chains`, not by `ConstantSheafCohomology.pullback` as the receipt said |
| 09 Sheaves | 34 | 34 module docstrings | 83 | 77 / **317 (corrected)** | ~10 / 37 | PASS, 159 explained |
| 10 SingularCochainSheaf | 24 | 24 module docstrings | 19 | 6 / rest (one of `PrimitivesH1`'s 14 "forced" pins is not forced) | 0 / 1 | PASS, 6 explained; the +1 constant is `TopCat.SingularCochainSheaf.unit._proof_1` |
| **total** | **261** | | **≈2,057** | **≈467 lifted** | **≈53 widened** | |

Forcing declarations that hold the remaining pins (each named in a receipt; lifting them is a judgement-round item because their consumers are in several packets): `AlgebraicTopology.SingularCochains.complex`/`.chains` (`X : Type`, `AddCommGrpCat.{0}`; packet 01 lifted the cochain interface itself, so packets 02 and 10 can be re-run), `TopCat.SheafH1.unitSheaf` and `ConstantSheaf.integralSheaf`, `OpenRestriction.freeOpen`/`cohomologyEquiv`, `Sheaf.cohomologyAddCommGroup` (the load-bearing instance), `TopCat.Sheaf.pushforwardAdditive` (packet 07 lifted it; the Leray cluster in packet 04 can be re-run), `ConstantSheafCohomology.pullback`, `HasExt.{0}` in `H1Vanishing/Flasque.lean`, Mathlib's `ModuleCat.hasLimits` at `max v w`. Two agents noted that the audit's `: Type` counts were regex false positives on `Type u` binders.

Attribution: packet 02's commits carry `Co-Authored-By: Claude Opus 5 (1M context)` instead of the Fable trailer; the agent reasoned that Opus did the work. Left as is.  **(corrected)** all ten packets were done by Opus agents, so packet 02's twelve commits carry the *accurate* trailer and the other 248 do not; this note had the anomaly the wrong way round.

## 3. Checks on the merged head `d950428a`

Receipts: `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}`; build logs in the session scratch (summary lines below).

| check | result |
|---|---|
| `lake build Lib` | green, 9,150 jobs, 332 modules recompiled, 474 s |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,189 jobs, 29 modules recompiled, 371 s; the final theorem reports `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | 3,352 probes, all subsets of `{propext, Classical.choice, Quot.sound}`; no `sorryAx` |
| `scripts/lib_stock_census.py --check` | 123 (unchanged) |
| environment diff, `Lib` at `9552305f` (21,719 constants) against `d950428a` (21,721) | PASS: 0 source declarations lost, 0 added; 1,028 source names with a changed type hash, all in the tool's `PROOF-NAMING` class; 0 in the unexplained bucket; 0 module moves; the +2 constants are the two auxiliaries the packet-04 and packet-10 receipts recorded.  **(corrected)** this row originally described `PROOF-NAMING` as "the tool's unchanged-dependency class (a universe or binder generalisation keeps the `uses` set)" and presented "0 in the unexplained bucket" as evidence that the statements were preserved.  The class tests only that the name's `uses` set, restricted to the reported `Lib.*` modules and with `._proof_n` edges dropped, is unchanged; it sees nothing that names only Mathlib or core constants.  An added `[MetrizableSpace X]`, a conclusion weakened from `IsIso` to `Mono`, or a body-level `∃ Y : Type` widened to `∃ Y : Type u` all pass it (demonstrated on the tool with a two-row table).  So this check is **necessary, not sufficient**: it shows nothing lost, nothing added, no `Lib`-internal dependency changed, and statement preservation rests on the per-packet receipts.  Mitigation done: 120 of the 1,028 sampled, declaration headers at `9552305f` vs `d950428a` identical after stripping universe annotations (115 identical, 4 auto-generated, 1 benign binder move); and none of the 74 `: Type` binder widenings in the stage-2 diff reuses an existing universe parameter of an already-polymorphic declaration, so the third shape does not occur in round 7.  Tool fix wanted: hash the type with universe parameters instantiated at 0, and include Mathlib constants in `uses` |
| git | ten merges in arrival order, 0 conflicts, **260 commits + 10 merges (corrected; "270 commits" counted the merge commits: `git rev-list --count --no-merges 9552305f..d950428a` = 260 = 26+5+33+25+35+16+12+33+56+19)**, 264 files, +9,438 / −2,582 lines |

## 4. What remains (the judgement round)

- The chokepoint pins above, then a second checklist pass over the files they release.
- The 25 files over 1,800 lines to split by topic (`AUDIT.md` finding 7; the auditors' finding lines are the cut lists), first `PrismOperator` (the general operator is ~300 of 5,303 lines), `Connection`, `SurgeryCollapse`, `CrossProduct`, `MorseLemma`, `Collar`, `RiemannMapping`, `Transversality/Basic`, `Cubic`, `CubeBoundaryThreeCells`, `VanKampen.lean`.
- The 20 verbatim-moved D files: extract the general islands the auditors named, return the rest to `Hopf/Proof`.
- The internal duplicates (finding 5): `VanKampen.lean` vs the split, `Chains.lean` vs the PR files, barycentric subdivision twice, MV naturality twice, Hatcher 2.6 twice, the H¹-first sheaf pipeline, `FunctionSheaf` vs `DependentFunctionSheaf`, the constant ℤ sheaf and global sections under several names.
- The names the packets could not change (renames delete declarations): `MorseCancellation.*` on real analysis, `ThreefoldGluing`/`SpecialPeriods.Threefold.Star` on generic glue data, `NativeTransversality.At`, "native" throughout.
- The 40 Jev two-letter disagreements and the auditors' ten low-confidence calls, for a reader.
- A fresh-reviewer pass over this round's receipts (one reviewer per receipt).

## 5. Corrections after the fresh-reviewer pass (2026-09-21)

Twenty-one independent reviewers went over the twelve round-7 receipts, the seven round-8 branch
receipts, the round-8 merge receipt and the two coordinator reviews; verdicts and the consolidated
fix list are in `Lib/reviews/REVIEW-7-8.md`, the reviews themselves in
`Lib/reports/review-7-8/*.md`.  All twenty-one: ACCEPT WITH FINDINGS.  **Nothing unsound was found**
— no weakened statement, no added hypothesis, no lost declaration whose content is gone, no
`sorry`/`axiom`, no merge that dropped a line from either parent.  What follows corrects this file;
each packet receipt carries its own dated corrections section.

1. **§3's environment-diff row overstated what the merged `PASS` proves**
   (`Lib/reports/review-7-8/r7-merged-head.md`, finding 1).  Corrected in place: the `PROOF-NAMING`
   class means the `Lib`-internal `uses` set is unchanged, which an added hypothesis or a weakened
   conclusion naming only Mathlib constants also satisfies.  The row now states what the class tests,
   that it is necessary and not sufficient, and what was sampled instead.

2. **Two §2 table cells misquoted their receipts** (finding 4), corrected in place: packet 01's "407
   changed types explained" is "**314 source** of 407" in RECEIPT-01, and packet 03's binder cell
   "0 / 61" quotes a number that **appears nowhere** in RECEIPT-03 — that receipt says "0 widened; 99
   left", while its own per-file rows give 34 false positives + 106 forced = 140.  The cell now reads
   "0 widened; forced count inconsistent in the receipt, 106 by its rows".

3. **Seven further §2 cells carried receipt arithmetic that the reviewers refuted**, corrected in
   place from the per-file tables: packet 01 pins 119/24 → **116/27**; packet 02 101/25 →
   **103/31**; packet 04 81 → **80** forced; packet 06 docstrings 395 → **392** and pins 6 → **0**
   (the six "pins" were the six binder widenings, counted twice); packet 07 binders 59 → **62**;
   packet 08 118/217 → **108/226** and docstrings 33 → **35**; packet 09 316 → **317**.  Packet 08's
   wrong pair had also propagated into the commit message of `835b39be` and into this table.  The
   two "forced by" attributions the reviewers refuted are noted in the cells for packets 02 and 08,
   and the un-named auxiliaries for packets 04 and 10 are now named.

4. **"One commit per file" is not literally true** (finding 5), qualified in §2: packet 01's
   `067ee091` touches 17 `.lean` files and packet 03's `f31d9b09` six Leray files (the latter
   disclosed in its receipt).  The other eight packets comply.

5. **The commit count in §3 counted merges** (finding 7): **260 commits + 10 merges**, not 270.
   The attribution note is also turned the right way round: all ten packets were Opus work, so packet
   02's trailer is the accurate one.

6. **§1's `r7/names` row called `Contragredient.lean` a true Mathlib duplicate** (see
   `Lib/reports/review-7-8/r7-names.md`, finding 1).  Corrected in place: five of its seven
   declarations were deleted with no twin at all, and `contragredient`'s named twin has a different
   type.  Neither file has consumers, so nothing is at risk; the names receipt now carries the
   per-declaration table and records the five as a protocol exception.

7. **Cross-cutting, for the next round** (`REVIEW-7-8.md` §§2–4).  (a) None of the ten packet
   receipts committed its `envdiff.json`; reviewers had to reconcile against the merged file, which
   cannot attribute a downstream change to a packet.  Every receipt now commits its
   `envdiff.json`/`.txt` beside itself.  (b) Every round-7 packet receipt had at least one number
   disagreeing with its own per-file table: totals are to be computed from the table by script, and
   occurrence vs declaration counts labelled.  (c) "Forced by X" must quote X's signature and name
   the binder, and list the file's *own* chokepoints too; "not done, because X" must ship a one-file
   reproduction.  (d) `autoImplicit` is **on** in half of `Lib` (no `leanOptions` in
   `lakefile.toml`), so compile-based minimisation must set it off first — the preamble receipt's and
   the brief's premise was wrong.  (e) About fifteen textbook item numbers in ~600 docstrings read
   were copied from the audit's twin column without checking; citations so copied are to be marked
   "cf." unless verified.
