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
| `r7/names` | 28 `_mo1973_NNNN` names stripped (86 occurrences, 12 files, 0 collisions; map `names/rename.txt`); `Sites/Leray/DegreeZero.lean` and `LinearAlgebra/Dual/Contragredient.lean` deleted (true Mathlib duplicates, no consumers) and `MorseCancellation.range_tanh` replaced by `Real.tanh_bijOn`; the 13 modules missing from `Lib.lean` imported (443 of 443); the `Hopf/` halves of 12 `center-solution` extraction commits cherry-picked as 10 commits (one already applied, two forced into one by the stock/proof split; the first also removed the duplicate `SpecialPeriods.Threefold.Star.Input` that made a joint `Solution`+`Lib` dump abort). **Not done, with reasons:** `Cohomology/AddCommGroup.lean` (the `Ext` group instance is load-bearing for instance search on `Sheaf.H`), `Sheaves/SheafificationLocal.lean` (proves three facts where Mathlib has two), `GroupTheory/SplitExtension.lean` (Mathlib's needs the conjugation action, the consumer has an independent homomorphism), `hasDerivAt_tanh`/`contDiffAt_artanh` (not in this Mathlib: upstream candidates, the audit was wrong). Envdiff: every lost name accounted for in the receipt. | `Lib/reports/round-7/names/RECEIPT.md` |

Checks at `9552305f`: `lake build Lib` 9,150 jobs, chain 9,189, `Lib.AxiomAudit` 3,352 probes all standard, census 123.

## 2. Stage 2: the checklist packets (merged at `d950428a`)

Ten packets (`Lib/reports/round-7/packets/packet-NN.md`, 261 files with counted work: manuscript-only citations, docstring coverage under 30%, `.{0}` universe pins, `: Type` binders), one Opus agent each, one commit per file, receipts `RECEIPT-NN.md`. Rules: no statement changed beyond a universe or binder generalisation, no hypotheses added, nothing deleted; a generalisation that cascades is recorded with its forcing declaration and left.

| packet | files | citations | docstrings added | pins lifted / forced | binders widened / forced | envdiff (own branch) |
|---|---:|---:|---:|---|---|---|
| 01 Algebra/Homology, Ext, cochains | 59 | 5 coordinates, 41 reference blocks | 287 | 119 / 24 | 17 / 57 | PASS, 407 changed types explained |
| 02 SingularHomology core | 11 | 13 | 104 | 101 / 25 | 0 / 13 | PASS, 233 explained |
| 03 Pontryagin, Torus, Abelian, Leray stalks | 32 | 116 coordinates | 171 | 13 / 146 | 0 / 61 | source-level check (dump starved); 13 explained |
| 04 Leray, Morse, Immersion | 18 | 18 module docstrings | 335 | 26 / 81 | 13 / — | PASS, 129 explained |
| 05 Whitney, Transversality | 4 | 3 module docstrings | 385 | 0 / 0 | 0 / 0 | PASS, 0 changes |
| 06 Whitney rest, exterior powers, group theory | 15 | 9 files | 395 | 6 / 1 | 6 / — | PASS, 8 explained |
| 07 Dimension, Čech, Wang, gluing | 32 | 30 module + 297 declaration docstrings | 245 | 1 / 29 | 7 / 59 | PASS, 30 explained |
| 08 Čech, pushforward | 32 | 42 | 33 | 118 / 217 | 0 / 8 | PASS, 233 explained |
| 09 Sheaves | 34 | 34 module docstrings | 83 | 77 / 316 | ~10 / 37 | PASS, 159 explained |
| 10 SingularCochainSheaf | 24 | 24 module docstrings | 19 | 6 / rest | 0 / 1 | PASS, 6 explained |
| **total** | **261** | | **≈2,057** | **≈467 lifted** | **≈53 widened** | |

Forcing declarations that hold the remaining pins (each named in a receipt; lifting them is a judgement-round item because their consumers are in several packets): `AlgebraicTopology.SingularCochains.complex`/`.chains` (`X : Type`, `AddCommGrpCat.{0}`; packet 01 lifted the cochain interface itself, so packets 02 and 10 can be re-run), `TopCat.SheafH1.unitSheaf` and `ConstantSheaf.integralSheaf`, `OpenRestriction.freeOpen`/`cohomologyEquiv`, `Sheaf.cohomologyAddCommGroup` (the load-bearing instance), `TopCat.Sheaf.pushforwardAdditive` (packet 07 lifted it; the Leray cluster in packet 04 can be re-run), `ConstantSheafCohomology.pullback`, `HasExt.{0}` in `H1Vanishing/Flasque.lean`, Mathlib's `ModuleCat.hasLimits` at `max v w`. Two agents noted that the audit's `: Type` counts were regex false positives on `Type u` binders.

Attribution: packet 02's commits carry `Co-Authored-By: Claude Opus 5 (1M context)` instead of the Fable trailer; the agent reasoned that Opus did the work. Left as is.

## 3. Checks on the merged head `d950428a`

Receipts: `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}`; build logs in the session scratch (summary lines below).

| check | result |
|---|---|
| `lake build Lib` | green, 9,150 jobs, 332 modules recompiled, 474 s |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,189 jobs, 29 modules recompiled, 371 s; the final theorem reports `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | 3,352 probes, all subsets of `{propext, Classical.choice, Quot.sound}`; no `sorryAx` |
| `scripts/lib_stock_census.py --check` | 123 (unchanged) |
| environment diff, `Lib` at `9552305f` (21,719 constants) against `d950428a` (21,721) | PASS: 0 source declarations lost, 0 added; 1,028 source names with a changed type hash, all in the tool's unchanged-dependency class (a universe or binder generalisation keeps the `uses` set); 0 in the unexplained bucket; 0 module moves; the +2 constants are the two auxiliaries the packet-04 and packet-10 receipts recorded |
| git | ten merges in arrival order, 0 conflicts, 270 commits, 264 files, +9,438 / −2,582 lines |

## 4. What remains (the judgement round)

- The chokepoint pins above, then a second checklist pass over the files they release.
- The 25 files over 1,800 lines to split by topic (`AUDIT.md` finding 7; the auditors' finding lines are the cut lists), first `PrismOperator` (the general operator is ~300 of 5,303 lines), `Connection`, `SurgeryCollapse`, `CrossProduct`, `MorseLemma`, `Collar`, `RiemannMapping`, `Transversality/Basic`, `Cubic`, `CubeBoundaryThreeCells`, `VanKampen.lean`.
- The 20 verbatim-moved D files: extract the general islands the auditors named, return the rest to `Hopf/Proof`.
- The internal duplicates (finding 5): `VanKampen.lean` vs the split, `Chains.lean` vs the PR files, barycentric subdivision twice, MV naturality twice, Hatcher 2.6 twice, the H¹-first sheaf pipeline, `FunctionSheaf` vs `DependentFunctionSheaf`, the constant ℤ sheaf and global sections under several names.
- The names the packets could not change (renames delete declarations): `MorseCancellation.*` on real analysis, `ThreefoldGluing`/`SpecialPeriods.Threefold.Star` on generic glue data, `NativeTransversality.At`, "native" throughout.
- The 40 Jev two-letter disagreements and the auditors' ten low-confidence calls, for a reader.
- A fresh-reviewer pass over this round's receipts (one reviewer per receipt).
