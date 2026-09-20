# Integration review 8 — the judgement round (2026-09-21)

Coordinator: Claude Fable 5.1 (this seat); seven Opus 5 agents in seeded worktrees from `4e15a034`
(the round-7 hand-off head), one branch each, packets from `Lib/reports/round-7/judgement/`; the merge
with its conflicts resolved by an eighth agent. Head after the round: `4ce6d6d3`. Receipts:
`Lib/reports/round-8/<branch>/RECEIPT.md` (with `rename.txt`, `envdiff.json`), `Lib/reports/round-8/MERGE.md`.

## 1. What merged

| branch | done | left, with the reason |
|---|---|---|
| `r8/pins` | 8 chokepoint declarations lifted to universe variables, the checklist re-run on ~45 released files: `.{0}` pins in `Lib` 1,024 in 99 files → 320 in 48 files | the singular cochain/chain interface (271 of the 320): the polymorphic form elaborates but makes the coefficient object `ULift ℤ` instead of literal `ℤ`, which four consumers use in proofs; a design decision, not a lift. `SphereTwo` (moved to `Hopf/Proof` by `dfiles-c` anyway) |
| `r8/dup-sheaf` | one name each for the constant ℤ sheaf (`TopCat.ConstantSheaf.integralSheaf`), the global-sections functor (`TopCat.Sheaf.globalSectionsFunctor`, new `GlobalSections.lean`) and sheafification (`TopCat.Sheaf.sheafification`, new `Sheafification.lean`); `FunctionSheaf.lean` deleted for its dependent twin; nine degree-one declarations deleted as literal `n = 0` instances; 28 deletions, each with its twin | the rest of the degree-one pipeline: its comparison isomorphisms are metrizability-free while the positive-degree ones need `[MetrizableSpace X]`; `freeOpenFunctor` is defined identically three times (recorded) |
| `r8/dup-hom` | the 1,823-line van Kampen monolith deleted after porting the uniqueness half and docstrings into the Mathlib-PR split (17 statements verified character-identical modulo the `Cocone.` segment); Mayer–Vietoris naturality down to one copy; cocycle-class helpers in one module; a third copy of `homotopy_on_cocycle_succ` unified; 251 deletions with twins | the pre-PR chain files vs the PR trio and the re-proved barycentric subdivision (~275 declarations): two towers typed on different simplex/chain definitions, 57 importers, re-proving not aliasing; two of the packet's duplicate claims refuted on inspection (the mesh files are imported by the file said to supersede them; the two resolution structures differ by a field) |
| `r8/dfiles-a` | of five Morse D files: `MinimalSystem` deleted, `MiddleBlocks`/`CutTransport`/`SurgeryHomology` split into general islands (new `EqualRangeHomology`, `RadialFilling`, `SignedCancellation`) and `Hopf/Proof` remainders, 6 renames out of `MorseCancellation` | 96 of 115 `BeltCancellation` and 120 of 143 `SurgeryHomology` constants are in the dependency closure of `SurgeryCollapse.lean`/`OrderedCancellation.lean` (monolith wave); `Lib` may never import `Hopf` |
| `r8/dfiles-b` | `SurjectiveDescent` deleted for Mathlib's `MonoidHom.liftOfSurjective`; seven files moved under `Hopf/Proof`; mesh constants folded into their consumer; the lower-differentials island kept under its statement's name | `LocalDegreeNeighborhoods`/`OnePointCover` consumed by the surgery monoliths; their general halves extracted to `LinearSphereAction`, `Reeb`, new `SpherePointTransport` |
| `r8/dfiles-c` | `SphereTwo` moved under `Hopf/Proof` (imported from `Hopf/Proof/Final.lean` so it still builds: `Hopf` has no root); `cohomologyAddCommGroup` → `instAddCommGroupH`, documented with the failed-deletion experiment | the instance stays (load-bearing); its four axiom probes have no `Lib`-side home now (owner: a `Hopf`-side probe file?) |
| `r8/moved` | 34 renames out of `MorseCancellation`/`HomologyTransport`/`native*`; two clean splits (`Geometry/Manifold/Curve/CircleGluing`, `Combinatorics/IndexDisorder`); the default codimension 4 removed from `TubularBigon` | `*_of_circle_nullhomotopies` → `SimplyConnectedSpace` would strengthen the hypothesis; one cut lemma's only consumer is imported by `Hopf/Proof` |

Merge (`MERGE.md`): 16 conflicts between `dup-sheaf` and `pins` (the same declarations unified and lifted), 3 with `dfiles-c`, 2 with `dfiles-a`, resolved by the rule "keep the survivor, keep the lift on what survives"; one cross-branch break (a name `moved` renamed, used by `dfiles-a`'s new file) fixed at the merge; two docstring sentences that had become false after the lift corrected.

## 2. Checks on `4ce6d6d3`

| check | result |
|---|---|
| `lake build Lib` | green, 9,144 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,196 jobs; final theorem `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | 3,300 probes, all standard, no `sorryAx` |
| census | 123 |
| environment diff, `Solution`+`Lib` at `4e15a034` (38,593 constants) against `4ce6d6d3` (38,254), rename map 91 entries after→base | 221 source names lost and not re-added, all reconciled to a receipt (dup-hom 190, dup-sheaf 28, dfiles-b 3); 3 added (documented); 477 changed types: 350 universe lifts (unchanged use-sets), 11 the documented `TwoOpenCover` substitution, 17 the hand-ported van Kampen statements, the rest the lift combined with the survivor respelling; 33 one-to-one module moves, 0 ambiguous. Verdict FAIL by construction (deletions are never accepted); the reconciliation is the judgment |

## 3. Process and tool notes

- Three agents found independently that `dump --rename` applies the map to the dumped environment, so lines must be `<after name> <base name>`; my shared rules said the reverse. Fixed in `spec/dump.md` of the tool. Two more hash sources recorded there: library-suffixed anonymous local instances when a file moves between Lake libraries; bare `{X : TopCat}` binders elaborating at universe 0 (an invisible pin, the cause of a `whnf` timeout round 7 had recorded).
- The auditors' claims were tested, not followed: five of the eleven duplicate items and three of the five "Mathlib has it" items turned out wrong or blocked for a reason the receipt states. The audit is a work list, not a verdict.
- No fresh-context reviewer has read this round's or round 7's receipts yet.

## 4. What remains

The monolith wave (`Lib/reports/round-7/judgement/monoliths.md`, 25 files; it also unblocks the last Morse D material); the chain-interface decision (`ULift ℤ` vs literal `ℤ`); the pre-PR chain tower; the fresh-reviewer pass over rounds 7 and 8; the `Hopf`-side axiom probes question.
