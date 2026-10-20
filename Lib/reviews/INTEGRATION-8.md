# Integration review 8 — the judgement round (2026-09-21)

Coordinator: Claude Fable 5.1 (this seat); seven Opus 5 agents in seeded worktrees from `4e15a034`
(the round-7 hand-off head), one branch each, packets from `Lib/reports/round-7/judgement/`; the merge
with its conflicts resolved by an eighth agent. Head after the round: `4ce6d6d3`. Receipts:
`Lib/reports/round-8/<branch>/RECEIPT.md` (with `rename.txt`, `envdiff.json`), `Lib/reports/round-8/MERGE.md`.

## 1. What merged

| branch | done | left, with the reason |
|---|---|---|
| `r8/pins` | 8 chokepoint declarations lifted to universe variables, the checklist re-run on ~45 released files: `.{0}` pins in `Lib` 1,024 in 99 files → 320 in 48 files | the singular cochain/chain interface (**280 of the 320, corrected; the receipt said 271**): the polymorphic form elaborates but makes the coefficient object `ULift ℤ` instead of literal `ℤ`, which four consumers use in proofs; a design decision, not a lift — and **(corrected)** also a *protocol* obstruction independent of
those four proofs: no `ModuleCat.{u} ℤ` object has carrier literally `ℤ` for `u > 0`, so every
polymorphic form changes the `u = 0` object to `ULift.{0} ℤ`, which "statement at `u = 0` unchanged"
forbids; the clean route is a new polymorphic `chains` beside the pinned one plus a `u = 0`
comparison, an addition rather than a lift.  `SphereTwo` (moved to `Hopf/Proof` by `dfiles-c` anyway).
Of the remaining pins, ~17 are attributed to nothing in the receipt |
| `r8/dup-sheaf` | one name each for the constant ℤ sheaf (`TopCat.ConstantSheaf.integralSheaf`), the global-sections functor (`TopCat.Sheaf.globalSectionsFunctor`, new `GlobalSections.lean`) and sheafification (`TopCat.Sheaf.sheafification`, new `Sheafification.lean`); `FunctionSheaf.lean` deleted for its dependent twin; nine degree-one declarations deleted as literal `n = 0` instances; 28 deletions, each with its twin | the rest of the degree-one pipeline: its comparison isomorphisms are metrizability-free while the positive-degree ones need `[MetrizableSpace X]`; `freeOpenFunctor` is defined identically three times (recorded) |
| `r8/dup-hom` | the **1,810-line (corrected; the receipt said 1,823)** van Kampen monolith deleted after porting the uniqueness half and docstrings into the Mathlib-PR split (17 statements verified character-identical modulo the `Cocone.` segment); Mayer–Vietoris naturality down to one copy; cocycle-class helpers in one module; a third copy of `homotopy_on_cocycle_succ` unified; 251 deletions with twins | the pre-PR chain files vs the PR trio and the re-proved barycentric subdivision (~275 declarations): two towers typed on different simplex/chain definitions, 57 importers, re-proving not aliasing; two of the packet's duplicate claims refuted on inspection (the mesh files are imported by the file said to supersede them; the two resolution structures differ by a field) |
| `r8/dfiles-a` | of five Morse D files: **`MinimalSystem` moved (corrected; this row said "deleted")** — the whole module, four declarations, verbatim to `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean`; nothing was deleted (envdiff: 0 lost) — `MiddleBlocks`/`CutTransport`/`SurgeryHomology` split into general islands (new `EqualRangeHomology`, `RadialFilling`, `SignedCancellation`) and `Hopf/Proof` remainders, 6 renames out of `MorseCancellation` | 96 of 115 `BeltCancellation` and 120 of 143 `SurgeryHomology` constants are in the dependency closure of `SurgeryCollapse.lean`/`OrderedCancellation.lean` (monolith wave); `Lib` may never import `Hopf` |
| `r8/dfiles-b` | `SurjectiveDescent` deleted for Mathlib's `MonoidHom.liftOfSurjective`; seven files moved under `Hopf/Proof`; mesh constants folded into their consumer; the lower-differentials island kept under its statement's name | `LocalDegreeNeighborhoods`/`OnePointCover` consumed by the surgery monoliths; their general halves extracted to `LinearSphereAction`, `Reeb`, new `SpherePointTransport` |
| `r8/dfiles-c` | `SphereTwo` moved under `Hopf/Proof` (imported from `Hopf/Proof/Final.lean` so it still builds: `Hopf` has no root); `cohomologyAddCommGroup` → `instAddCommGroupH`, documented with the failed-deletion experiment | the instance stays (load-bearing) — though **(corrected)** the receipt's stated cause is wrong:
`Sheaf.H` is an `abbrev` and resolution does see through it; the blocker is Mathlib's `TopCat.Sheaf`
being a non-reducible `def`.  Its four axiom probes have no `Lib`-side home now: **(corrected)** this
was framed as an owner decision, but the fact is that after the move **the four `SphereTwo` theorems
are probed by nothing** — the `dfiles-c` receipt's reason ("they remain axiom-audited transitively:
they are in the import closure of `Solution.lean`") is false, because `#print axioms` follows
dependencies, not imports.  A `Hopf/Proof/AxiomAudit.lean` with the four lines is being added; a move
to `Hopf/Proof` carrying its probes is now a standing rule, not an owner decision.  Also pending: the
`w4-w1-solution` branch still imports `Lib.Topology.Sheaves.Cohomology.SphereTwo` and must be
rerouted |
| `r8/moved` | 34 renames out of `MorseCancellation`/`HomologyTransport`/`native*`; two clean splits (`Geometry/Manifold/Curve/CircleGluing`, `Combinatorics/IndexDisorder`); the default codimension 4 removed from `TubularBigon` | `*_of_circle_nullhomotopies` → `SimplyConnectedSpace` would strengthen the hypothesis; one cut lemma's only consumer is imported by `Hopf/Proof` |

Merge (`MERGE.md`): 16 conflicts between `dup-sheaf` and `pins` (the same declarations unified and lifted), 3 with `dfiles-c`, 2 with `dfiles-a`, resolved by the rule "keep the survivor, keep the lift on what survives"; one cross-branch break (a name `moved` renamed, used by `dfiles-a`'s new file) fixed at the merge; two docstring sentences that had become false after the lift corrected.

## 2. Checks on `4ce6d6d3`

| check | result |
|---|---|
| `lake build Lib` | green, 9,144 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,196 jobs; final theorem `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit` | 3,300 probes, all standard, no `sorryAx` |
| census | 123 |
| environment diff, `Solution`+`Lib` at `4e15a034` (38,593 constants) against `4ce6d6d3` (38,254), rename map 91 entries after→base (**85 effective: six `dfiles-a` lines are inert, written in the wrong direction — corrected**) | 221 source names lost and not re-added, all reconciled to a receipt (dup-hom 190, dup-sheaf 28, dfiles-b 3); 3 added (documented); 477 changed types: 350 universe lifts (unchanged use-sets), 11 the documented `TwoOpenCover` substitution, 17 the hand-ported van Kampen statements, and **the remaining 99 (corrected)** in the Leray / `Topology.Sheaves` cluster, spread over 34 base modules (largest: `ResolutionTransgression` 9, `SheafificationPushforward` 8, `SheafificationStalkCompatibility` 7, `HigherDirectImageSheafification` 6, `SkyscraperReconstruction` 6, `AcyclicResolution` 6).  **(corrected)** this row summarised them as "the lift combined with the survivor respelling"; `MERGE.md`'s parenthetical for them summed to 88, not 99, and the cause is not uniform — `TopCat.SingularCochainSheaf.exists_h1Comparison_natural` stays at `.{0}` and changes type only because the `dfiles-c` instance rename is named in its statement, and the six `SkyscraperReconstruction` names change only through the `topEvaluation` respelling at unchanged universe.  33 one-to-one module moves, 0 ambiguous. Verdict FAIL by construction (deletions are never accepted); the reconciliation is the judgment |

## 3. Process and tool notes

- Three agents found independently that `dump --rename` applies the map to the dumped environment, so lines must be `<after name> <base name>`; my shared rules said the reverse. Fixed in `spec/dump.md` of the tool. Two more hash sources recorded there: library-suffixed anonymous local instances when a file moves between Lake libraries; **(corrected)** an instance argument resolved at a universe metavariable — `TopCat.Presheaf.germ`'s
`[HasColimits AddCommGrpCat.{?v}]`, assigned `?v := 0` — which is the real "invisible pin" and the
cause of the `whnf` timeout round 7 had recorded.  This note originally said "bare `{X : TopCat}`
binders elaborating at universe 0"; bare binders in fact become universe *parameters*, and
`autoImplicit` is irrelevant.  A `.{0}` grep census cannot find this class; `#check` with
`pp.universes true` can.
- The auditors' claims were tested, not followed: five of the eleven duplicate items and three of the five "Mathlib has it" items turned out wrong or blocked for a reason the receipt states. The audit is a work list, not a verdict.
- ~~No fresh-context reviewer has read this round's or round 7's receipts yet.~~ **(done, 2026-09-21)** twenty-one fresh reviewers, one receipt each: `Lib/reviews/REVIEW-7-8.md`, reviews in `Lib/reports/review-7-8/*.md`.  All twenty-one ACCEPT WITH FINDINGS; nothing unsound.

## 4. What remains

The monolith wave (`Lib/reports/round-7/judgement/monoliths.md`, 25 files; it also unblocks the last Morse D material); the chain-interface decision (`ULift ℤ` vs literal `ℤ`); the pre-PR chain tower; the fresh-reviewer pass over rounds 7 and 8; the `Hopf`-side axiom probes question.

## 5. Corrections after the fresh-reviewer pass (2026-09-21)

The pass §3 called for has been done: twenty-one fresh reviewers, one receipt each, no prior context,
read-only.  Verdicts and the consolidated fix list are in `Lib/reviews/REVIEW-7-8.md`; the reviews
are in `Lib/reports/review-7-8/*.md`.  All twenty-one: ACCEPT WITH FINDINGS.  **Nothing unsound** —
no weakened statement, no added hypothesis, no lost declaration whose content is gone, no
`sorry`/`axiom`, and no merge that dropped a line from either parent (all seven merges replayed with
`git merge-tree`; `envdiff.py` re-run reproduces `envdiff.json` field for field).  This section
records what was corrected in this file; each branch receipt and `MERGE.md` carry their own dated
corrections.

1. **`r8/dfiles-a`: "`MinimalSystem` deleted" is a move** (`r7-merged-head.md`, finding 6), corrected
   in §1.  The whole module, four declarations, went verbatim to
   `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean`; the envdiff shows 0 lost.

2. **The 127 changed-type residue in §2 is 99, not "the rest" summarised from a parenthetical that
   summed to 88** (finding 6, and `r8-merge.md` finding 2), corrected in §2 with the per-module
   breakdown and the two cases whose cause is neither the `pins` lift nor a `dup-sheaf` respelling.

3. **Three §1 figures corrected from the branch reviews**: `pins` 271 → **280** of the 320 (and the
   `SingularCochainSheaf/*` file count 26 → 32 in that receipt); `dup-hom`'s monolith 1,823 →
   **1,810** lines; the rename map's 91 entries → **85 effective**, six `dfiles-a` lines being inert.
   §1's `pins` row also now records the protocol half of the `ULift ℤ` obstruction and the ~17 pins
   the receipt attributes to nothing.

4. **`dfiles-c`'s two claims corrected in §1** (`r8-dfiles-c.md`, findings 1 and 2, and
   `r7-merged-head.md` finding 2).  The `instAddCommGroupH` registration is load-bearing — confirmed
   by `#synth` — but the cause is Mathlib's `TopCat.Sheaf` being a non-reducible `def`, not `Sheaf.H`
   failing to reduce to `Ext`.  And the four moved `SphereTwo` theorems are **probed by nothing**:
   "they remain axiom-audited transitively" is false, since `#print axioms` follows dependencies, not
   imports.  This was framed here as an owner decision on the same scale as the other two; it is not
   — it is a four-line `Hopf/Proof/AxiomAudit.lean`, now a standing rule (`REVIEW-7-8.md` §4).  The
   pending `w4-w1-solution` import reroute is recorded in the same row.

5. **§3's second tool note is corrected**: the invisible pin is an *instance argument resolved at a
   universe metavariable* (`germ`'s `HasColimits`), not a bare-binder effect, and `autoImplicit` has
   nothing to do with it.  Both corrected tool findings — this one and "`autoImplicit` is on in half
   of `Lib`" — go to `lean-agent-ide`'s `spec/dump.md`.  A third, from two reviewers independently:
   `envdiff`'s `PROOF-NAMING` class is misnamed and under-powered; it should hash the type with
   universe parameters instantiated at 0 and include Mathlib constants in `uses`, so that a pure lift
   verifies mechanically and a hypothesis change becomes a distinct class.

6. **§4's "what remains" was thin** (`r7-merged-head.md`, finding 3).  The receipts' "left" sections
   carry items neither this file nor `NEXT_STEPS.md` listed: the 40 Jev two-letter disagreements and
   the auditors' ten low-confidence calls; the remaining project namespaces (`nativeMorseIndex` 226
   lines, `NativeTransversality` 86, `ThreefoldGluing` 154, `SpecialPeriods.Threefold.Star` 102,
   `MorseCancellation.` 931); `dup-hom` items 3–6; `dup-sheaf`'s five recorded-and-left items;
   `dfiles-c`'s `sheaf`/`unit` removal and the `Sheaf.H` instance gap; `moved`'s `Matrix.Pivot`,
   `Module.Presentation` and `sheetSum` items; and the ~17 unattributed pins.  The full list is in
   `REVIEW-7-8.md` §3.  One item is **no longer blocked**: `dup-hom`'s degree-one cochain lemmas
   waited on `GlobalUnitH1Criterion.lean`, which `dup-sheaf` deleted later in the same round.
