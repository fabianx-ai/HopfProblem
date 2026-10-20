# Integration 7c — `center-solution` `d4db0d1a..91485e80` (`Lib`, `Lib.lean`) onto `lib/integration`

Run by Claude Opus 5.5 (model ID `claude-opus-5-5`), as a subagent of this seat; start 2026-10-03
20:05 CEST, end 2026-10-03 20:40 CEST (this receipt's commit). Worktree `/home/goblin/hopf-int7c`,
branch `work/int7c`, base `41dde599` (= `lib/integration`). No push, no merge.

Source head pinned at the start: `H = 91485e800aeadfa43cbf1f009516197a4a1da533`.
Range: `git rev-list --reverse d4db0d1a..H -- Lib Lib.lean` = 3 commits, one author
(Fabian Franz `<fabian@isomorphic-ai.com>`), touching only `Lib/Geometry/Hyperbolic/Models.lean` and
`Lib/AxiomAudit.lean`.

## 1. Method

As in integration 7 / 7b (`REPLAY.md` §1, `REPLAY-7b.md` §1): `replay.py` (the integration-7 script with
worktree, scratch path and an empty `MANUAL` set changed; kept in the job scratch
`/home/goblin/.claude/jobs/06995e68/tmp/int7c/`) runs `git cherry-pick --no-commit`, would resolve
`Lib.lean` / `Lib/AxiomAudit.lean` conflicts by the append rule, stops on anything else, and commits with
the original author name, email, author date and message verbatim (for `91485e80` this keeps its
`Generated with [Devin]` line and `Co-Authored-By: Devin` trailer), then `(cherry picked from commit <sha>)`
and the two trailers. All three applied cleanly.

| method | commits |
|---|---|
| `git cherry-pick` (three-way, clean) | 3 |
| cherry-pick + append rule | 0 |
| reroute to `Center/Proof` / `Shared/Proof` | 0 |
| adaptation commits / real collisions | 0 / 0 |

## 2. Commit table

| # | source | replayed | subject | method | build |
|---|---|---|---|---|---|
| 1 | `7f554356` | `5f4dfa87` | feat(Lib): prove hyperbolic reflections preserve length distance | cherry-pick | b1: `lake build Lib.Geometry.Hyperbolic.Models Lib.AxiomAudit`, green, 9429 jobs |
| 2 | `127c7d33` | `94f47191` | feat(Lib): identify hyperbolic reflection axis tangents | cherry-pick | b2: same targets, green, 9429 jobs |
| 3 | `91485e80` | `fae88d31` | feat(Lib): realize hyperbolic reflections in polar coordinates | cherry-pick | b3: same targets, green, 9429 jobs |

Full hashes and build lines: `replay-7c.log`.

## 3. Deviations

None. No `Integration note:` lines.

Content check: `git diff 91485e80 fae88d31 -- Lib/Geometry/Hyperbolic/Models.lean` is empty (the file is
identical to the source at `H`). On `Lib/AxiomAudit.lean` and `Lib.lean` the diff consists exactly of the
target's own earlier edits: the sorted `+/-` line sets of `git diff d4db0d1a 41dde599` and
`git diff 91485e80 fae88d31` on each file are equal (md5 `32fa84c6…` for `Lib/AxiomAudit.lean`, `51fa7ebf…`
for `Lib.lean`). Probes added: 19 `#print axioms` lines (6 + 6 + 7).

## 4. Layout judgement (owner decision 2026-10-03, `Lib/reports/center-proof/RECEIPT.md`)

| source | judgement | reason |
|---|---|---|
| `7f554356` | generic, stays in `Lib` | Six theorems that a hyperboloid reflection preserves curve speed, length and the length/piecewise-C1 distance: standard isometry facts of the hyperboloid model, no reference to the center construction. |
| `127c7d33` | generic, stays in `Lib` | Six theorems on the tangent space along a reflection axis (velocity constraints, tangent basis, the reflection's action on it): model geometry of `Models.lean`, nothing center-specific. |
| `91485e80` | generic, stays in `Lib` | Seven theorems realising a reflection across an arbitrary unit spacelike normal in polar coordinates about its axis: generic hyperbolic-plane geometry (its message says it serves "local finite-reflection geometry", a textbook topic). |

Nothing went to `Center/Proof`, `Shared/Proof` or `Hopf/Proof`.

## 5. Final checks on `fae88d31` (logs in the job scratch, `final-*.log`; summary in `replay-7c.log`)

```
lake build Lib                                   Build completed successfully (9429 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9489 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8877 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9443 jobs).
  probe results per file (one-line regex `^info: <file>:L:C: '<name>' (depends|does not)`):
    Lib/AxiomAudit.lean 3781 (before 3762, +19)   Shared/Proof/AxiomAudit.lean 54
    Center/Proof/AxiomAudit.lean 7                Unused/…/CubeBoundaryThreeCells.lean 34
  every 'depends on axioms' list ⊆ {propext, Classical.choice, Quot.sound}; sorryAx 0; errors 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root→Center; Center→Hopf): all empty
```

Unit note: the one-line regex above reproduces the stated "before" count (3,762) but misses the 4 probes
whose name contains a prime (`natAbs_det_eq_natCard_quotient_range_toLin'`, `quotientRangeToLin'EquivZModOfIsCoprime`,
`mapHomologicalFunctor_δ'_app`, `homologyIsoSc'_hom_naturality`). Counted correctly
(`grep -cE "^info: Lib/AxiomAudit.lean.*(depends on axioms|does not depend)"`), `Lib/AxiomAudit.lean` gives
3785 results (3772 depends + 13 no axioms) and has 3785 `#print axioms` lines (3766 at `41dde599`). Both
units give +19; the earlier "Lib 3,762" in `NEXT_STEPS.md` is the undercounting unit (3,766 `#print axioms` lines at `41dde599`).

## 6. Environment diff (`envdiff-7c.txt`, `envdiff-7c.json`)

The `head3/dump_head.jsonl` base predates `Shared`/`Center`, so a fresh base was dumped from the untouched
head: detached worktree `/home/goblin/hopf-int7c-base` at `41dde599` (build copied from
`hopf-lib-integration`, `lake build Solution Lib Shared Center` green, 9491 jobs), then in both trees
`lake env …/lean-agent-ide dump Solution Lib Shared Center --modules Hopf,Lib,Shared,Center`
(base 39,159 constants, after 39,180).

```
constants before 39159 after 39180 (keys 39055 39076 )
lost 0 added 21 of which source declarations: 0 19 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 2 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

- 0 lost, 0 changed types, 0 module moves.
- 19 added source declarations, all in `Lib.Geometry.Hyperbolic.Models`, exactly the 19 theorem headers of
  `git diff d4db0d1a 91485e80 -- Lib`: `hyperboloidReflection_{speed,speedWithin,length,piecewiseC1EDist_le,
  piecewiseC1EDist,lengthDist}`, `hyperboloidAxis_{velocity_constraints,radial_tangent,tangent_basis,
  velocity_iff,reflection_values,tangent_reflection}`, `hyperboloidAxis_{polarDirection_unit,
  polarDirection_exists,polarDirection_eq_iff,polar_reflection_formula,polar_reflection,
  polar_positive_coordinates,polar_zero_coordinates}`.
- 2 auxiliary additions: `Hyperbolic.hyperboloidReflection.congr_simp` and
  `_private.….hyperboloidAxis_polarDirection_exists._simp_1_1`.
- Verdict FAIL by construction (unaccepted additions), as in integrations 7 and 7b.

## 7. Left

- `center-solution` `Lib` commits beyond `H` at the end of this run: 0
  (`git -C /home/goblin/hopf log --oneline d4db0d1a..center-solution -- Lib Lib.lean` lists exactly the three
  replayed commits; `center-solution` still at `91485e80`). The source worktree has two untracked files
  `Lib/Geometry/Hyperbolic/G07AngularOrigin_Interface{,Consumer}Check.lean` (`git -C /home/goblin/hopf status
  --short`); not committed, not part of this range.
- `Models.lean` grows by 558 lines with this range (now 8,428 lines); the INTEGRATION-7 Left item on splitting it is unchanged
  (`wc -l Lib/Geometry/Hyperbolic/Models.lean`).
- The base worktree `/home/goblin/hopf-int7c-base` (detached, no branch) is removed after this commit
  (`git -C /home/goblin/hopf-lib-integration worktree list`).

Reproduce: `git log --format='%H %an %ad%n%B' 41dde599..work/int7c`; checks as in §5 from the worktree root
with `taskset -c 0-7` and the lake path of `replay-7c.log`; envdiff:
`python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_after.jsonl --receipt envdiff-7c.json`.
