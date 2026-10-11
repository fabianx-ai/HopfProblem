# Integration 7d: `center-solution` `91485e80..0870a3da` (`Lib`, `Lib.lean`) onto `lib/integration`

Run by Claude Opus 5.5 (model ID `claude-opus-5-5`) as a subagent of this seat. Started 2026-10-11
14:10 CEST and ended 2026-10-11 15:00 CEST with this receipt's commit. Worktree `/home/goblin/hopf-int7d`,
branch `work/int7d`, base `41b46d37` (= `lib/integration`). No push, no merge.

Source head pinned at the start: `H = 0870a3da8ddccf2d78a8d609b5679e0877ee6b3b`.
Range: `git rev-list --reverse 91485e80..H -- Lib Lib.lean` = 1 commit by Fabian Franz
`<fabian@isomorphic-ai.com>`. It touches only `Lib/Geometry/Hyperbolic/Models.lean` (+153) and
`Lib/AxiomAudit.lean` (+6).

## 1. Method

The method is the same as in 7c (`REPLAY-7c.md` §1). `replay.py` is the 7c script with the worktree and scratch path changed
(`/home/goblin/.claude/jobs/06995e68/tmp/int7d/`) and an empty `MANUAL` set. It runs `git cherry-pick --no-commit`.
It would resolve `Lib.lean` / `Lib/AxiomAudit.lean` conflicts by the append rule and stops on any other conflict.
It commits with the original author name, email, author date and message verbatim, keeping the `Generated with [Devin]`
line and the `Co-Authored-By: Devin` trailer. After the message come `(cherry picked from commit <sha>)` and the two trailers.
The commit applied cleanly. The facade dissolution and the better-homes moves on this branch did not touch `Models.lean`.

| method | commits |
|---|---|
| `git cherry-pick` (three-way, clean) | 1 |
| cherry-pick + append rule | 0 |
| reroute to `Center/Proof` / `Shared/Proof` | 0 |
| adaptation commits / real collisions | 0 / 0 |

## 2. Commit table

| # | source | replayed | subject | method | build |
|---|---|---|---|---|---|
| 1 | `0870a3da` | `32c9a734` | feat(Lib): generalize polar reflections to arbitrary angular origins | cherry-pick | b1: `lake build Lib.Geometry.Hyperbolic.Models Lib.AxiomAudit`, green, 9402 jobs |

Full hashes and build lines are in `replay-7d.log`.

## 3. Deviations

None. There are no `Integration note:` lines.

Content check: `git diff 0870a3da 32c9a734 -- Lib/Geometry/Hyperbolic/Models.lean` is empty, so the file is
identical to the source at `H` (8,581 lines). On `Lib/AxiomAudit.lean` and `Lib.lean` the diff consists only of the
target's own earlier edits. For each file, the sorted `+/-` line sets of `git diff 91485e80 41b46d37` and
`git diff 0870a3da 32c9a734` are equal (md5 `f1dad9c3…` for `Lib/AxiomAudit.lean`, `368f95f8…` for `Lib.lean`).
The commit adds 3 `#print axioms` probes: 3,785 to 3,788 lines.

## 4. Layout judgement (owner decision 2026-10-03, `Lib/reports/center-proof/RECEIPT.md`)

| source | judgement | reason |
|---|---|---|
| `0870a3da` | generic, stays in `Lib` | The commit adds three theorems: rotating a Lorentz tangent frame preserves its Gram form and polar coordinates, the axis through a center does not depend on the ray or the sign of the normal, and reflection at angular origin β sends θ to 2β−θ. This is hyperboloid-model geometry with a textbook source line (G07) and no reference to the center construction. |

Nothing went to `Center/Proof`, `Shared/Proof` or `Hopf/Proof`.

## 5. Final checks on `32c9a734` (logs in the job scratch, `final-*.log`; summary in `replay-7d.log`)

```
lake build Lib                                   Build completed successfully (9402 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9462 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8867 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9418 jobs).
  probe results (grep -cE "^info: <file>.*(depends on axioms|does not depend)"):
    Lib/AxiomAudit.lean 3788 (before 3785, +3)   Shared/Proof/AxiomAudit.lean 53 (before 53)
    Center/Proof/AxiomAudit.lean 9 (before 9)     Unused/…/CubeBoundaryThreeCells.lean 34 (before 34)
  union of all 'depends on axioms' lists = {propext, Classical.choice, Quot.sound}; sorryAx 0; errors 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root→Center; Center→Hopf): all empty
lake build Solution Lib Shared Center Unused S6 S6Shortcuts   Build completed successfully (9474 jobs).
```

## 6. Environment diff (`envdiff-7d.txt`, `envdiff-7d.json`)

The base was dumped fresh from the untouched head. Detached worktree `/home/goblin/hopf-int7d-base` at `41b46d37`
(build copied from `hopf-lib-integration`, `lake build Solution Lib Shared Center Unused S6 S6Shortcuts` green, 9474 jobs).
Both trees then ran `lake env …/lean-agent-ide dump Solution Lib Shared Center Unused S6 S6Shortcuts --modules
Hopf,Lib,Shared,Center,Unused,S6,S6Shortcuts,Solution`. The base has 39,475 constants and the result has 39,478.

```
constants before 39475 after 39478 (keys 39368 39371 )
lost 0 added 3 of which source declarations: 0 3 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

- 0 lost, 0 changed types, 0 module moves, 0 auxiliary changes.
- 3 added source declarations, all in `Lib.Geometry.Hyperbolic.Models`. They are exactly the 3 theorem headers of
  `git diff 91485e80 0870a3da -- Lib`: `Hyperbolic.hyperboloidPolar_{rotated_frame,axis_comparison,angular_reflection}`.
- The verdict is FAIL by construction because of the unaccepted additions, as in 7, 7b and 7c.

## 7. Left

- `center-solution` `Lib` commits beyond `H` at the end of this run: 0. `center-solution` is still at `0870a3da`, and
  `git -C /home/goblin/hopf log --oneline 91485e80..center-solution -- Lib Lib.lean` lists only the replayed commit.
  The source worktree has uncommitted edits to `Lib/AxiomAudit.lean` and `Lib/Geometry/Hyperbolic/Models.lean`
  (`git -C /home/goblin/hopf status --short`). They are not part of this range and were not looked at.
  The two untracked `G07AngularOrigin_*Check.lean` files noted at the end of 7c are no longer present.
- With this range `Models.lean` is 8,581 lines. The INTEGRATION-7 Left item on splitting it is unchanged.
- The base worktree `/home/goblin/hopf-int7d-base` (detached, no branch) is removed after this commit.

Reproduce: `git log --format='%H %an %ad%n%B' 41b46d37..work/int7d`. Run the checks as in §5 from the worktree root
with `taskset -c 0-7` and the lake path of `replay-7d.log`. Envdiff:
`python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_after.jsonl --receipt envdiff-7d.json`.
