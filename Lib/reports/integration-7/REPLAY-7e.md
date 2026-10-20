# Integration 7e: `center-solution` `0870a3da..84a62a02` (`Lib`, `Lib.lean`) onto `lib/integration`

Run by Claude Opus 5.5 (model ID `claude-opus-5-5`) as a subagent of this seat. Started 2026-10-20
01:00 CEST and ended 2026-10-20 01:41 CEST with this receipt's commit. Worktree `/home/goblin/hopf-int7e`,
branch `work/int7e`, base `bf6688c0` (= `lib/integration`). No push, no merge.

Source head pinned at the start: `H = 84a62a024019b8cdee9cb3003920aae78057571d`.
Range: `git rev-list --reverse 0870a3da..H -- Lib Lib.lean` = 1 commit by Fabian Franz
`<fabian@isomorphic-ai.com>`. It touches only `Lib/Geometry/Hyperbolic/Models.lean` (+271) and
`Lib/AxiomAudit.lean` (+30).

## 1. Method

The method is the same as in 7c and 7d (`REPLAY-7c.md` §1, `REPLAY-7d.md` §1). `replay.py` is the 7d script with the
worktree and scratch path changed (`/home/goblin/.claude/jobs/06995e68/tmp/int7e/`) and an empty `MANUAL` set. It runs
`git cherry-pick --no-commit`. It would resolve `Lib.lean` / `Lib/AxiomAudit.lean` conflicts by the append rule and
stops on any other conflict. It commits with the original author name, email, author date and message verbatim,
keeping the `Generated with [Devin]` line and the `Co-Authored-By: Devin` trailer. After the message come
`(cherry picked from commit <sha>)` and the two trailers. The commit applied cleanly.

| method | commits |
|---|---|
| `git cherry-pick` (three-way, clean) | 1 |
| cherry-pick + append rule | 0 |
| reroute to `Center/Proof` / `Shared/Proof` | 0 |
| adaptation commits / real collisions | 0 / 0 |

## 2. Commit table

| # | source | replayed | subject | method | build |
|---|---|---|---|---|---|
| 1 | `84a62a02` | `672affc1` | feat(Lib): provide real polar charts for arbitrary tangent frames | cherry-pick | b1: `lake build Lib.Geometry.Hyperbolic.Models Lib.AxiomAudit`, green, 9402 jobs |

Full hashes and build lines are in `replay-7e.log`.

## 3. Deviations

None. There are no `Integration note:` lines.

Content check: `git diff 84a62a02 672affc1 -- Lib/Geometry/Hyperbolic/Models.lean` is empty, so the file is
identical to the source at `H` (8,852 lines). On `Lib/AxiomAudit.lean` and `Lib.lean` the diff consists only of the
target's own earlier edits. For each file, the sorted `+/-` line sets of `git diff 0870a3da bf6688c0` and
`git diff 84a62a02 672affc1` are equal (md5 `eeaacbab…` for `Lib/AxiomAudit.lean`, `368f95f8…` for `Lib.lean`).
The commit adds 15 `#print axioms` probes: 3,788 to 3,803 lines.

## 4. Layout judgement (owner decision 2026-10-03, `Lib/reports/center-proof/RECEIPT.md`)

| source | judgement | reason |
|---|---|---|
| `84a62a02` | generic, stays in `Lib` | The commit adds 5 definitions and 10 theorems: polar points in an arbitrary orthonormal tangent frame at a point of the hyperboloid, the normalized complex and circle-valued direction, its continuity off the polar center, and a real angle chart on the domain avoiding a prescribed angular cut (open, continuous, with exact forward inverse and recovery of any prescribed lift), plus joint continuity of polar points. "Center" here is the polar origin `p`, not the center construction. This is hyperboloid-model geometry with a textbook source line (G07) and no reference to `Center`. |

Nothing went to `Center/Proof`, `Shared/Proof` or `Hopf/Proof`.

## 5. Final checks on `672affc1` (logs in the job scratch, `final-*.log`; summary in `replay-7e.log`)

```
lake build Lib                                   Build completed successfully (9402 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9462 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Shared Center                         Build completed successfully (8867 jobs).
lake build Lib.AxiomAudit Shared.Proof.AxiomAudit Center.Proof.AxiomAudit Unused
                                                 Build completed successfully (9418 jobs).
  probe results (grep -cE "^info: <file>.*(depends on axioms|does not depend)"):
    Lib/AxiomAudit.lean 3803 (before 3788, +15)  Shared/Proof/AxiomAudit.lean 53 (before 53)
    Center/Proof/AxiomAudit.lean 9 (before 9)     Unused/…/CubeBoundaryThreeCells.lean 34 (before 34)
  union of all 'depends on axioms' lists = {propext, Classical.choice, Quot.sound}; sorryAx 0; errors 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
isolation greps (Lib→Shared|Hopf|Center; Shared→Hopf|Center; Hopf,S6,root→Center; Center→Hopf): all empty
lake build Solution Lib Shared Center Unused S6 S6Shortcuts   Build completed successfully (9474 jobs).
```

All lake commands ran with the full `GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`
triple; Lake did not touch `/home/goblin/hopf/.lake/packages` (directory mtime unchanged, 2026-10-12).

## 6. Environment diff (`envdiff-7e.txt`, `envdiff-7e.json`)

The base was dumped fresh from the untouched head. Detached worktree `/home/goblin/hopf-int7e-base` at `bf6688c0`
(build copied from `hopf-lib-integration`, `lake build Solution Lib Shared Center Unused S6 S6Shortcuts` green, 9474 jobs).
Both trees then ran `lake env …/lean-agent-ide dump Solution Lib Shared Center Unused S6 S6Shortcuts --modules
Hopf,Lib,Shared,Center,Unused,S6,S6Shortcuts,Solution`. The base has 39,478 constants (equal to the 7d result, so
the import trim between `7c511259` and `bf6688c0` left the environment unchanged) and the result has 39,503.

```
constants before 39478 after 39503 (keys 39371 39396 )
lost 0 added 25 of which source declarations: 0 15 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 10 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

- 0 lost, 0 changed types, 0 module moves.
- 15 added source declarations, all in `Lib.Geometry.Hyperbolic.Models`. They are exactly the 15 declaration headers of
  `git diff 0870a3da 84a62a02 -- Lib`: `Hyperbolic.hyperboloidFramePolar{,_coefficients,_direction,_reconstruct}`,
  `Hyperbolic.hyperboloidFrameDirectionComplex{,_normalization}`, `Hyperbolic.hyperboloidFrameDirection`,
  `Hyperbolic.hyperboloidFrameAngleDomain`, `Hyperbolic.hyperboloidFrameAngle{,_chart,_forward_inverse,_prescribed_lift}`,
  `Hyperbolic.continuous_hyperboloid{FrameDirectionComplex,FrameDirection,FramePolar}`.
- 10 auxiliary additions, all generated from these: `hyperboloidFramePolar._proof_{1,2}`, `hyperboloidFrameAngle._proof_{1,2,3}`,
  `hyperboloidFrameDirection{,Complex}.eq_1`, `hyperboloidFramePolar.congr_simp`, and two private `_simp_1_*` lemmas.
- The verdict is FAIL by construction because of the unaccepted additions, as in 7, 7b, 7c and 7d.

## 7. Left

- `center-solution` `Lib` commits beyond `H` at the end of this run: 0. `center-solution` is still at `84a62a02`, and
  `git -C /home/goblin/hopf log --oneline 0870a3da..center-solution -- Lib Lib.lean` lists only the replayed commit.
  The source worktree has uncommitted edits to `Lib/AxiomAudit.lean` and `Lib/Geometry/Hyperbolic/Models.lean` and an
  untracked `Lib/Geometry/Hyperbolic/G07TwoAxisProduct_ActualConsumerCheck.lean` (`git -C /home/goblin/hopf status --short`).
  They are not part of this range and were not looked at.
- With this range `Models.lean` is 8,852 lines. The INTEGRATION-7 Left item on splitting it is unchanged.
- The base worktree `/home/goblin/hopf-int7e-base` (detached, no branch) is removed after this commit.

Reproduce: `git log --format='%H %an %ad%n%B' bf6688c0..work/int7e`. Run the checks as in §5 from the worktree root
with `taskset -c 0-7` and the lake path of `replay-7e.log`. Envdiff:
`python3 /home/goblin/lean-agent-ide/tools/envdiff.py <S>/dump_base.jsonl <S>/dump_after.jsonl --receipt envdiff-7e.json`.
