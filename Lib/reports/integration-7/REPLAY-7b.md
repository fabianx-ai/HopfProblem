# Integration 7b — `center-solution` `8ea19482..d4db0d1a` (`Lib`, `Lib.lean`) onto `lib/integration`, plus two follow-ups

Run by Claude Opus 5.5 (model ID `claude-opus-5-5`), as a subagent of this seat; start 2026-10-02
00:37 CEST (22:37 UTC), end 2026-10-02 00:59 CEST (this receipt's commit). Worktree `/home/goblin/hopf-int7b`,
branch `work/int7b`, base `223b655d` (= `lib/integration`). No push.

Source head pinned at the start: `H = d4db0d1ab4d1913e7de9a3be99bf74ffb8f9d209`.
Range: `git rev-list --reverse 8ea19482..H -- Lib Lib.lean` = 2 commits (the whole `8ea19482..H` is these two
commits), one author (Fabian Franz `<fabian@isomorphic-ai.com>`), touching only `Lib/` and `Lib.lean`.

## 1. Method

As in integration 7 (`REPLAY.md` §1): `replay.py` (the integration-7 script with paths, range and an empty
`MANUAL` set changed; kept in the job scratch) runs `git cherry-pick --no-commit`, resolves `Lib.lean` /
`Lib/AxiomAudit.lean` conflicts by the append rule, stops on anything else, and commits with the original
author name, email, author date and message, then `(cherry picked from commit <sha>)` and the trailers.
Both commits applied cleanly; no append-rule resolution, no reroute, no adaptation, no collision.

| method | commits |
|---|---|
| `git cherry-pick` (three-way, clean) | 2 |
| cherry-pick + append rule | 0 |
| reroute (facade target) | 0 |
| adaptation commits / real collisions | 0 / 0 |

## 2. Commit table

| # | source | replayed | subject | method | build |
|---|---|---|---|---|---|
| 1 | `75a6f9a9` | `c46194b6` | feat(Lib): construct coefficient-plane frames and full geodesic sections | cherry-pick | b1: `lake build Lib.Geometry.Hyperbolic.GeodesicEquations Lib.AxiomAudit` at `c46194b6` (detached checkout), green, 9428 jobs |
| 2 | `d4db0d1a` | `745bacc9` | feat(Lib): identify hyperbolic metric angles with coordinate angles | cherry-pick | b2: `lake build Lib.Geometry.Hyperbolic.ConformalCoordinates Lib Lib.AxiomAudit`, green, 9430 jobs |

`d4db0d1a` adds the new module `Lib/Geometry/Hyperbolic/ConformalCoordinates.lean` and its `Lib.lean` import
(merged cleanly). Full hashes and build logs: `replay-7b.log`.

## 3. Deviations

None in the replay. No `Integration note:` lines.

## 4. Part 2 — follow-ups from `Lib/reviews/INTEGRATION-7.md` §Left

### a. Cube-root lemma to `SectorRoots` — `ff9dfc00`

Precondition (checked before the move):

- `uses` in `/home/goblin/.claude/jobs/06995e68/tmp/head3/dump_head.jsonl` (39,175 constants, the merged head):
  no constant uses `RiemannBoundary.principalRoot_three_reverse_of_wedge`; its own entry is in
  `Lib.Analysis.Complex.RiemannMapping.PrincipalRoot`.
- `grep -rnw principalRoot_three_reverse_of_wedge --include=*.lean .` (whole worktree, `.lake` excluded): only
  the definition (`Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean:175`) and its probe
  (`Lib/AxiomAudit.lean:7448-7449`). No `Lib` user, no `Hopf` consumer, so no import change.

Move: the 97-line block (docstring + statement + proof) cut from the end of `PrincipalRoot.lean` and inserted
in `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` after `principalRoot_three_real_boundary`
(the last exponent-3 lemma, before the `quarticRootRotation` material). The removed and added line sets differ
only in where `git diff` places the separating blank line; the 97 lines are identical. Probe: the two lines
removed from `Lib/AxiomAudit.lean` (with their blank separator) and inserted in the `SectorRoots` section of
`Hopf/Proof/AxiomAudit.lean`, before the quartic probe. `SectorRoots` already imports `PrincipalRoot` and
`Hopf/Proof/AxiomAudit.lean` already imports `SectorRoots`. Build b3 (`PrincipalRoot`, `SectorRoots`,
`Lib.AxiomAudit`, `Hopf.Proof.AxiomAudit`): green, 9432 jobs; the probe reports
`[propext, Classical.choice, Quot.sound]`.

### b. `Hopf/Proof/AxiomAudit.lean` docstring — `35d116de`

Comment-only: the module docstring now lists both groups it probes, the four two-sphere vanishing theorems of
`SphereTwo` and the two sector-root wedge reversals (`principalRoot_three_reverse_of_wedge`,
`rotatedPrincipalRootFour_reverse_of_wedge`) in `SectorRoots`, neither used by the final theorem's closure
(grep: the quartic lemma has no user either).

## 5. Final checks on `35d116de` (logs in the job scratch `final-*.log`; summary in `replay-7b.log`)

```
lake build Lib                                   Build completed successfully (9429 jobs).
lake build Solution S6Shortcuts S6 Challenge     Build completed successfully (9490 jobs).
  'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit  Build completed successfully (9432 jobs).
  'depends on axioms' lines: 3759 (Lib/AxiomAudit.lean 3753, Hopf/Proof/AxiomAudit.lean 6)
  'does not depend on any axioms' lines: 13 (Lib/AxiomAudit.lean)
  distinct axioms: propext (3759), Quot.sound (3747), Classical.choice (3623); sorryAx: 0
python3 scripts/lib_stock_census.py --check      ratchet PASS: 123 <= baseline 1648
grep -rnE '^(public )?import Hopf' Lib/ --include=*.lean    (empty; exit 1)
```

Probe accounting: `Lib/AxiomAudit.lean` 3736 + 18 (range) − 1 (moved) = 3753; `Hopf/Proof/AxiomAudit.lean`
5 + 1 = 6. (Axiom names were counted over the whole bracketed list, which Lean wraps across lines.)

Content check: `git diff d4db0d1a 745bacc9` on `Lib/Geometry/Hyperbolic/GeodesicEquations.lean` and
`Lib/Geometry/Hyperbolic/ConformalCoordinates.lean` is empty. On `Lib.lean` and `Lib/AxiomAudit.lean` it
consists exactly of the target's own earlier edits: the sorted `+/-` line sets of `git diff 8ea19482 223b655d`
and `git diff d4db0d1a 745bacc9` on each file are equal (md5 `51fa7ebf…` for `Lib.lean`, `23457d01…` for
`Lib/AxiomAudit.lean`). No file of the range was rerouted.

## 6. Environment diff (`envdiff-7b.txt`, `envdiff-7b.json`)

`lake env …/lean-agent-ide dump Solution Lib --modules Hopf,Lib` → 39,199 constants; base
`head3/dump_head.jsonl` 39,175.

```
constants before 39175 after 39199 (keys 39073 39095 )
lost 0 added 24 of which source declarations: 0 19 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 5 0
module moves (source declarations, 1-to-1):
       1  Lib.Analysis.Complex.RiemannMapping.PrincipalRoot -> Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots
ambiguous module changes: 1
  AMB ('Hyperbolic.termI', {}, {'Lib.Geometry.Hyperbolic.ConformalCoordinates': 1})
auxiliary constants that changed module: 1
VERDICT FAIL
```

- 0 lost, 0 changed types.
- 19 added source = the 18 declarations of the range plus 1 notation constant:
  `Lib.Geometry.Hyperbolic.GeodesicEquations` 13 (`planeCoefficient_positiveScalars`,
  `planeCoefficientUnitDirection`, `planeCoefficientNegativeVector`, `planeCoefficientFrame_spec/_basis/_gram`,
  `planeCoefficientBaseCoords`, `planeCoefficientBaseCoords_mem`, `planeCoefficientBasePoint`,
  `planeCoefficientBasePoint_spec`, `planeCoefficient_timelike_of_discriminant_pos`,
  `planeCoefficient_whole_section`, `planeCoefficient_timelike_iff`), `Lib.Geometry.Hyperbolic.ConformalCoordinates`
  5 (`upperHalfPlaneMetric_{inner,norm,normalized,angle}_coordinates`, `toHyperboloid_angle_coordinates`) —
  exactly the 18 declaration headers of `git diff 8ea19482 d4db0d1a -- Lib`.
- Notation constant, listed separately: `Hyperbolic.termI` from `local notation "I" => 𝓘(ℝ, ℂ)` in
  `ConformalCoordinates` (raw name `_private.Lib.Geometry.Hyperbolic.ConformalCoordinates.0.Hyperbolic.termI`).
- The 5 auxiliary additions: the `termI` macro-rules constant and four `planeCoefficientFrame_basis`
  `_proof_`/`_simp_` constants.
- One module move: the cube-root lemma, `Lib.…PrincipalRoot` → `Hopf.Proof.…SectorRoots` (Part 2a).
- The ambiguous entry and the one "auxiliary constant that changed module" are the tool normalising private
  names: `Models.lean` already has a `local notation "I"` with the same normalised name `Hyperbolic.termI`.
  A raw-name comparison of the two dumps shows exactly one constant whose module changed (the cube-root lemma)
  and nothing else.
- Verdict FAIL by construction (unaccepted additions), as in integration 7.

## 7. Left

- `center-solution` `Lib` commits beyond `H` at the end of this run: 0
  (`git -C /home/goblin/hopf rev-list --count d4db0d1a..center-solution -- Lib Lib.lean`; `center-solution`
  was still at `d4db0d1a`). The source worktree has uncommitted edits to `Lib/AxiomAudit.lean` and
  `Lib/Geometry/Hyperbolic/Models.lean` (`git -C /home/goblin/hopf status --short`); not part of this range.
- `ConformalCoordinates.lean` adds a second `local notation "I"` in namespace `Hyperbolic` beside the one in
  `Models.lean`; harmless (both private) but it makes `envdiff.py` report an ambiguous name
  (`grep -n 'local notation' Lib/Geometry/Hyperbolic/*.lean`).
- The integration-7 Left items about `Models.lean` size, manuscript labels, the Mathlib `ℍ` metric bridge and
  lint warnings are unchanged; the range adds to `GeodesicEquations.lean` (+304 lines) and the new
  `ConformalCoordinates.lean` (89 lines).

Reproduce: `git log --format='%H %an %ad%n%B' 223b655d..work/int7b`; checks as in §5 from the worktree root with
`taskset -c 6-11` and the lake path of `replay-7b.log`; envdiff:
`python3 /home/goblin/lean-agent-ide/tools/envdiff.py <head3>/dump_head.jsonl <S>/dump_after.jsonl --receipt envdiff-7b.json`.
