# Integration 7 — `center-solution` `bcf711d6..8ea19482` (`Lib`, `Lib.lean`) onto `lib/integration`

Run by Claude Opus 5.5 (model ID `claude-opus-5-5`), as a subagent of this seat; start 2026-10-01
20:48 UTC, end 2026-10-01 21:22 UTC (this receipt's commit). Worktree `/home/goblin/hopf-int7`,
branch `int7/replay`, base `8ff8d81e` (= `lib/integration`). Source pinned at `8ea19482`.

Range: `git rev-list --reverse bcf711d6..8ea19482 -- Lib Lib.lean` = 51 commits, one author
(Fabian Franz `<fabian@isomorphic-ai.com>`), touching only `Lib/` and `Lib.lean`. Replayed head:
`752dfd1e`; this receipt is the commit after it. No push.

## 1. Method

One commit per source commit, oldest first: original author name, email and author date, original
message verbatim, a blank line, `(cherry picked from commit <full sha>)`, any `Integration note:` lines,
then the `Co-Authored-By` / `Claude-Session` trailers. Tooling: `replay.py FROM TO` (in this directory;
paths point at the job scratch) runs `git cherry-pick --no-commit <sha>`; when only `Lib.lean` /
`Lib/AxiomAudit.lean` conflict it resolves them by the append rule (target version plus the patch's added
lines, in patch order, duplicates skipped; it refuses if the patch removes lines), anything else stops.
The two `RiemannMapping` commits were done by hand (`manual_append.py` appends a pure-addition hunk
verbatim to the destination file, `manual_commit.py` commits it with the message rules).

| method | commits |
|---|---|
| `git cherry-pick` (three-way, clean) | 46 |
| `git cherry-pick` + append rule for `Lib/AxiomAudit.lean` | 3 (`d335e3ff`, `d2aa179a`, `a75fc8b9`) |
| manual reroute (`RiemannMapping` facade) | 2 (`b3f08b95`, `e238166c`) |
| adaptation commits for renamed names | 0 (no new file referred to a renamed name; every build was green) |
| real collisions | 0 |

`Lib/Algebra/Group/Prod.lean` (`d335e3ff`, which also changes one line) and `Lib/Analysis/Complex/Mobius.lean`
(`d2aa179a`, `66cf4d4e`, `b16573b6`) merged three-way without conflict; `git diff 8ea19482 HEAD` on these two
files consists exactly of the target's own edits since `bcf711d6` (the sorted `+/-` line sets of
`git diff bcf711d6 8ff8d81e` and `git diff 8ea19482 752dfd1e` on them are equal). The nine `Lib.lean` imports
merged cleanly (`a75fc8b9`'s `BoundaryLimits` import landed at its three-way context position after
`Lib.Topology.OnePointCollapse`, the others after the last import).

## 2. Commit table

`replay.log` has the full hashes, method and build per commit. Builds: `b01` = `lake build
Lib.Algebra.Group.Prod Lib.Analysis.Complex.Mobius Lib.AxiomAudit`; `b03`/`b04` = the touched module plus its
audit file, run on the applied but not yet committed change; `bA-B` = `lake build Lib Lib.AxiomAudit` after
commits A..B (never more than five commits per build). All green.

| # | source | replayed | subject | method | build |
|---|---|---|---|---|---|
| 1 | `d335e3ff` | `33f5e284` | Prove signed cap-elimination and kernel criteria | cherry-pick + append rule Lib/AxiomAudit.lean(+5 dup0) | b01 |
| 2 | `d2aa179a` | `bf1a66c1` | feat(Lib): prove quantitative fractional-linear reverse coordinate | cherry-pick + append rule Lib/AxiomAudit.lean(+3 dup0) | b01 |
| 3 | `b3f08b95` | `259b165e` | feat(Lib): prove principal cubic root reversal from wedge | manual: rerouted to RiemannMapping/PrincipalRoot.lean; AxiomAudit append rule | b03 |
| 4 | `e238166c` | `044f1f68` | feat(Lib): prove rotated quartic root reversal from wedge | manual: rerouted to Hopf/Proof/.../RiemannMapping/SectorRoots.lean; probe to Hopf/Proof/AxiomAudit.lean | b04 |
| 5 | `a75fc8b9` | `6f8a7681` | feat(Lib): extend homeomorphisms using paired boundary limits | cherry-pick + append rule Lib/AxiomAudit.lean(+3 dup0) | b05-09 |
| 6 | `66cf4d4e` | `311e4e29` | feat(Lib): identify oriented half-plane interior and frontier | cherry-pick | b05-09 |
| 7 | `b16573b6` | `a2802ddc` | feat(Lib): expose the full three-point normalization inverse | cherry-pick | b05-09 |
| 8 | `16de82a4` | `adb08cec` | feat(Lib): identify upper-half-plane and hyperboloid coordinates | cherry-pick | b05-09 |
| 9 | `be8c14af` | `087001b8` | feat(Lib): identify smooth hyperbolic coordinates and tangents | cherry-pick | b05-09 |
| 10 | `c35f96a0` | `dbc9aa8b` | feat(Lib): construct smooth metrics from positive forms | cherry-pick | b10-14 |
| 11 | `517c354d` | `286c8a9e` | feat(Lib): identify positive smooth hyperbolic tensors | cherry-pick | b10-14 |
| 12 | `097193f0` | `507d1c87` | feat(Lib): preserve curve speeds under tensor-preserving maps | cherry-pick | b10-14 |
| 13 | `9a9fd183` | `b152fd57` | feat(Lib): derive inverse tensor and norm preservation | cherry-pick | b10-14 |
| 14 | `1b30699d` | `594dcfd0` | feat(Lib): transport fixed-subdivision piecewise smooth curves | cherry-pick | b10-14 |
| 15 | `9065ab36` | `42569e0c` | feat(Lib): establish finite subdivision-independent curve length | cherry-pick | b15-19 |
| 16 | `892bed7a` | `e0cbaa20` | feat(Lib): preserve finite curve lengths under tensor-preserving maps | cherry-pick | b15-19 |
| 17 | `018ffe4f` | `af6862a1` | feat(Lib): preserve curve lengths in both directions | cherry-pick | b15-19 |
| 18 | `28a074f2` | `1e06f0d3` | feat(Lib): identify hyperbolic models with length-preserving metrics | cherry-pick | b15-19 |
| 19 | `c68ccce5` | `0b022058` | feat(Lib): identify piecewise C1 and Riemannian length distances | cherry-pick | b15-19 |
| 20 | `14db2720` | `c65f15d9` | feat(Lib): identify intrinsic distances between hyperbolic models | cherry-pick | b20-24 |
| 21 | `12622505` | `48662aca` | feat(Lib): prove positive Lorentz tangent planes independently | cherry-pick | b20-24 |
| 22 | `6ea7dce5` | `59b695f1` | feat(Lib): construct Lorentz frames and centering coordinates | cherry-pick | b20-24 |
| 23 | `b278f689` | `833def88` | feat(Lib): construct smooth upper-sheet centering maps | cherry-pick | b20-24 |
| 24 | `c7a42042` | `3b41224d` | feat(Lib): preserve hyperbolic curve lengths under centering | cherry-pick | b20-24 |
| 25 | `d4d2be27` | `00d93652` | feat(Lib): glue absolute continuity across weak subdivisions | cherry-pick | b25-29 |
| 26 | `0fbb2873` | `8e3e571d` | feat(Lib): bound scalar variation by absolute derivative integral | cherry-pick | b25-29 |
| 27 | `826a4dec` | `3869d257` | feat(Lib): prove hyperbolic polar calculus and radial length bounds | cherry-pick | b25-29 |
| 28 | `0284a59d` | `805baec7` | feat(Lib): derive monotonicity from derivative integral equality | cherry-pick | b25-29 |
| 29 | `30994575` | `25b5832d` | feat(Lib): prove constancy across weak finite subdivisions | cherry-pick | b25-29 |
| 30 | `87ffe268` | `25d36355` | feat(Lib): prove centered hyperbolic distance and minimizer uniqueness | cherry-pick | b30-34 |
| 31 | `30eea821` | `ba3f4793` | feat(Lib): construct arbitrary-center minimizing segments and distance | cherry-pick | b30-34 |
| 32 | `05eb3fba` | `a516c865` | feat(Lib): prove continuous hyperbolic segment endpoint families | cherry-pick | b30-34 |
| 33 | `21dbfb06` | `9a6965ac` | feat(Lib): characterize complete hyperbolic geodesics and plane sections | cherry-pick | b30-34 |
| 34 | `9c2ebacb` | `4329360b` | feat(Lib): identify hyperbolic length metrics with model topology | cherry-pick | b30-34 |
| 35 | `992840df` | `a700536c` | feat(Lib): characterize centered hyperbolic length balls | cherry-pick | b35-39 |
| 36 | `bc23c9ab` | `510c6d32` | feat(Lib): prove centered hyperbolic length balls compact | cherry-pick | b35-39 |
| 37 | `b261399d` | `6c9d0686` | feat(Lib): prove properness of hyperbolic length metrics | cherry-pick | b35-39 |
| 38 | `96c29b75` | `d478f193` | feat(Lib): prove completeness of hyperbolic length metrics | cherry-pick | b35-39 |
| 39 | `7684a773` | `94d8323e` | feat(Lib): exclude ideal escape for hyperbolic Cauchy filters | cherry-pick | b35-39 |
| 40 | `b0260e41` | `84dadabe` | feat(Lib): prove finite-length hyperbolic tails are Cauchy | cherry-pick | b40-44 |
| 41 | `5859bf51` | `be33e1a8` | feat(Lib): present real planes by coefficient and Lorentz normals | cherry-pick | b40-44 |
| 42 | `1d54e099` | `13a540cd` | feat(Lib): add unit-normal bilinear and Lorentz reflections | cherry-pick | b40-44 |
| 43 | `0d854d5f` | `8981fcf1` | feat(Lib): construct hyperbolic axes from unit normals | cherry-pick | b40-44 |
| 44 | `71123c42` | `137b344b` | feat(Lib): construct hyperboloid graph homeomorphism and connectedness | cherry-pick | b40-44 |
| 45 | `4d9d0727` | `c17cf741` | feat(Lib): construct and classify Lorentz plane unit normals | cherry-pick | b45-49 |
| 46 | `19e89005` | `9702edf4` | feat(Lib): restrict Lorentz reflections to smooth hyperboloid involutions | cherry-pick | b45-49 |
| 47 | `f910d74d` | `a2c10a8a` | feat(Lib): identify the two components cut by a hyperbolic axis | cherry-pick | b45-49 |
| 48 | `b8af9b41` | `490bc583` | feat(Lib): prove positivity of hyperbolic plane discriminants | cherry-pick | b45-49 |
| 49 | `c8a2213d` | `e3c3aee1` | feat(Lib): prove hyperboloid reflections preserve the tangent metric | cherry-pick | b45-49 |
| 50 | `c3c136b4` | `a52b0fa9` | feat(Lib): identify hyperbolic reflection axes and side exchanges | cherry-pick | b50-51 |
| 51 | `8ea19482` | `752dfd1e` | feat(Lib): pull back hyperbolic plane equations to coordinates | cherry-pick | b50-51 |

## 3. Deviations and integration notes

Only the two `RiemannMapping` commits deviate; their notes are in the commit messages.

The source appends 215 lines (two declarations, nothing else) to `Lib/Analysis/Complex/RiemannMapping.lean`,
which on the target is an imports-only facade (wave 2). Per declaration:

| declaration | source commit | uses (project names) | landed in | statement block vs source |
|---|---|---|---|---|
| `RiemannBoundary.principalRoot_three_reverse_of_wedge` | `b3f08b95` → `259b165e` | `RiemannBoundary.principalRoot`, `RiemannBoundary.principalRoot_pow_of_sector` (both in `Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean`) | `Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean` (end of file); probe appended to `Lib/AxiomAudit.lean` | identical (`diff` of the 97-line block: empty) |
| `RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge` | `e238166c` → `044f1f68` | `RiemannBoundary.rotatedPrincipalRootFour`, `RiemannBoundary.quarticRootRotation` (moved by wave 2 to `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`), `RiemannBoundary.principalRoot`, `norm_principalRoot`, `arg_principalRoot` | `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean` (end of file) — not `Lib`, since `Lib` never imports `Hopf`; the replayed commit therefore changes `Hopf/Proof`, not `Lib`; probe to `Hopf/Proof/AxiomAudit.lean` (new `import Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots` and a section `## Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots`) | identical (`diff` of the 116-line block: empty) |

Placement of the cube-root lemma is by its dependencies, as the brief asks; by topic it belongs with the
exponent-3 statements (`principalRoot_three_upper`, …) that wave 2 moved to `SectorRoots` as project
material. See "Left".

Probe accounting: the range adds 882 non-blank lines to `Lib/AxiomAudit.lean`; 880 are there (the target's
`8ff8d81e` file is a prefix of the new one), the other 2 are the quartic probe in `Hopf/Proof/AxiomAudit.lean`.
All nine `Lib.lean` imports of the range are present; the range removes no line from either file.

## 4. The merge commit `12f41cf0`

`12f41cf0` ("Merge native atlas endpoint with the reduced center circuit", parents `027540fc`, `3c094688`) is
in `bcf711d6..8ea19482` but has no `Lib` diff of its own: `git diff 12f41cf0^1 12f41cf0 -- Lib Lib.lean` and
`git diff 12f41cf0^2 12f41cf0 -- Lib Lib.lean` are both empty, `git log bcf711d6..12f41cf0^1 -- Lib Lib.lean`
and `git log bcf711d6..12f41cf0^2 -- Lib Lib.lean` list nothing, and `git diff bcf711d6 12f41cf0^1 -- Lib
Lib.lean` is empty. Not replayed.

## 5. Final checks on `752dfd1e` (logs in this directory)

```
lake build Lib                                   (final-lib.log)
Build completed successfully (9428 jobs).
lake build Solution S6Shortcuts S6 Challenge     (final-chain.log, 265 s; 14 Hopf/Solution/S6 modules rebuilt,
                                                  among them Hopf.Proof.LCP.AnalyticFillings, which imports SectorRoots)
Build completed successfully (9489 jobs).
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit  (final-axioms.log: header, every axiom line, tail)
Build completed successfully (9431 jobs).
  'depends on axioms' lines: 3741 (Lib/AxiomAudit.lean 3736, Hopf/Proof/AxiomAudit.lean 5)
  'does not depend on any axioms' lines: 13
  distinct axioms: propext (2241), Quot.sound (2229), Classical.choice (2114); sorryAx: 0
python3 scripts/lib_stock_census.py --check      (final-census.log)
ratchet PASS: 123 <= baseline 1648
grep -rnE '^(public )?import Hopf' Lib/ --include=*.lean   (final-importgrep.log)
(empty; exit 1)
```

Environment diff (`final-envdiff.log`; dump `lake env …/lean-agent-ide dump Solution Lib --modules Hopf,Lib`,
39,175 constants; base dump 38,373), `envdiff.txt` verbatim:

```
constants before 38373 after 39175 (keys 38271 39073 )
lost 0 added 802 of which source declarations: 0 463 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 339 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
  (20 `ADDED` sample lines omitted here; see envdiff.txt)
```

The tool's verdict FAILs on any unaccepted addition. Rerun with `--accept` for each of its 463 source
additions (`accept.txt`; `envdiff-accepted.txt`/`.json`):

```
constants before 38373 after 39175 (keys 38271 39073 )
lost 0 added 802 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 802 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

0 lost, 0 changed types, no module moves. The 463 added source constants are exactly the range's new
declarations: the 454 `theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance`/… headers in
`git diff bcf711d6 8ea19482 -- Lib` (each found among the additions, private ones included), the two
`local instance`s `Manifold.lengthTangentT2` and `Manifold.lengthRefinementT2` (`CurveTransport.lean`), and the
seven syntax constants of `local notation` in `Models.lean`: `Hyperbolic.termV`, `termF`, `termB`, `termI`,
`termJ`, `termK`, `termK_1`. The other 339 added constants are auxiliary (`_proof_`, `match_`, `eq_`,
`congr_simp`, …). By module: `Hyperbolic.Models` 360, `Riemannian.CurveTransport` 47, `Order.Fin.Refinement` 29,
`BilinearForm.Reflection` 9, `CurveVariation` 7, `GeodesicEquations` 7, `Mobius` 3, `Group.Prod` 2,
`VectorBundle.Riemannian` 2, `InnerProductSpace.FiniteDimensional` 1, `BoundaryLimits` 1,
`RiemannMapping.PrincipalRoot` 1, `Hopf.Proof…SectorRoots` 1 (non-aux constants, 470 incl. 7 `congr_simp`).

Content check against the source: for each of the nine new files of the range
(`Analysis/Calculus/CurveVariation`, `Analysis/InnerProductSpace/FiniteDimensional`,
`Geometry/Hyperbolic/{GeodesicEquations,Models}`, `Geometry/Manifold/Riemannian/CurveTransport`,
`Geometry/Manifold/VectorBundle/Riemannian`, `LinearAlgebra/BilinearForm/Reflection`, `Order/Fin/Refinement`,
`Topology/Compactification/BoundaryLimits`) `git diff 8ea19482 752dfd1e -- <file>` is empty; there are no
adaptation commits. `RiemannMapping`: see §3.

## 6. Left (noticed, not done)

- `Lib/Geometry/Hyperbolic/Models.lean` is 7,870 lines, one module (360 source declarations). Split is a later
  step. `wc -l Lib/Geometry/Hyperbolic/Models.lean`
- Manuscript-style labels in docstrings: 275 added lines of the range match
  `textbook|canonical line|G0[0-9]|.md\``; per current file (`textbook|canonical line|G0[0-9]`): `Models` 255,
  `GeodesicEquations` 7, `CurveTransport` 3, `Reflection`, `Refinement`, `BoundaryLimits`, `PrincipalRoot`,
  `SectorRoots` 1 each; e.g. "Textbook source: `CENTER_…_TEXTBOOK.md`, lines 86–100, FREE G3a–G3c".
  `git diff bcf711d6 8ea19482 -- Lib | grep '^+' | grep -c -i 'textbook\|canonical line\|G0[0-9]\|\.md`'`;
  per file `grep -c -i 'textbook\|canonical line\|G0[0-9]' Lib/Geometry/Hyperbolic/*.lean …`
- Modules of the range not imported by `Lib.lean`: none (all nine new modules are imported).
  `for m in …; do grep -qx "import $m" Lib.lean || echo $m; done`
- Overlap with Mathlib's `UpperHalfPlane` metric API: `Models.lean` defines its own
  `Hyperbolic.upperHalfPlaneLengthMetricSpace : MetricSpace UpperHalfPlane` (Riemannian length metric) and proves
  `properSpace_upperHalfPlaneLengthMetricSpace` / `completeSpace_upperHalfPlaneLengthMetricSpace`, while Mathlib
  (`Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`, not imported by `Models.lean`) has `instance :
  MetricSpace ℍ` with `UpperHalfPlane.dist_eq`/`cosh_dist` and `instance : ProperSpace ℍ`. No lemma identifies the
  two distances (no use of `UpperHalfPlane.dist`/`cosh_dist` in `Lib/Geometry/Hyperbolic/`); the hyperboloid
  formula `hyperboloidLengthDist_cosh`/`_arcosh` is the natural bridge. Not a literal duplicate (different
  definitions), but the properness/completeness results duplicate Mathlib's for the equal metric.
  `grep -n 'upperHalfPlaneLengthMetricSpace\|properSpace_\|completeSpace_' Lib/Geometry/Hyperbolic/Models.lean`;
  `grep -n 'instance' .lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`
- `RiemannBoundary.principalRoot_three_reverse_of_wedge` sits in `Lib` (`PrincipalRoot.lean`) by the
  dependency rule, but it is an exponent-3 statement of the kind wave 2 moved to `Hopf/Proof/…/SectorRoots.lean`
  as project material; owner decision whether to move it there too.
  `grep -n 'principalRoot_three' Lib/Analysis/Complex/RiemannMapping/PrincipalRoot.lean Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`
- `Hopf/Proof/AxiomAudit.lean`'s module docstring still says it probes only the four two-sphere theorems; it now
  also probes `rotatedPrincipalRootFour_reverse_of_wedge`. `sed -n 8,25p Hopf/Proof/AxiomAudit.lean`
- Linter warnings in the replayed code (unchanged from the source, not fixed), counted in `b50-51.log`:
  `Models` 201, `CurveTransport` 35, `Mobius` 12 (file total), `FiniteDimensional` 7, `BoundaryLimits` 6,
  `Refinement` 5, `GeodesicEquations` 2, `PrincipalRoot` 2 (the new lemma's `simpa` → `simp at`),
  `CurveVariation` 1, `SectorRoots` 1. `lake build Lib 2>&1 | grep '^warning' | cut -d: -f2 | sort | uniq -c`
  (needs a rebuild of those modules to re-emit; or the scratch logs).
- Source commits `d335e3ff`/`d2aa179a` carry author dates of 2026-09-20/25 although they come after
  `bcf711d6`; kept as is.
