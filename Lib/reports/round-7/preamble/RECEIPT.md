# Round 7 — stock preamble cleanup in `Lib/`

Branch `r7/preamble`, base `46c22597`, Lean v4.33.0 / Mathlib v4.33.0.
Scope: whole-line deletions in `Lib/**/*.lean` only.  No `import` line was touched,
no `set_option backward.*` or `maxHeartbeats` line was touched, no declaration was
added, removed or changed.  The tool is
[`preamble_clean.py`](preamble_clean.py) (categories a, c, d) plus
[`apply_minimized_open.py`](apply_minimized_open.py) (category b).

## The stock preamble

The block the textbook audit found (cross-cutting finding 2) is, verbatim:

```
set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f
```

The `open scoped …` line is four physical lines and occurred character-for-character
identically in all 96 files that carried it.  `open Set Function Filter Manifold Topology`
(111 files) is not a `open scoped` line and was out of scope for this round.

## Removal rules (verbatim, as applied)

**(a) `set_option maxSynthPendingDepth`** — delete every line matching

```
^set_option\s+maxSynthPendingDepth\s+\d+\s*$
```

(no leading whitespace, i.e. a file-top-level command; any value of N, not just 3).

**(b) stock `open scoped` block** — delete the four-line block above wherever it
occurs verbatim; rebuild; in every file that then fails, restore the block and
minimise it namespace by namespace: starting from the full 22-namespace list, drop
each namespace in turn and keep the drop only when the file still compiles on its
own (`lean <file>` with the project `LEAN_PATH`, deps prebuilt).  The surviving list
is written back as a single `open scoped …` line.

**(c) `universe`** — delete every line matching

```
^universe\s+([A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\s+[A-Za-z_][A-Za-z0-9_'₀-₉]*)*)\s*$
```

for which *every* declared name is unused in the rest of the file, where "used"
means the name occurs, as a whole word
(`(?<![A-Za-z0-9_₀-₉'])NAME(?![A-Za-z0-9_₀-₉'])`), in at least one of these
universe positions:

```
(?:Type|Sort)\s*NAME          Type u / Sort v
\.\s*\{[^}]*NAME[^}]*\}       C.{u} / Type.{u, v}
\b[im]?max\b[^\n]{0,80}?NAME  max u v / imax u v
(?:Type|Sort)\s*\([^)\n]*NAME Type (max u v)
NAME\s*\+\s*\d                u + 1
universe\b[^\n]*NAME          another universe command
```

A line with a mix of used and unused names is left untouched.

**(d) `local` notations** — delete every line matching

```
^local\s+(?:notation|infix|infixr|infixl|prefix|postfix)\b
```

whose *distinguishing token* — the longest string literal to the left of `=>`,
stripped of surrounding whitespace — does not occur anywhere else in the file.
For the two stock lines the distinguishing tokens are `≫ₚ` and `∣[`.

In every category, deleting a line also deletes one immediately following blank
line when the preceding line is blank too, so no double blank is left behind.

## Results per category

| | files with the pattern | files edited | lines removed | lines added |
|---|---|---|---|---|
| (a) `set_option maxSynthPendingDepth 3` | 110 | 108 | 108 | — |
| (b) stock `open scoped` block | 96 | 96 | 384 | 68 |
| (c) `universe` | 233 `universe` commands in 230 files | 90 | 90 | — |
| (d) `local notation` / `local infixr` | 69 | 69 | 137 | — |
| (restorations, see below) | | 4 | — | 9 (1 removed) |

`git diff --shortstat 46c22597 HEAD -- 'Lib/**/*.lean'`:
**110 files changed, 68 insertions(+), 1074 deletions(-)**.

### (a) 108 files, 108 lines

All 110 occurrences were the identical line `set_option maxSynthPendingDepth 3`.
Two files were restored because the build fails without the option (instance
synthesis runs out of pending depth):

* `Lib/Analysis/Calculus/MorseLemma.lean` — 24 errors, e.g.
  `1219:4: failed to synthesize instance of type class`,
  `1633:25: Unknown identifier exists_congruencePolynomial_partialDiffeomorph`
* `Lib/Analysis/ODE/SmoothFlow.lean` — 4 errors, e.g. `164:2: Type mismatch`,
  `428:43: rewrite failed: did not find an occurrence of the pattern`

Four more files were restored later for the environment diff, see *Restorations
forced by the environment diff*.  Net effect: the option survives in 6 of 110 files.

### (b) 96 files, 384 lines removed, 68 lines added

Removing the block outright left 28 files green.  The other 68 were minimised as
described.  Sizes of the surviving lists: 49 files keep one namespace, 16 keep two,
2 keep three, 1 keeps six.  Frequency of the kept namespaces:

```
ContDiff 51   ContinuousMap 14   CategoryTheory 7   NNReal 5   ComplexConjugate 3
Convolution 2   Interval 2   ENNReal 2   InnerProductSpace 2
EuclideanSpace 1   UniformConvergence 1   Uniformity 1   Complex.UnitDisc 1
UpperHalfPlane 1   Matrix 1
```

The seven namespaces `BigOperators`, `Fin.NatCast`, `MatrixGroups`, `Modular`,
`Pointwise`, `RealInnerProductSpace`, `TensorProduct` are needed by no file at all.
The per-file result is in [`open-scoped-minimized.json`](open-scoped-minimized.json).
1565 single-file `lean` compiles were run to produce it.

### (c) 90 files, 90 lines

All 90 hits were the stock line `universe u v`; the rule found no other unused
`universe` command.  Of the 233 `universe` commands in `Lib/`, 143 declare at least
one name that is genuinely used in a universe position and were left alone.
No restoration was needed: the first `lake build Lib` after the edit was green.

### (d) 69 files, 137 lines

68 files lost both stock lines; `Lib/Topology/Homotopy/LoopSubdivision.lean` lost
only the `∣[` notation, because `≫ₚ` is actually used in that file — the rule kept
it automatically.  No restoration was needed: the first `lake build Lib` after the
edit was green.

## Restorations forced by the environment diff

A green build is not enough: the first environment diff (base vs. cleaned tree)
reported **PASS** but listed five source declarations whose public type hash had
changed.  Single-file `lean` probes with `set_option pp.explicit true` and
`set_option pp.universes true`, comparing the printed type of the declaration
against the base file, pinned each one:

| file | line restored | declaration(s) affected | why |
|---|---|---|---|
| `Lib/Analysis/Complex/Cousin.lean` | `set_option maxSynthPendingDepth 3` | `HolomorphicCousin.hasFDerivAt_cauchyGreen` | instance path |
| `Lib/Geometry/Manifold/Collar.lean` | `set_option maxSynthPendingDepth 3` | `DiskFraming.exists_smooth_frame_near_starConvex`, `DiskFraming.exists_smooth_frame_on_neighborhood_closedBall` | instance path |
| `Lib/Geometry/Manifold/Morse/Birth.lean` | `set_option maxSynthPendingDepth 3` | `MorseCancellation.hessian_comp_linearEquiv` | instance path |
| `Lib/Analysis/Complex/SquareRoot.lean` | `set_option maxSynthPendingDepth 3` **and** `ContDiff` in the narrowed `open scoped` line | `AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane` | instance path, then `ContDiff` |

"instance path": without the option, synthesis of `NormedSpace ℝ ℝ` resolves through
`NormedField.toNormedSpace` where the base resolved through
`InnerProductSpace.toNormedSpace ∘ RCLike.toInnerProductSpaceReal`.  The two are
definitionally equal — everything downstream still compiles — but the stored type
term, and hence the type hash, differs.  For `SquareRoot.lean` restoring the option
was not enough; a second minimisation run, this time keeping a namespace only when
the *printed type* still matched the base, gave the minimal list
`ContDiff UpperHalfPlane`.

After these four restorations the environment diff is clean.

## Builds

```
$ lake build Lib
Build completed successfully (9149 jobs).

$ lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9188 jobs).

$ lake build Lib.AxiomAudit
Build completed successfully (9152 jobs).
```

The axiom audit emits 3361 `depends on axioms` probes.  The only axiom names that
occur anywhere in its output are `propext` (3361), `Quot.sound` (3345) and
`Classical.choice` (3215); `sorryAx` occurs nowhere.  (`Challenge.lean:42` carries a
`sorry` at the base commit and still does; it is outside `Lib/` and untouched.)

## Environment diff

`lean-agent-ide dump` cannot load `Solution` and `Lib` into one environment — they
clash on `SpecialPeriods.Threefold.Star.Input`, declared both in
`Lib/Topology/Gluing/OverBase.lean` and in `Hopf/Proof/LCP/GlobalAssembly.lean`
(`import Lib.Topology.Gluing.OverBase failed, environment already contains …`).
The dump was therefore taken as two runs, `dump Lib --modules Lib` and
`dump Solution --modules Hopf`, concatenated into one table.

```
$ python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl --receipt envdiff.json
constants before 39159 after 38749 (keys 38535 38536 )
lost 20 added 15 of which source declarations: 0 0 ; names with changed type 14 of which source: 0
auxiliary lost/added/changed (not judged): 20 15 14
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 6
VERDICT PASS
```

**0 source declarations lost, 0 added, 0 changed.**  The 410 constants that
disappeared are the notation artifacts of the 137 deleted `local notation` /
`local infixr` lines and their unexpanders, all classified auxiliary and not judged.
Full receipt in [`envdiff.json`](envdiff.json), build lines in
[`build-summary.txt`](build-summary.txt).

## Commits

| hash | subject |
|---|---|
| `4ffc57e2` | remove unused maxSynthPendingDepth options from Lib preambles |
| `5314b057` | shrink the stock open scoped preamble line in Lib to what each file uses |
| `cd439ebf` | drop unused universe declarations from Lib preambles |
| `28bc8bf8` | drop unused local notations from Lib preambles |
| `779accf3` | restore preamble lines that five declarations' elaborated types depend on |
