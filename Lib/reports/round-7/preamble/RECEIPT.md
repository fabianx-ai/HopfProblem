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

> **Method caveat (added on correction, 2026-09-21).**  `lakefile.toml` sets no
> `leanOptions`, so Lean v4.33.0's default applies and **`autoImplicit` is on in every
> one of the 96 files this rule was run on** (221 of the 446 `Lib/**/*.lean` files at
> the branch tip carry no `set_option autoImplicit false`, including all 96 category-(b)
> files and all 90 category-(c) files).  In such a file, dropping a namespace whose
> scoped notation is an identifier-like token (`ω`, `ℍ`, `𝔻`, `𝓤`, `𝒟`, `Ι`, `𝟙`,
> `𝟭`, `conj`, `SL(`, `GL(`) does **not** break the build: the token silently becomes an
> auto-bound implicit binder in the signature.  **Compile-success is therefore not
> evidence that a dropped namespace was unused**, and the criterion stated above is not
> sound on its own.  The guarantee for this branch rests entirely on the final
> type-hash environment diff, which did catch the one case that occurred
> (`Lib/Analysis/Complex/SquareRoot.lean`: with `ContDiff` dropped,
> `AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane` silently acquired a
> universally quantified `{ω : WithTop ℕ∞}` where the base had `ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω r`
> with `ω = ⊤`; the restoration table below files this under "instance path, then
> `ContDiff`" and never names the mechanism).  Two independent checks bound the residual
> risk: a token scan of all 96 files at the branch tip finds no remaining identifier-like
> scoped token in a file that dropped its namespace, and `#synth NatCast (Fin 3)` /
> `#synth Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)` both fail globally, so
> the dropped `Fin.NatCast` / `EuclideanSpace` scoped instances cannot have been silently
> replaced.  Any future compile-based minimisation must run with `autoImplicit` off
> (`-DautoImplicit=false`, or a `set_option` inserted first) so a dropped
> identifier-like notation fails loudly.  (The round-7 brief's premise, "`autoImplicit`
> is off repo-wide", is false for half of `Lib`.)

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
| (c) `universe` | 233 `universe` commands in **227 (corrected; the receipt said 230)** files | 90 | 90 | — |
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
2 keep three, 1 keeps six.  **(corrected)** this is the *pre-restoration* distribution;
`open-scoped-minimized.json` at head reads 48 / 17 / 2 / 1, and the frequency table below
is *post-restoration* (commit `5314b057` says `ContDiff` 50, the table says 51).  Frequency of the kept namespaces:

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

**(corrected)** the branch deletes **89 × `universe u v` and 1 × `universe u v w`** — the
last in `Lib/Topology/MappingTorus/Wang.lean` (commit `cd439ebf`), where `w` is unused as
well, so the deletion is right and only the sentence "all 90 hits were the stock line
`universe u v`" was false.  The rule found no other unused `universe` command.  Of the 233 `universe` commands in `Lib/`, 143 declare at least
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
`Classical.choice` (3215); `sorryAx` occurs nowhere.  (`Challenge.lean:46` **(corrected;
the receipt said l.42)** carries a `sorry` at the base commit and still does; it is outside
`Lib/` and untouched.)

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

**0 source declarations lost, 0 added, 0 changed.**  **(corrected)** the 410 constants that
disappeared are **not** all notation artifacts.  The arithmetic is

```
411 notation artifacts  (138 local notations at base − 1 kept, × 3 constants each)
+ 14 _proof_ auxiliaries lost   (CrossProduct.lean, see below)
−  15 _proof_ auxiliaries added (same file)
= 410
```

`envdiff.json`'s `lost` (20) is 6 notation-artifact names (`«term_≫ₚ_»`, `«term_∣[_]_»`,
two `_aux_…macroRules…`, two `_aux_…unexpand…`, each aggregated over ~69 modules) **plus 14
`_proof_N` auxiliaries** of `PeriodTorusHigherHomology.formalAssociatorDefect` and
`PeriodTorusHigherHomology.triplePostcomp_mo1973_13949` in
`Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`; `added` (15) and
`changed_type_all` (14) are *only* those `_proof_` names.  The branch diff of that file is
the single line `-set_option maxSynthPendingDepth 3` — it never carried the stock
`open scoped` block — so **removing the option changed the elaborated value of a `def`**:
at head, `formalAssociatorDefect._proof_2` / `_proof_3` are `SMulCommClass ℤ ℤ (…)`
obligations discharged by `AddGroup.int_smulCommClass` and `_proof_5` the same class by
`LinearMap.instSMulCommClass`, where the base had one `_proof_` fewer with different hashes.
`SMulCommClass` is a `Prop`, so the change is proof-irrelevant and benign, and
`formalAssociatorDefect_apply` is still `rfl`.  It is nevertheless direct evidence that
`envdiff.py` compares **types only**, that removing `maxSynthPendingDepth` did change
definition *bodies*, and that **definition values were not compared in the 104 files that
lost the option** — the same "instance path" class of change this branch chose to *restore*
where it surfaced in four types.  All constants above are classified auxiliary and not
judged by the tool.
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

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-preamble.md` (ACCEPT WITH FINDINGS; the end state is
sound — every deletion is a whole preamble line, the four restored files carry the option at head,
`envdiff` shows 0 source declarations lost/added/changed, no hygiene issue; what the reviewer
refuted is this receipt's description of its own method and of its own envdiff).  These corrections
are to this receipt's text only; no Lean file was changed by them.

1. **The `open scoped` minimisation criterion is not sound in these files, and the receipt did not
   say so (finding 1).**  A "Method caveat" paragraph is now inserted under rule (b) above.  In
   short: `lakefile.toml` sets no `leanOptions`, so `autoImplicit` is **on** in all 96 minimised
   files (and in 221 of the 446 `Lib` files); dropping a namespace whose scoped notation is an
   identifier-like token makes the token an auto-bound implicit instead of an error, so
   compile-success is not evidence that the namespace was unused.  The only guarantee is the final
   type-hash envdiff, which caught the one case that occurred (`SquareRoot.lean`, `ω`).  Future
   compile-based minimisation runs with `autoImplicit` off (`Lib/reviews/REVIEW-7-8.md` §4).

2. **The 410-constant churn is reconciled, and a definition body changed (finding 2).**  The
   environment-diff section now carries the arithmetic: **411 notation artifacts + 14 `_proof_`
   lost − 15 `_proof_` added = 410**, with the `_proof_` churn attributed to
   `PeriodTorusHigherHomology.formalAssociatorDefect` / `triplePostcomp_mo1973_13949` in
   `CrossProduct.lean`, whose only change on this branch is the removal of
   `set_option maxSynthPendingDepth 3`.  The change is a `Prop`-valued `SMulCommClass` instance
   path, hence proof-irrelevant and benign, but it shows that `envdiff.py` hashes types only and
   that definition values were **not** compared in the 104 files that lost the option.  The receipt
   as first written filed the whole 410 under "notation artifacts".

3. **"All 90 hits were the stock line `universe u v`" is false (finding 3).**  It is **89 ×
   `universe u v` + 1 × `universe u v w`** (`Lib/Topology/MappingTorus/Wang.lean`, commit
   `cd439ebf`); `w` is unused there too, so the deletion stands.  Corrected in place, together with
   "233 `universe` commands in 230 files" → **227 files** (230 counts files with any line starting
   `universe`, three of them inside docstrings).

4. **The instance-path description does not match the file checked (finding 4).**  This receipt says
   "synthesis of `NormedSpace ℝ ℝ` resolves through `NormedField.toNormedSpace` where the base
   resolved through `InnerProductSpace.toNormedSpace ∘ RCLike.toInnerProductSpaceReal`".  At head,
   `@HolomorphicCousin.hasFDerivAt_cauchyGreen` (`Cousin.lean`, option restored) carries
   `@InnerProductSpace.toNormedSpace ℝ ℂ Real.instRCLike _ instInnerProductSpaceRealComplex` — the
   class is `NormedSpace ℝ **ℂ**` and the inner-product instance is `instInnerProductSpaceRealComplex`,
   not `RCLike.toInnerProductSpaceReal`.  The description may hold for the `Collar`/`Birth` cases
   (`E = ℝ`); that was not checked.  The substantive claims of that section — the option is present
   at head in exactly `Cousin`, `SquareRoot`, `Collar`, `Birth` (+ `MorseLemma`, `SmoothFlow` = 6 of
   110), and `changed_type_source` is empty — are verified.

5. **Small internal inconsistencies (finding 5), corrected in place.**  "49 keep one namespace, 16
   keep two" is the pre-restoration distribution (the JSON at head reads 48 / 17 / 2 / 1) while the
   frequency table is post-restoration (`ContDiff` 51 there, 50 in commit `5314b057`);
   `Challenge.lean`'s pre-existing `sorry` is at line **46**, not 42.  The "1565 single-file `lean`
   compiles" figure remains **unverifiable**: no compile log is in the receipt directory, and
   `open-scoped-minimized.json` records `error: ""` for every file, which carries no information.
   A future minimisation JSON should record the compile log path or hash per file and the
   `autoImplicit` flag.
