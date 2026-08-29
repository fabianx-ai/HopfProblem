# Provenance

This tree is a move-only reorganization of
[`plby/HopfProblem`](https://github.com/plby/HopfProblem) at commit
`9ac8a456b526527837d7082ff775213ca8bc9809` (Apache-2.0).

The original `Solution.lean` had SHA-256 `fda66f602707b290cf7fba9111506b39d72b2f509f9ebb44a1901471c69dec49`.  Its declaration
body, original lines 80--248811 inclusive, is partitioned into the `Hopf/`
modules listed in `SPLIT_MANIFEST.json`.  Each listed body is an exact byte
slice of that pinned source; no proof body or theorem statement is edited by
the extraction.  Module wrappers and imports are the only generated Lean text
outside those slices.  All 2,543 original attribute commands are command-scoped
wrappers and remain inside their exact body slices.

The full original attribution/license header is retained in every extracted
Lean module and in the public root aggregator.  `Solution.lean` imports
`Hopf.Final`.  The original `Challenge.lean`, `LICENSE`, and comparator
configuration are not changed by the splitter.  Mathematical equivalence must
additionally be certified by a green `lake build`, unchanged Comparator
verdict, and unchanged per-theorem axiom audit before committing the
reorganization.

The audited splitter is retained on the split branch as
`scripts/split_solution.py`.  It intentionally remains outside its own
generated-state hash map, avoiding circular self-authentication; Git and the
external attestation receipt pin the script itself.  A second run validates
all generator-owned output and leaves the script untouched.

## V10 algebraic shortcut source

The `simplify/v10-shortcuts` branch imports the following unconditional Lean
sources from the companion S6 V10 release at commit
`8e83d2d2bc4e4ba32b8dfe0ecfe9094d3834cea0`:

- `S6Shortcuts.lean`;
- `S6/CyclicAverage.lean`;
- `S6/LatticeOrbitIndex.lean`;
- `S6/SquareZeroExchange.lean`;
- `S6/TwoExceptionalGluing.lean`;
- `S6/UnitTransgression.lean`.

Those six files are copied byte-for-byte from
`formal/lean-source/` in that source commit.  They contain 1,244 lines and 165
source declaration commands: 149 are non-private/non-local, 14 are private,
and 2 are local.  The new `S6.lean` file is only the local Lake routing root.
The source project used Lean 4.31.0-rc1; the unchanged files also elaborate
under this repository's pinned Lean 4.33.0/Mathlib v4.33.0 environment.  They
are included under this repository's Apache-2.0 license.

The initial port changes no Hopf theorem or proof.  Later entries in this file
must identify each replacement or explanatory bridge, its exact S6 source
module, measured source delta, build/axiom gate, and final Comparator status.

## Section 6 reusable linear-algebra library

The proof-independent parts of V10 Lemmas 6.1--6.3 and 6.6 now live under
`Lib/LinearAlgebra/`.  `Lib.lean` is a public routing root and a separate Lake
library target.  It imports no `S6Shortcuts`, `S6`, `Hopf`, `Challenge`, or
`Solution` module.  The concrete matrix certificates remain in `S6/` as
proof-owned adapters which import the reusable layer.

This first extraction exports 25 reusable source declarations: 10 for cyclic
averaging, 11 for square-zero exchanges, and 4 for full-rank integral lattice
index.  Their general theorem bodies were moved intact from the checked V10
modules; the only proof-text modernization is Mathlib's nonsemantic
`LinearEquiv.ofLinearMap` spelling for the deprecated alias
`LinearEquiv.ofLinear`.  `Lib/AxiomAudit.lean` queries every export directly.

In the expansion ledger, all 25 exports are library assets and therefore
**free**.  The namespace-routing edits in the S6/Hopf consumers are
proof-specific adapters; this extraction does not count library lines,
declarations, or bytes as proof cost.  It also makes no claim that every
export is already a verbatim Mathlib pull request: natural-namespace and
generality refinement is a separate, checker-gated library step.  Comparator
remains deferred to the single final accumulated-change gate.

## Square-zero cusp exchange

`Hopf/Shortcuts.lean` defines the integral dual-cusp endomorphism
`dualCuspN = Matrix.toLin' (M₀ - 1)` and proves it square-zero from Hopf's
existing coordinate formula.  `Hopf/LCP/LocalModels.lean` then identifies the
explicit cusp matrix family with
`Lib.LinearAlgebra.SquareZeroExchange.exchange dualCuspN`
and proves `cuspIntegralMatrix_add` through the generic
`exchange_mul_exchange` theorem.  The public additive-law statement and all
downstream consumers are unchanged.

Relative to the source-port commit, this replacement adds one 35-line bridge
module and changes the local-model file by +15/-4 lines: **+46 Lean lines,
+1,569 bytes, and +3 public declaration commands project-wide**.  It is an
explanatory routing improvement, not a net source shrink.  The commit receipt
under `~/s6-notes/hopf/phase5/commit02-squarezero/` records the Lake and direct
per-theorem axiom gates.  Per the current protocol, Comparator is deferred to
the one final accumulated-shortcuts run.

## Two-exceptional twist arithmetic

`Hopf/LCP/BoundaryTopology.lean` now defines `twistOrder` as the `(3,4)`
specialization of `S6.TwoExceptionalGluing.gluingDefect`.  The concrete
`main_twist_value` proof is `rfl`, rather than an invocation of the generic
consecutive-order theorem, so its previously empty axiom set remains empty.
The sole downstream unfolding exposes both routed definitions.  The 23 public
declaration statements and the presentation data remain unchanged; only
`c_twistOrder`'s unfolding proof is adjusted, so the former 140-line block is
retained at 142 source lines.  This commit makes no presentation-equivalence
or deletion claim.

Relative to the square-zero commit, the proof-source change is **+3 Lean
lines, +96 bytes, and 0 declaration commands**.  The receipt under
`~/s6-notes/hopf/phase5/commit03-twist/` records the Lake and direct
per-theorem axiom gates.  Comparator remains deferred to the one final
accumulated-shortcuts run.

## Rational cyclic-average endpoints

`Hopf/LCP/IntegralHomology.lean` now records that, after scalar extension to
`ℚ`, the order-three and order-four integral norm matrices are respectively
`3 • S6Shortcuts.P3` and `4 • S6Shortcuts.P4`.  These are explanatory
endpoints connecting Hopf's unnormalized integral norms to the normalized
projectors formalized in `S6.CyclicAverage`.

No integral or topological norm proof is replaced or deleted.  In particular,
the new rational equalities do not identify an integral fixed lattice, prove
saturation, or replace the homology-coordinate transport.  Relative to the
twist-arithmetic commit, this derived-only bridge adds **17 Lean lines, 803
bytes, and 2 public theorem declarations**.  The receipt under
`~/s6-notes/hopf/phase5/commit04-cyclic/` records the Lake and direct
per-theorem axiom gates.  Comparator remains deferred to the one final
accumulated-shortcuts run.

## Real cusp equivalence through square-zero exchange

`Hopf/Shortcuts.lean` now records the real scalar extension
`dualCuspNReal` of the integral dual-cusp endomorphism, together with its
coordinate formula and square-zero law.  `Hopf/LCP/LocalModels.lean`
identifies the real cusp matrix with the corresponding
`Lib.LinearAlgebra.SquareZeroExchange.exchange`, and defines `cuspRealEquiv` using the
generic `exchangeEquiv`.  Its public application formula, zero, addition,
negation, real-cast, complex-cast, and lattice-preservation interfaces are
retained; the one direct homology consumer is routed through the retained
application formula.

This is an abstraction replacement, not a mathematical or source-size
reduction.  Relative to the cyclic-average commit, the proof-source change is
**+21 Lean lines, +1,323 bytes, and +4 public declaration commands**.  The
receipt under `~/s6-notes/hopf/phase5/commit05-cusp-real/` records the full
Lake build, sampled aggregate process-group RSS, and direct per-theorem axiom
gates.  The RSS sample can double-count shared pages and can miss peaks between
samples; it is not a cgroup or unique-memory measurement.  Comparator remains
deferred to the one final accumulated-shortcuts run.
