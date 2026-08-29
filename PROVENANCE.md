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

## Square-zero cusp exchange

`Hopf/Shortcuts.lean` defines the integral dual-cusp endomorphism
`dualCuspN = Matrix.toLin' (M₀ - 1)` and proves it square-zero from Hopf's
existing coordinate formula.  `Hopf/LCP/LocalModels.lean` then identifies the
explicit cusp matrix family with `S6.SquareZeroExchange.exchange dualCuspN`
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
