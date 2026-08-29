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
