# cube3 — Lib/Topology/Dimension/CubeBoundaryThreeCells.lean (agent 2, Opus 5.5, start 2026-10-01 19:59)

## Decisions
- Closure (closure.py over dump_head): 406 constants, 353 reached from other Lib modules
  (Bricks, Dimension, via the 19 public decls). The 36 unreached ranged decls are all
  module-private dead lemmas whose proofs use ~38 private helpers that Lib needs.
  => NO Hopf/Proof move (would need making helpers public API only for dead code, or
  `import all`, banned/impossible from non-module Hopf files). Listed in "Left" (deletion candidates).
- File is a `module`: decls are private by default. Splitting needs cross-piece decls `public`,
  defs `@[expose]`. Lists: pub.txt, expose.txt; applied by vis.py (adds modifier on the decl line,
  line numbers unchanged so dump ranges still anchor the tool).
- Plan: 7 pieces (partition.py PIECES): Lattice, Cells, Faces, Coverage, RelInterior,
  SquareBoundary, Separation. Split runs: run_split.sh <source> -> split/<P>.raw.lean; assemble.py.
- Plain `/- -/` comments on decls (lines 31-778, 94 of them) converted to `/-- -/` docstrings
  (needed so the tool carries them with the units; also gives docstrings to newly public decls).

## Done
- Old ZTest files deleted.
- 190d287c docstring conversion; 099a566a visibility (public/@[expose]; built green b1.log with
  CubeBoundaryThreeDimension); 344b7b6c split + facade (pieces built green b2.log; verbatim check:
  213/213 units found verbatim). No-expose trial (b3.log) showed exposures are needed.
- 9e1e83b5 19 docstrings rewritten (comment-only); 5cbc00f0 Lattice import trim (b4.log green).
- Public decls in pieces: 53, all with docstrings.

- envdiff PASS (moves only; 3/4 auxiliaries reconciled in receipt).
- Receipt Lib/reports/wave-2/cube3.md + cube3/ written; committed as the last commit (see git log).

## In progress
- nothing.

## Next
- nothing; report back (receipt path, commit range 190d287c..receipt commit, checks, Left).
