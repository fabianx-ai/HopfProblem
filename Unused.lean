import Unused.Topology.Dimension.CubeBoundaryThreeCells

/-!
# `Unused`: proved declarations that nothing uses

This tree holds proved declarations that no other declaration of the project uses.  They are
neither deleted nor kept in `Lib`: they are moved here verbatim (statement, proof, docstring and
attributes unchanged; only a visibility modifier may change where the move forces it), so that an
environment diff of the move shows module moves only.  The tree is neither for Mathlib nor for
anything else; it just exists.

Rules: a module of `Unused` may import `Lib` (also with `import all` of a `Lib` module, to reach
the private helpers of the declarations it received); nothing imports `Unused` — not `Lib`, not
`Hopf`, not a root file.  It is not a default target; the check chain builds it explicitly with
`lake build Unused`.

## Modules

* `Unused.Topology.Dimension.CubeBoundaryThreeCells`: the dead lemmas of the pieces of
  `Lib.Topology.Dimension.CubeBoundaryThreeCells` (receipt `Lib/reports/unused/cube3.md`).
-/
