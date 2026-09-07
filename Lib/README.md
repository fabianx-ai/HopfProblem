# `Lib/` — reusable mathematics

`Lib/` holds general mathematics formalized in this repository: statements that make no
reference to the six-sphere construction (the threefold, its cusps, period lattices, elliptic
fibres, honeycombs, or any `Fin 6`/`Fin 7`-specific datum). Everything here is written to be
upstream-bound: Mathlib-shaped file paths (`Lib/AlgebraicTopology/…`, `Lib/Geometry/Manifold/…`,
`Lib/Analysis/Complex/…`), Mathlib naming conventions, a docstring on every public declaration
stating the textbook result, and no dependency on the project: **a file under `Lib/` never
imports `Hopf.*`, `S6.*`, `S6Shortcuts`, `Challenge` or `Solution`.** The finished extraction of
the degree-one Hurewicz theorem into `Mathlib/AlgebraicTopology/Hurewicz/*`
(github.com/fabianx-ai/mathlib4, PR #4) is the template for what a `Lib/` file should become.

## Placement rule (FREE / CHARGED)

The rule is stated in `lean-protocol.md` at the repository root, **Stage 4: FREE-first file
placement**, with the governing principle in its **Purpose** section and the placement axis in
**Axis 4: presence / geometry**. In short: a result is FREE when its statement does not depend
on the motivating construction; FREE results live under `Lib/` at their natural reusable level.
A result is CHARGED only when it substitutes the explicit objects of the construction into a
FREE theorem; CHARGED results stay under `Hopf/` as thin adapters whose proofs visibly invoke
the `Lib/` interface. "Where would humanity look for this theorem next time?" decides the file.

## Stock rule (the ratchet)

Most of the generic mathematics of this project still lives inside `Hopf/` (see
`Lib/EXTRACTION_PLAN.md`). The number of such *stock* declarations is checked in:

- `scripts/lib_stock_prefixes.txt` — the declaration-name prefixes classified generic by the
  census (one entry per line; `Prefix`, `Prefix.Sub`, or `Hopf/File.lean:Prefix`);
- `scripts/lib_stock_baseline.txt` — the committed count.

**The committed number may only decrease.** The CI / ratchet step is

```sh
python3 scripts/lib_stock_census.py --check      # exit 1 if the count exceeds the baseline
python3 scripts/lib_stock_census.py --update     # after an extraction: lower the baseline
python3 scripts/lib_stock_census.py --by-file    # the per-file / per-prefix table
```

The script needs no Lean toolchain. It also fails if any `Lib/**/*.lean` imports a project
module. A commit that moves declarations out of `Hopf/` runs `--update` and commits the
lowered baseline together with the code; adding an entry to the prefix list is allowed only
with a census row in `Lib/EXTRACTION_PLAN.md` justifying it; raising the baseline by hand must
be justified in the commit message.

## Definition of done for an extraction lane

Lanes are defined in `Lib/EXTRACTION_PLAN.md`. A lane is done when all of the following hold:

1. **Axis 1 first.** A textbook file exists — `Lib/<path>/TEXTBOOK.md` next to the new files,
   or `Lib/docs/<lane>.md` — giving, in ordinary mathematics with no Lean names, the theorem(s)
   the lane moves, the reference (book, theorem number), and for a *pure move* the
   correspondence table block → textbook theorem → `Lib` file → declaration names; for a
   *generalize-then-move* lane the complete textbook proof of the generalized statement
   (`lean-protocol.md`, Stages 1–3), then the decomposition, then the typed ledger, then Lean.
2. No `sorry`, no `axiom`, no `proof_wanted` under `Lib/`.
3. `#print axioms` on every top theorem of the lane (listed in the plan) shows exactly
   `propext`, `Classical.choice`, `Quot.sound`; the probes are added to `Lib/AxiomAudit.lean`.
4. Every moved declaration is deleted from `Hopf/`; every consumer named in the plan is
   re-routed (`import Lib.…`) and `lake build` of each consumer module is green; the final
   consumers `Hopf.Final` and `Solution` build; the Comparator verdict is unchanged.
5. `python3 scripts/lib_stock_census.py --check` passes and the baseline was lowered.
6. `Lib.lean` imports the new modules; `git diff --check` is clean.
7. A report `Lib/reports/<lane>.md` records what moved, consumers re-routed, census before /
   after, the `#print axioms` output, wall-clock build times, and open items.

## Branch and commit conventions

- One branch per lane, `lib/<lane-id>-<slug>` (e.g. `lib/A-singular-homology`), off
  `lib/textbook-extraction`.
- Commit message prefix `lib(<lane>):`, e.g. `lib(A): move Mayer–Vietoris to
  Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean`. One commit per `Lib` file or
  per independently green unit; each commit builds.
- **Transitional namespace rule.** On first landing a moved file may keep
  `namespace Mathoverflow1973` and the original declaration names, with `export`/`alias`
  shims left in `Hopf/` so that consumers with hundreds of references stay green. The rename
  to Mathlib-style names and namespaces is a separate second commit in the same lane
  (`lib(<lane>): rename …`), and the lane is not done until it has landed.
- Statements of moved theorems do not change in a pure-move lane (only names, namespaces and
  `variable` binders). A statement change is a generalize-then-move item and needs the
  textbook file.
- Never push; leave attribution to the repository owner's instructions.
