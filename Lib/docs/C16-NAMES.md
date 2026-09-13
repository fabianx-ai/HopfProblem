# C16 — `SecondHurewicz` → `Hurewicz.DegreeTwo` namespace cleanup

Acting seat Devin, powered by Fusion (GPT-6 Astra Low Thinking + SWE-2 Medium).

## Scope

Exact token-boundary substitution `SecondHurewicz` → `Hurewicz.DegreeTwo` applied to all
and only files under `Lib/AlgebraicTopology/Hurewicz/*.lean` containing the token:

`CubeChainDecomposition`, `CubeGluing`, `CubeSphere`, `CubeTriangulation`, `Degree`,
`HomotopyExtension`, `HopfDegree`, `Naturality`, `PrismOperator`, `SimplexCube`,
`Straightening`, `Subdivision` (12 files, the actual grep result).

Every transformed file was verified byte-for-byte equal to its `HEAD` (`f9a24ba`)
version modulo exactly that substitution — no proof terms, statements, or whitespace
changed. No filenames changed, no other Lib directories touched, and `Hopf/` uses of
`SecondHurewicz` were **not** globally replaced.

This is a namespace cleanup, not a mathematical redesign: `DegreeTwo` collects the
degree-two Hurewicz constructions and their supporting helpers; it is not claimed
that every helper now has ideal file/namespace granularity.

## Naming rationale

- Twin: the degree-one Hurewicz material already lives under `AlgebraicTopology.Hurewicz`
  (`Degree1.lean`, `namespace AlgebraicTopology` / `namespace Hurewicz` at lines 86–89 —
  there is no `Mathoverflow1973` wrapper on that namespace). Nesting degree-two
  constructions under `Mathoverflow1973.Hurewicz.DegreeTwo` mirrors that
  subject-namespace pattern and distinguishes them from the general
  `Hurewicz.hurewiczMap`/`hurewiczLinearEquivOfTwoLE` interface, avoiding name
  collisions.
- No existing upstream `DegreeTwo` namespace is claimed; the name is a local
  organizational choice.
- Plain `import` statements are retained: the shared dependency graph
  (`SimplexCube`/`PrismOperator` use `import Mathlib` and broad non-module
  dependencies) is not yet module-converted, and that conversion is out of scope.
- Global removal of the transitional `Mathoverflow1973` root remains future work
  (GLM-owned global wrapper).

## Interface capture (pre-rename, frozen)

The complete old public-name list was captured mechanically from a **Lib-only** Lean
environment — `import Lib.AlgebraicTopology.Hurewicz.Naturality` only, **not**
`Hopf.LibShims` — via:

```lean
import Lib.AlgebraicTopology.Hurewicz.Naturality
open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`Mathoverflow1973.SecondHurewicz).isPrefixOf name && !name.isInternal then
      logInfo m!"{name}"
```

- Source: `~/s6-notes/C16-capture-old-names.lean`; output: `~/s6-notes/C16-old-names.log`
  (597 names, exit 0).
- This list is frozen evidence and was not recaptured after the rename.
- The existing compatibility abbreviation
  `Mathoverflow1973.SecondHurewicz.SimplyConnected.hurewiczLinearEquiv` in
  `Hopf/LibShims.lean` is intentionally absent from the capture (Lib-only
  environment) and is left untouched.

## Compatibility exports

`Hopf/LibShims.lean` appends a generated block mapping each old namespace parent
`Mathoverflow1973.SecondHurewicz.<suffix>` to
`Mathoverflow1973.Hurewicz.DegreeTwo.<suffix>`, with leaf names grouped
deterministically and sorted:

- `export` blocks for parents that are genuine namespaces (root, `SimplyConnected`,
  `SimplyConnected.BasedTetrahedron`, `SimplyConnected.SubdivisionSameSide`,
  `SimplyConnected.VertexHomotopyData`, `SimplyConnected.VertexHomotopyData.mk`,
  `SimplyConnected.VerticesBased`, `SimplyConnected.vertexStraighteningData`).
- `alias` declarations for generated names under declaration parents (equation
  lemmas `eq_1`/`eq_def`/`congr_simp`, structure fields, etc.) where `export` is
  unavailable because the parent is a declaration rather than a namespace, and
  where `abbrev` cannot infer the implicit arguments. 57 such aliases. `alias`
  creates distinct declarations, so name/type preservation is not certified as
  exhaustive metadata compatibility (attributes, equation-unfolding behavior);
  the probes below verify resolution and type/`rfl` equality, and a follow-up
  `#check`-all-597-names probe verifies every frozen old name still elaborates.
- No captured public name was dropped.

## Review status

Design reviewed GO before implementation by the persistent Devin subagent in a
separate critical pass, with prior implementation role (C14/C15 receipts, C13)
explicitly disclosed — a self-review, not independent certification.

## Verification evidence

- Focused build `lake build Lib.AlgebraicTopology.Hurewicz.Naturality
  Lib.Topology.Homeomorph.DiskCube Hopf.LibShims`: the Lib targets succeeded, but the
  aggregate command ended **exit 1** because the first generated `export` block used
  `export` under declaration (non-namespace) parents — 55 `unknown namespace` errors
  (`~/s6-notes/C16-focused-build.log`). This failed initial attempt is recorded
  separately; it was a shim-syntax issue, not a mathematical failure.
- `Hopf.LibShims` retry after switching declaration-parent leaves to `alias`
  declarations: first attempt still exit 1 (`abbrev` could not infer implicit
  arguments), then **exit 0** with `alias` (`~/s6-notes/C16-libshims-build.log`
  contains both attempts; the final successful entry is the tail). One
  `linter.auxLemma` warning: the captured name `vertexStraighteningData.match_1` is an
  auto-generated matcher, preserved for completeness.
- Full build `lake build Lib Hopf.Final Solution`: exit 0
  (`~/s6-notes/C16-full-build.log`).
- Axiom audit `lake env lean Lib/AxiomAudit.lean`: exit 0, all audited
  declarations on `[propext, Classical.choice, Quot.sound]`
  (`~/s6-notes/C16-axiom-audit.log`).
- Old/new-name probe (`import Hopf.LibShims`, `Naturality`, `DiskCube`, `Solution`):
  old and new names for `mapGenLoop` and `SimplyConnected.hurewiczPi2Equiv` check at
  identical types and are `rfl`-equal; `#print axioms` for new `hurewiczPi2Equiv`,
  Naturality headlines, `DiskCube.boundary_iff`, and `mathoverflow_1973` all standard
  three axioms (source `/home/kimi/s6-notes/C16_NamesProbe.lean`, log
  `/home/kimi/s6-notes/C16-names-probe.log`).
- C16 interface supplement: provider `/home/kimi/s6-notes/C16_InterfaceCheck.lean`
  (log `C16-interface-provider.log`) and consumer
  `/home/kimi/s6-notes/C16_InterfaceConsumerCheck.lean` (log
  `C16-interface-consumer.log`), aliases over current names plus the degree-six
  equivalence — both exit 0. This supplements rather than rewrites the historical
  `C-INTERFACE_RECEIPT.md` (`37fc1de8`).
- Rename equivalence artifact: `/home/kimi/s6-notes/C16-rename-equivalence.py` +
  `C16-rename-equivalence.log` — mechanically compares all 17
  `Lib/AlgebraicTopology/Hurewicz/*.lean` files against `git show f9a24ba:` with the
  token replaced; all `MATCH`.
- Exhaustive old-name resolution probe: `/home/kimi/s6-notes/C16-old-names-probe.lean`
  + `C16-old-names-probe.log` — `#check`s all 597 frozen captured names through the
  shims; exit 0.
- Census `scripts/lib_stock_census.py --check`: PASS, 2651 ≤ baseline 2651,
  extracted-prefix list unchanged (`~/s6-notes/C16-census.log`).
- `git diff --check` clean.
- Independent review: conditional GO archived in
  `Lib/docs/C-FOLLOWUPS-INDEPENDENT-REVIEW.md`; merge conditions (retrospective
  protocol, Comparator owner disposition, untracked-file inclusion) are owner gates,
  not claimed here.
