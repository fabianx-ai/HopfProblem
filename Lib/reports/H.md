/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane H report — complex analysis (Ahlfors Ch. 6, Rudin 14.8)

**Status: all movable H baselines landed (8 Lib files, ~470 declarations, green), module
docstrings installed, axiom receipts exact. Per-decl docstrings: complete — verified
2026-09-13 (GLM seat): 0 of the 483 declarations across the eight H Lib files lack a
docstring.**

## What moved (source on 721fc82, cut BY NAME out of the SpecialPeriods project namespace)

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/Instances/RiemannSphere.lean` | PeriodConstruction RiemannSphere 8012–8082 + TwoAffineCharts 7758–8011 | 37 | (H baseline) |
| `Lib/Analysis/Complex/Mobius.lean` | AnalyticFillings RiemannSphere.* 3581–4019 | 54 | (H baseline) |
| `Lib/Analysis/Complex/SchwarzReflection.lean` | AnalyticFillings SchwarzReflection.* | 16 | (H baseline) |
| `Lib/Analysis/Complex/RiemannMapping.lean` | AnalyticFillings RiemannMapping.* + TriangleRiemannNormalization.* + RiemannBoundary.* | 181 | (H baseline) |
| `Lib/Analysis/Complex/RiemannMapping/Steps.lean` | AnalyticFillings _root_.* steps 4711–5413 | 31 | (H baseline) |
| `Lib/Analysis/Complex/Cousin.lean` | PeriodConstruction HolomorphicCousin.* 15593–17278 | 95 | (H baseline) |
| `Lib/Analysis/Complex/SquareRoot.lean` | PeriodConstruction AnalyticRootCover(+Continuation) + 1 SpecialPeriods step | 62 | (H baseline) |
| `Lib/Geometry/Manifold/Complex/Biholomorph.lean` | AnalyticFillings TriangleUniformizationGluing.{3 lemmas + supports} | 8 | (H baseline) |

Commit: 685fd91 (baselines), then docstring commit.

**File-scope notes.** (1) `BoundaryExtension.lean` merges into `RiemannMapping.lean`:
`RiemannBoundary` and `RiemannMapping` interleave-depend (46 qualified references one way,
3 the other) — lane-A MayerVietoris precedent. (2) `TwoAffineCharts` pulled forward from
lane I to unblock the `RiemannSphere` atlas (27 decls, Mathlib-only deps). (3)
`DBar.lean` folds into `Cousin.lean` (the Cauchy–Green ∂̄ machinery is the Cousin proof).
(4) `SpecialPeriods.exists_analytic_unit_root` moved with its SquareRoot consumers, prefix
kept (deviation — the SpecialPeriods namespace is otherwise project code).

## H honest obstruction

The `RiemannMapping` **triangle tail** (114 decls: `triangleDomain`, `triangleMap`,
normalization/Ford-cycle machinery) is project code per the plan's STOP-at-5579 note (seed
closure on `SpecialPeriods`/`triangle*`). Post-split disposition (2026-09-13): the 114
declarations live under `Hopf/Proof/LCP/AnalyticFillings.lean` (demoted proof-side by
`20f69036`; not census-counted), so the owner's done-last rule applies — each needs a
generalisation before it can move, which is not a pure move. Verified this session: no
`RiemannMapping.*` stock declaration remains under `Hopf/` outside `Hopf/Proof/` (the
census's RiemannMapping 114 figure predates the split).

## H axiom receipts

- `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`:
  `[propext, Classical.choice, Quot.sound]`
- `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution`:
  `[propext, Classical.choice, Quot.sound]`
- `AnalyticRootCover.exists_analytic_square_root` (+ `_ball`): `[propext, Classical.choice, Quot.sound]`
  (the plan's `..._on_of_even_zeros` spelling does not exist in the source; the two actual
  root-existence theorems are probed)

## H open items

Per-declaration docstrings; import minimization; the Q6 upstream Mathlib PR for the two
duplicated steps; comparator `landrun`.

---


---

# Q6 resolution (session 4): upstream PR draft

Facts at the pin (Mathlib db584cd): `Mathlib/Analysis/Complex/RiemannMapping.lean`
contains `Complex.exists_injective_not_dense_image_deriv_ne_zero` and
`Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` — statement-identical to our
`RiemannMapping/Steps.lean` copies — but the module is a **private module** in the
built artifacts (`RiemannMapping.olean.private`; module docstring: partial results
towards the Riemann mapping theorem, "all lemmas strictly weaker than the final
theorem, so they're private", complete proof upstream at mathlib4 PR #33505).
The two lemmas are therefore unavailable downstream, and our copies stay (Q6
default). We also import `Mathlib.Analysis.Complex.RiemannMapping` explicitly in
`Steps.lean`'s neighborhood? — no: with the module private, downstream import is
pointless; Steps.lean keeps `import Mathlib` only.

## Mathlib PR draft (branch not pushed)

**Title:** `feat(Analysis/Complex): expose the two RiemannMapping partial-result
lemmas for downstream use`

**Description:**

> `Mathlib/Analysis/Complex/RiemannMapping.lean` carries partial results towards
> the Riemann mapping theorem with the module docstring noting they will remain
> private until the full theorem (upstream PR #33505) lands. The module is
> nevertheless built as a private module, which makes even a *public, correct and
> independently useful* API inaccessible to downstream projects:
>
> - `Complex.exists_injective_not_dense_image_deriv_ne_zero`
> - `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero`
>
> We (the Hopf-fibration formalization) needed exactly these two statements for
> a reusable library extraction of the level-cylinder construction and had to
> duplicate them (statement-identical, with attribution) — see
> `Lib/Analysis/Complex/RiemannMapping/Steps.lean` in
> github.com/fabianx-ai/HopfProblem, branch `lib/textbook-extraction`.
>
> This PR removes the two lemmas from the private-module list (or splits them
> into a public module `Mathlib/Analysis/Complex/RiemannMapping/Partial.lean`),
> so downstream work can cite them instead of duplicating. No statement changes;
> no proof changes. The module docstring's privacy rationale is unaffected for
> the remaining lemmas.

**Steps taken here:** attempted delete-and-re-route first; failed because the
private-module build hides the lemmas from downstream elaboration (verified by
`#check` against `import Mathlib.Analysis.Complex.RiemannMapping`). Copies
restored; Lib builds green.

---

