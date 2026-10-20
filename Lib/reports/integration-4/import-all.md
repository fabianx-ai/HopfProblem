# NEXT_STEPS item 10: `import all` drops (receipt)

Branch `lib/next-importall`, worktree `hopf-wt-importall`, 2026-09-14.
Skipped by instruction: `Lib/Geometry/Manifold/Morse/Cancellation.lean` (being split by another seat).

## Mechanism

Mathlib's `IsLocalDiffeomorphAt` (a `def`, not `@[expose]`d), `Diffeomorph.toPartialDiffeomorph`
and `IsLocalDiffeomorph.diffeomorphOfBijective` cannot be unfolded by module-mode importers: no
anonymous constructor, `rcases`, `change` or `rfl` through them (`backward.isDefEq.respectTransparency`
does not help; verified in a `module`-headed scratch file, which does respect publicity under
`lake env lean`, unlike a script file).

New module `Lib/Geometry/Manifold/LocalDiffeomorph.lean` (commit 23b8c97f), public API only:

| helper | role | built from |
|---|---|---|
| `IsLocalDiffeomorphAt.of_eqOn φ hx h` | constructor | re-packed `PartialDiffeomorph` with `toFun := f`, `PartialDiffeomorph.isLocalDiffeomorphAt` |
| `IsLocalDiffeomorphAt.exists_partialDiffeomorph hf` | destructor | `localInverse.symm`, `localInverse_mem_target`, `localInverse_right_inv` |
| `Diffeomorph.toPartialDiffeomorphUniv` | transparent `toPartialDiffeomorph` | explicit `PartialEquiv` literal |
| `IsLocalDiffeomorph.diffeomorphOfBijective'` | transparent `diffeomorphOfBijective` | `Equiv.ofBijective` |

The last two duplicate `Transversality/Basic`'s `toPartialDiffeomorph'`/`diffeomorph'`, which the
files below Basic in the import graph (Collar, RegularLevel, WhitneyEmbedding, Flow/Compact,
SmoothFlow, MorseLemma) cannot import (Basic imports Collar/RegularLevel/WhitneyEmbedding).
Basic was not edited; its two primed definitions can later be replaced by these (one-line
redirects, not done here: outside the edit permission).

## Per file

| file | status | routed definitions | proof steps changed | build |
|---|---|---|---|---|
| `Geometry/Manifold/Collar.lean` | done (4839412f) | `IsLocalDiffeomorphAt`, `diffeomorphOfBijective` | `isLocalDiffeomorphAt_normalDisplacement_zero` (obtain → `exists_partialDiffeomorph`, refine ⟨⟩ → `of_eqOn`), `isOpen_regularNormalLocus` (rintro ⟨⟩ → destructor, witness → `of_eqOn`), `normalDisplacement_locally_injective_zero`, `contMDiffAt_normalNeighborhood_inverse` (obtain → destructor), `hWloc` in the disk tubular neighbourhood proof (⟨Φ,_,rfl⟩ → `Φ.isLocalDiffeomorphAt`), def `SmallPerturbation.diffeomorphIdAdd` (→ `diffeomorphOfBijective'`, restoring the `rfl` in `bumpTranslation_apply` and the bump-translation existence lemma) | module green |
| `Geometry/Manifold/Flow/Compact.lean` | done (e59d9dc7) | `IsLocalDiffeomorphAt` | `isLocalDiffeomorphAt_of_contMDiffOn` line 639: refine ⟨c.trans d, ⟨hc, hd⟩, ?_⟩ → `of_eqOn` | module green |
| `Geometry/Manifold/Morse/Rearrangement.lean` | done (4aa8ab0a) | `Diffeomorph.toPartialDiffeomorph` → Basic's `toPartialDiffeomorph'`; `IsLocalDiffeomorphAt` → `of_eqOn`; `diffeomorphOfBijective` → Basic's `diffeomorph'` | def `MorseCancellation.linearTransverseChart` (line 73), `Ψ` in the four-dimensional window proof (line 222), `RegularHeightCoordinates.heightMap_localDiffeomorph` (constructor), def `RegularHeightCoordinates.longitudinalDiffeomorph` | module green |
| `Geometry/Manifold/WhitneyEmbedding.lean` | done (41cd84b5) | `IsLocalDiffeomorphAt` | three `isLocalDiffeomorphAt_*` lemmas (⟨⟩ → `of_eqOn`), `exists_partialDiffeomorph_of_isLocalDiffeomorphAt` (→ destructor), `exists_partialDiffeomorph_near_compact` (locus openness and local injectivity: destructor + `of_eqOn`) | module green |
| `Geometry/Manifold/RegularLevel.lean` | not done (reverted) | — | obstruction: lines 90–100 (`ImplicitFunctionData.prodFun`, `HasStrictFDerivAt.implicitFunctionDataOfComplemented` of `Mathlib.Analysis.Calculus.Implicit` are non-exposed: `apply ContDiffOn.prodMk`, `isInvertible_fderiv_prodFun` at `φ.pt` vs `x`, `rfl` for `(φ.prodFun y).1 = f y`, `change` to `(f x, Classical.choose hk (x - x))`); line 137 `mem_univ` for `Diffeomorph.toPartialDiffeomorph` source (→ `toPartialDiffeomorphUniv` would fix this one). Needs a Lib-side implicit-function datum built from `ImplicitFunctionData.mk` with transparent `prodFun`; out of this budget. | untouched |
| `Analysis/ODE/SmoothFlow.lean` | not done (reverted) | — | obstruction: lines 1006, 1021, 1034: `Diffeomorph.toPartialDiffeomorph` source/target `mem_univ` and a `change` through `(Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).symm`; fix is to switch these to `toPartialDiffeomorphUniv` (definitions `nativeFlowTimeDiffeomorph`-based charts) — mechanical but not attempted in the budget. | untouched |
| `Analysis/Calculus/MorseLemma.lean` | not done (reverted) | — | obstruction: lines 2014, 2019, 2026 (`change`/`rfl` through `e.toPartialDiffeomorph`: `x ∈ e.source ∧ e x ∈ univ`, `C (e a) = 0`), 2185 (`mem_univ` for `c.chart.toPartialDiffeomorph` source), 2193/2204/2214 (`change` through `c.splitChart`, defined via `toPartialDiffeomorph`). Fix is `toPartialDiffeomorphUniv` in the defs of `splitChart` and the chart in question; every downstream module rebuilds (root of the chain), not attempted in the budget. | untouched |

No statement changed in any converted file. No `import all` added anywhere; remaining
`import all` lines: RegularLevel (2), SmoothFlow, MorseLemma, Morse/Cancellation.

## Build

`lake build Lib.Geometry.Manifold.{LocalDiffeomorph,Flow.Compact,WhitneyEmbedding,Collar,Morse.Rearrangement}`:
green (8741 jobs, 0 errors, 0 warnings). Full chain `lake build Lib && lake build Solution S6Shortcuts S6 Challenge`:
see the final line of this file.

Full chain result (at the state of commit 4aa8ab0a): `lake build Lib` green and
`lake build Solution S6Shortcuts S6 Challenge` green, 8857 jobs, two `Build completed successfully`
lines, 0 `error:`.
