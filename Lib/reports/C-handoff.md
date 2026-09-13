# C10 handoff — `hurewiczLinearEquiv` at general `n`

**Branch:** `lib/C-10-boundary` (not pushed). **HEAD:** `63ef708`.
**Toolchain:** `leanprover/lean4:v4.33.0`. Gate used throughout: `lake build Lib.AlgebraicTopology.Hurewicz.CubeSphere`.
**Do not push.** Attribution is the owner's.

This is the remaining work on lane C's headline. Everything below is grounded in the current tree.

## Status

| Piece | State | Where |
|---|---|---|
| Additivity of `cubeHomologyClass` under `transAt`, all `n ≥ 2` | landed | `CubeSphere.lean` `cubeHomologyClass_transAt_zero` / `cubeHomologyClass_transAt` |
| `hurewiczPi` / `hurewiczMap` (`ℤ`-linear) | landed | `CubeSphere.lean`; degree `m+2` |
| `hurewiczInverse` | landed | `Straightening.lean`; degree `m+3` (`n ≥ 3`) |
| `hurewiczMap ∘ hurewiczInverse = id` | landed | `CubeSphere.lean` `hurewiczMap_comp_hurewiczInverse` |
| `classOperator (cubeChain p)` as signed Kuhn sum | landed | `CubeSphere.lean` `classOperator_cubeChain_sum` |
| `hurewiczInverse ∘ hurewiczMap = id` | **not landed** | degree-3 template in `Hopf/Hurewicz.lean` ~6679–6779 |
| `hurewiczLinearEquiv` | **not landed** | degree-2 model: `PrismOperator.lean` `SecondHurewicz.SimplyConnected.hurewiczLinearEquiv` |

C11 (CubeSphere module) and C12 (CellFilling) are already landed. C13 (HopfDegree) stays blocked on the headline.

`Lib/reports/C.md` open item 1 is stale on additivity (that is done as of `9afe2e4`). This file supersedes that paragraph.

## Indexing (easy to get wrong)

- `hurewiczMap (m := m)`: `Additive (π_(m+2)) →ₗ H_{m+2}`. So `n ≥ 2`.
- `hurewiczInverse x hpi` with `hpi : ∀ j, 2 ≤ j → j < m+3 → Subsingleton (π_j)`: `H_{m+3} →ₗ Additive (π_(m+3))`. So `n ≥ 3`.
- Round trip `map ∘ inverse` therefore uses `hurewiczMap (m := m+1)` against `hurewiczInverse x hpi`.
- `NormalizationState x k` has `aug` on `k`-simplices and `nxt` on `(k+1)`-simplices. `normalizationTower x m` is a state at level `m+2`. `normalizationHomotopy x (m+3) hpi` **is** `(normalizationTower x m …).nxt` (definitional).

Degree 2 already has a full `LinearEquiv` (`SecondHurewicz.SimplyConnected.hurewiczLinearEquiv`). The missing general statement is `n ≥ 3`. A wrapper that cases on `n = 2` vs `n ≥ 3` is fine for the public `hurewiczLinearEquiv`.

## What to write next (in order)

Copy `ThirdHurewicz` ~6679–6779 in `Hopf/Hurewicz.lean`. Names there → Lib names:

| Hopf (n = 3) | Lib |
|---|---|
| `normalizationTriangleHomotopy` | `S.aug` or `normalizationHomotopy x (m+2) …` |
| `normalizationThreeSimplexHomotopy` | `S.nxt` = `normalizationHomotopy x (m+3) hpi` |
| `normalizationHomotopy_face` | `S.compat` |
| `normalizationTriangleHomotopy_const` | **missing** — `hconst` on `S.aug` |
| `normalizationThreeSimplexHomotopy_zero` | `S.nxt_zero` |
| `normalizationThreeSimplexHomotopy_endpoint` | `normalizedSimplex` def (`timeSlice _ 1`) |
| `Geometry.cubeTetrahedron` | `CubeTriangulation.cubeSimplex` |
| `nativeCubeSubdivision_homotopy_class` | **only in Hopf** (Fin 3). Rebuild from Lib `nativeClass_homotopic` + `nativeCubeSubdivision_class` |
| `threeSimplexClassOperator_cubeChain` | `classOperator_cubeChain` (the missing identity) |

Concrete lemmas, all in `CubeSphere.lean` (already imports `Straightening`):

1. **`hconst` for the tower `aug` family.**
   `coherentCubeEndpoint` (`CubeGluing.lean` ~1365) requires
   ```
   H₀ (const (Simplex n) x) = const (I × Simplex n) x
   ```
   `S.aug_one` is only `timeSlice (aug smp) 1 = const x` (t = 1, every smp), not the whole homotopy of the constant simplex.
   Tools already landed:
   - `ThirdHurewicz.composeSimplexHomotopies_const` (`PrismOperator.lean` ~4591)
   - `simplexStraighteningHomotopy_const` (`Degree.lean` ~147)
   - `extendCoherentSimplexHomotopy_const` (`PrismOperator.lean` ~4662)
   - `vertexStraighteningHomotopy_const`, `edgeStraighteningHomotopy_const`
   `S.aug` is `composeSimplexHomotopies` of the previous `nxt` with a straightening (see `normalizationStep` / `normalizationBaseTwo` in `Straightening.lean`). Prove `S.aug (const x) = const` by induction on the tower, using `composeSimplexHomotopies_const`. `vertexEdgeHomotopy_const` is **not** in the tree yet (compose of vertex-straightening const and `edgeTower.low` const).

2. **`normalizedCube`.**
   ```
   S := normalizationTower x m (fun j hj hj' => hpi j hj (by omega))
   coherentCubeEndpoint S.aug S.nxt S.compat hconst p
   ```
   Cube dimension is `m+3` so the `coherentCubeEndpoint` parameter `n` is `m+2`.
   Homotopy: `coherentCubeHomotopy S.aug S.nxt S.compat hconst S.nxt_zero p`.
   Internal basedness: `coherentCubeEndpoint_internalBased` (`Degree.lean` ~527) plus `S.aug_one` as `hone`.

3. **Cell identity.**
   `coherentCubeEndpoint_cell` gives
   `(endpoint p).val.comp (cubeSimplex e) = timeSlice (S.nxt (p.comp cubeSimplex e)) 1`.
   That is `normalizedSimplex x (m+3) hpi (p.comp cubeSimplex e)` on `val`.
   Then `Subtype.ext` against `nativeBasedCubeSimplex (endpoint p) hp e`.

4. **Close `classOperator_cubeChain`.**
   `classOperator_cubeChain_sum` is already the LHS.
   RHS of `nativeCubeSubdivision_class` (`Subdivision.lean` ~2195) on the endpoint, after the cell identity, is the same sum.
   Homotopy `p ~ endpoint` + `nativeClass_homotopic` (`Subdivision.lean` ~552) gives `⟦p⟧`.
   There is no Lib `nativeCubeSubdivision_homotopy_class`; it is three lines:
   `nativeClass_homotopic ⟨H⟩` then `nativeCubeSubdivision_class q hq`.

5. **`hurewiczInverse_hurewiczMap_mk`.** Degree-3 is literally
   ```
   rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
   exact classOperator_cubeChain x hpi p
   ```
   Then `Quotient.inductionOn` for all of `Additive (π_n)`, then `.comp = LinearMap.id`.

6. **`hurewiczLinearEquiv`.**
   `LinearEquiv.ofLinearMap hurewiczMap hurewiczInverse map_comp_inv inv_comp_map`
   (`PrismOperator.lean` ~4460 is the n=2 copy). Need `[SimplyConnectedSpace X]` and `hpi` at `n ≥ 3`.

## Pitfalls already paid for

- Boundary-plumbing: do **not** `rw` into composed tower expressions in place (`isDefEq` timeout). Named intermediates only. Same note as `Lib/reports/C.md`.
- `LinearMap.comp_apply` vs `∘ₗ`: after `LinearMap.congr_fun hcomp c.1`, `simp only [LinearMap.comp_apply] at h` before `rw [h]`.
- `hurewiczMap (m := m)` vs inverse at `m+3`: always `hurewiczMap (m := m+1)` next to `hurewiczInverse x hpi`.
- `cubeHomologyClass_const` already exists in `CubeChainDecomposition.lean` (~2058). Do not redeclare in `CubeSphere`.
- `ThirdHurewicz.composeSimplexHomotopies_const` already exists in `PrismOperator.lean`. Do not redeclare.
- `CubeSphere.lean` must keep `import Lib.Topology.OnePointCollapse` (used at the top of the file). It now also imports `Straightening`.
- `add_comm` under `Multiplicative.ofAdd` can produce a motive that depends on the degree; rewrite `transAt_zero` first, then `exact add_comm _ _`.
- Extra term for additivity: killed in homology as `k • const_simplex` via support of `d(fund)` on `Cube.boundary` (`fundamentalCubeChain_boundary_supported`, `cubeChain_transAt_zero_extra_eq_smul`, `cubeChain_transAt_zero_extra_boundary`). Do not reopen that seam.

## Suggested first command

```
export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
lake build Lib.AlgebraicTopology.Hurewicz.CubeSphere
```

Then prove `NormalizationState.aug (const x) = const` (or `normalizationHomotopy` at degree `m+2` on `const`), and only then instantiate `coherentCubeEndpoint`.
