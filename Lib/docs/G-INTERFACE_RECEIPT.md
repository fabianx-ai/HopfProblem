# Lane G — Interface receipt

**Head:** `1cc1784` (post-F0a/F0b). **Status:** ledger certified in legacy context;
module extraction seam-gated (below).

## Probe 1 — FQN resolution (legacy context), PASS

File: `/tmp/G_Probe.lean` (deleted after recording), `import Hopf.Recognition`,
36 `#check`s covering every Axis-5 ledger name — all resolve with the ledger's
signatures at head `1cc1784`. Verified output highlights:

```
Smale.homeomorphic_sixSphere_of_homotopySixSphere : ∀ (E : Type) [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace E M] [IsManifold … ∞ M] [CompactSpace M],
  Module.finrank ℝ E = 6 → M ≃ₕ Smale.SixSphere → Nonempty (M ≃ₜ Smale.SixSphere)

Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points : ∀ {E M : Type*} …
  ContMDiff … ∞ f → IsMorse E f → f p < f q → criticalPoints E f = {p, q} →
    Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E))
```

`MorseCancel.nonempty_homeomorph_of_homotopySixSphere` (the inner chain the Lib
theorem wraps) resolves **without** `[SecondCountableTopology M]` — the drop is
confirmed real, not just unused-by-proof.

## Seam gate — why no producer probe yet

The G decls' types close over `AdaptedWindows`, `Smale.ManifoldMorse.SurgeryWindows`,
`MorseCancel.nativeMorseIndex/nativeMorseCount`, `IsNativeMiddleBasinFamily`,
`middleSectionClass`, `canonicalMiddleMatrix`, `Smale.Hemisphere.*`,
`SingularMayerVietoris.SingularHomology`, and the Reeb structures
(`TwoDiskDecomposition`, `SublevelDisk`). These live in legacy (non-`module`)
files — `Hopf/SphereTopology.lean`, `Hopf/Recognition.lean`,
`Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` — which a `module` file cannot
import. A producer probe in production context therefore cannot compile until
lanes C/D1/E1/F finish module-izing the dependency cone. Per the lane DAG and
`G.md` open item 1, that is the intended order: **G lands last**.

`MorseCancel.canonicalMiddleMatrix`'s algebraic partner (`classCoordinateMatrix`,
`mul_transvection_surjective`, `primitive_row_*`) is landed in Lib via F0a; the
structure itself (Rec 3359) and the geometric family remain in Recognition.

## Extraction plan (for the landing pass)

| Module | Rows | Probe when unblocked |
|---|---|---|
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | G1, G2, G5 count theorems | producer probe: all 20 FQNs `#check` at module imports |
| `Lib/Geometry/Manifold/Morse/HandleTrade.lean` | G3 | same |
| `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` | G4, G5 pivot/cancel | same |
| `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | G6 + headline | headline signature probe minus `SecondCountableTopology`, sphere consolidated |

Consumer probe (post-landing): `Hopf.Recognition` wrapper re-proves
`Smale.homeomorphic_sixSphere_of_homotopySixSphere` verbatim (with the instance)
through the Lib theorem; `Hopf/Final.lean` statement unchanged.

## Verdict

Ledger surface certified (names + coordinates + design mutations verified);
extraction **deferred pending lanes C/D1/E1/F** — recorded here so the gate is
auditable rather than implicit.
