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

Independently reproduced (astra finding 10): `module` + `public import
Hopf.Recognition` fails at the import with
`cannot import non-`module` Hopf.Recognition from `module``. The legacy
(non-`module`) providers the G cone needs are: `AdaptedWindows` and
`nativeMorseIndex`/`nativeMorseCount` (legacy `Lib/…/SurgeryWindows.lean`,
owning them at ~1804/~6741), `IsNativeMiddleBasinFamily`, `middleSectionClass`,
`canonicalMiddleMatrix`, `Smale.Hemisphere.*`, and the Reeb structures
(`TwoDiskDecomposition` ST 5199, `SublevelDisk` ST 5283) — all in
`Hopf/SphereTopology.lean`, `Hopf/Recognition.lean`, or legacy SurgeryWindows.
**Correction vs. the first receipt draft:** `SingularMayerVietoris.
SingularHomology` is already a real public module
(`Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean:853`), and
`SphereHomology.UnitSphere` is in `Lib/…/Sphere.lean` — the gate is the
*geometric* cone, not the homology layer. Per-provider inventory, not a blanket
claim: extraction waits on the D1/E1/C-side module-ization of SurgeryWindows and
the Recognition/SphereTopology Morse machinery. Per the lane DAG, **G lands
last**.

`MorseCancel.canonicalMiddleMatrix`'s algebraic partner (`classCoordinateMatrix`,
`mul_transvection_surjective`, `primitive_row_*`) is landed in Lib via F0a; the
structure itself (Rec 3359) and the geometric family remain in Recognition.

## Extraction plan (for the landing pass)

| Module | Rows | Probe when unblocked |
|---|---|---|
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | G1, G2a | producer probe: all FQNs `#check` at module imports |
| `Lib/Geometry/Manifold/Morse/HandleTrade.lean` | G3, G2b | same (G2b consumes G3 — astra finding 8) |
| `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` | G4, G5 | same |
| `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | G6 + headline | headline signature probe minus `SecondCountableTopology`, sphere consolidated |

Consumer probe (post-landing): `Hopf.Recognition` wrapper re-proves
`Smale.homeomorphic_sixSphere_of_homotopySixSphere` verbatim (with the instance)
through the Lib theorem; `Hopf/Final.lean` statement unchanged.

## Verdict

Ledger surface certified (names + coordinates + design mutations verified);
extraction **deferred pending lanes C/D1/E1/F** — recorded here so the gate is
auditable rather than implicit.
