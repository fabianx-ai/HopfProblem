# Lane G — Interface receipt

**Head:** `1cc1784` (post-F0a/F0b) for the recorded probes — **historical**; names and
provider locations below carry a post-integration map at `7e98c58`. **Status:**
DRAFT — historical FQN checks passed in legacy context under old names; the
probe must be re-run at the new head (stale `.olean`s still resolve pre-rename
names — fresh-subagent finding 2); module extraction seam-gated (below).

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

The historical probe checked the inner homeomorphism chain without
`[SecondCountableTopology M]`. Current source names it
`MorseCancellation.nonempty_homeomorph_of_homotopySixSphere` and retains that
instance-free signature; this source comparison is not a current-artifact probe.

*Name map after the post-integration renames (`ff89376`, `05b5d14` — see
`Lib/reports/RENAMES.md`): the probe's `Smale.` prefix is dropped
(`Smale.homeomorphic_sixSphere_of_homotopySixSphere` →
`homeomorphic_sixSphere_of_homotopySixSphere`, Rec 8020); `MorseCancel.` →
`MorseCancellation.`; Recognition's `SixSphere` → `MetricSixSphere`;
`Smale.SixSphere` → `SixSphere`; `Smale.Hemisphere` → `Hemisphere`. The fresh2
review (`Lib/docs/G-fresh2-subagent-review.md`, at `fdd2143`) confirmed all 35
current names and declaration starts but found
two G5 result types truncated at internal lets. The subsequent repair restores
Recognition:6008–6074 and 2481–2493 through their outer proof delimiters. These are
source-text repairs, not a new machine-elaboration or production certificate.*

## Seam gate — why no producer probe yet

Independently reproduced (astra finding 10): `module` + `public import
Hopf.Recognition` fails at the import with
`cannot import non-`module` Hopf.Recognition from `module``. The legacy
(non-`module`) providers the G cone needs, at post-integration head `7e98c58`:
`AdaptedWindows` (`Lib/…/Morse/SurgeryWindows.lean:1821` — the file is now 1,838
lines after the GLM split, still without a `module` header),
`MorseCancellation.nativeMorseIndex`/`nativeMorseCount`
(`Lib/…/Morse/Cancellation.lean:4987`), `IsNativeMiddleBasinFamily`,
`middleSectionClass`, `canonicalMiddleMatrix` (Rec 1952), `Hemisphere.*`, and
the Reeb structures (`TwoDiskDecomposition` ST 5199, `SublevelDisk` ST 5283) —
all in `Hopf/SphereTopology.lean`, `Hopf/Recognition.lean`, or the split legacy
files.
**Correction vs. the first receipt draft:** `SingularMayerVietoris.
SingularHomology` is already a real public module
(`Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean:853`), and
`SphereHomology.UnitSphere` is in `Lib/…/Sphere.lean` — the gate is the
*geometric* cone, not the homology layer. Per-provider inventory, not a blanket
claim: extraction waits on the D1/E1/C-side module-ization of SurgeryWindows and
the Recognition/SphereTopology Morse machinery. Per the lane DAG, **G lands
last**.

`MorseCancellation.canonicalMiddleMatrix`'s algebraic partner (`classCoordinateMatrix`,
`mul_transvection_surjective`, `primitive_row_*`) is landed in Lib via F0a; the
structure itself (Rec 1952) and the geometric family remain in Recognition.

## Extraction plan (for the landing pass)

| Module | Rows | Probe when unblocked |
|---|---|---|
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | G1, G2a | producer probe: all FQNs `#check` at module imports |
| `Lib/Geometry/Manifold/Morse/HandleTrade.lean` | G3, G2b | same (G2b consumes G3 — astra finding 8) |
| `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` | G4, G5 | same |
| `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | G6 + headline | headline signature probe minus `SecondCountableTopology`, sphere consolidated |

Consumer probe (post-landing): `Hopf.Recognition` wrapper re-proves
`homeomorphic_sixSphere_of_homotopySixSphere` verbatim (with the instance)
through the Lib theorem; `Hopf/Final.lean` statement unchanged.

## Verdict

**DRAFT / not currently certified.** Historical legacy checks, the current
source name/start census, and the repaired signature text are distinct evidence.
The current ledger still requires source-matched elaboration and aggregate
production provider/separate importing-consumer checks against its reviewed hash.
Extraction remains **deferred pending lanes C/D1/E1/F**, helper closure and those
checks; neither the historical probe nor the source-text repairs authorize Axis-6.
