# C19 — `Hopf/Hurewicz.lean` leftover classification

Branch `lib/C-19-hurewicz-leftovers`, based on upstream
`27f8e7f5fb507b947c1dd9507b3fdbc70c77e5c4`. After the proof split, `Hopf/Hurewicz.lean`
outside `Hopf/Proof/` held 16 declarations of stock. Each was classified individually:

## FREE — moved into `Lib/` (9)

| Declaration | Landed in | Why free |
|---|---|---|
| `SphereHomology.twoOpenCover_pathConnectedSpace` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | Generic: a two-open cover whose pieces are path-connected gives a path-connected space. Depends only on `TwoOpenCover` API already in the same file. |
| `SphereHomology.twoOpenCover_fundamentalGroup_eq_one` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | Generic van Kampen corollary for a two-open cover with simply connected pieces and path-connected overlap. Same dependencies. |
| `SphereHomology.suspensionConeCover` | `Lib/AlgebraicTopology/SingularHomology/SuspensionCover.lean` (new leaf) | Generic: the two-cone cover of a suspension. Needs VanKampen + suspension lemmas; placed in its own non-`module` leaf because `VanKampen.lean` is not yet a `module`, so `module` files cannot import it. |
| `ThirdHurewicz.hurewiczLinearEquiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Thin degree-3 specialization of the general `Hurewicz.hurewiczLinearEquiv` (`m = 0`). |
| `ThirdHurewicz.hurewiczPi3Equiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Multiplicative repackaging of the above; generic. |
| `FourthHurewicz.hurewiczLinearEquiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Degree-4 specialization (`m = 1`). |
| `FourthHurewicz.hurewiczPi4Equiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Multiplicative repackaging; generic. |
| `FifthHurewicz.hurewiczLinearEquiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Degree-5 specialization (`m = 2`). |
| `FifthHurewicz.hurewiczPi5Equiv` | `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | Multiplicative repackaging; generic. |

`Lib.lean` gains the `SuspensionCover` import; `Hopf/Hurewicz.lean` imports the new leaf
and the destination modules so every old reference still resolves. Statements and
proofs are unchanged apart from the necessary import/namespace placement.

## CHARGED — stays in `Hopf/Hurewicz.lean` (7)

| Declaration | Why charged |
|---|---|
| `SixSphereCube.StandardSphere` | Abbrev for `SphereHomology.UnitSphere 6` — the pinned six-sphere of the project; `SixSphereCube` is project vocabulary (see `Hopf/SphereTopology.lean`). |
| `SixSphereCube.euclideanOnePointSphereHomeomorph` | The specific `OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere` chart used by the project construction. |
| `SixSphereCube.sphereBasePoint` | The project's chosen basepoint (image of `OnePoint.infty`). |
| `Sphere.piTwo_subsingleton` | Charged specialization: π₂ of *the* six-sphere vanishes (degree and sphere both pinned). |
| `Sphere.piThree_subsingleton` | Same, π₃. |
| `Sphere.piFour_subsingleton` | Same, π₄. |
| `Sphere.piFive_subsingleton` | Same, π₅. |

The four `Sphere.piN_subsingleton` theorems are one-line instances of the general
`HigherHurewicz.sphere_pi_subsingleton_of_lt` at the project's six-sphere — generic in
proof but charged in declaration (project-named sphere, project basepoint, `Sphere`
namespace used by project consumers). They are not moved merely to reduce the count.

## Receipts

All under `Lib/docs/logs/C/`:

- `C19_InterfaceCheck.lean.txt` / `C19_InterfaceConsumerCheck.lean.txt`: pre-move
  provider + consumer probes (`C19-interface-pre-*.log`, exit 0).
- Same probe sources post-move (`C19-interface-post-*.log`, exit 0) — all 16 names
  still resolve through `import Hopf.Hurewicz`.
- `C19_AxiomProbe.lean.txt` / `C19-axiom-probe.log`: `#print axioms` for the 9 moved
  declarations — only `propext`, `Classical.choice`, `Quot.sound`.
- `C19-lib-build.log`: `lake build Lib` after the move.
- Probe sources are stored as `.lean.txt`: the stock-census import guard scans every
  `.lean` file under `Lib/` and evidence sources import `Hopf.*`, so they must not be
  `.lean` files in the Lib tree.

## Notes

- First attempt put all three cover declarations in `SphereHomology.lean` behind a new
  `module` boundary; Lean rejected the non-`module` `VanKampen` import. The two pure
  two-open-cover lemmas went to `VanKampen.lean` instead and the suspension cover got
  its own leaf. Recorded here so the placement rationale survives.
- Census: ratchet PASS, `1639 <= 1648` (nine declarations left `Hopf/`).
