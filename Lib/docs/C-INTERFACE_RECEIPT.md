# Lane C — aggregate production-interface receipt

## Scope and provenance

- Repository: `/home/kimi/hopf`, branch `lib/C-10-boundary`.
- Checked Lean head: `1a313843ed86eb106842fa1e2be031a5bb803eea`.
- Toolchain: `leanprover/lean4:v4.33.0`, executable directory `/tmp/shared-lean-copy/toolchain-v4.33.0/bin`.
- Ledger: the **current Axis-5 section** of `Lib/docs/C.md`.
- Ledger file SHA-256: `e7dceb65570ab09da72b86106d559f1dddb53a22e6f570ce6f8892227265d21f`.
- Boundary list: C1–C13; thirteen public output aliases; thirteen import-visible output checks.
- Representation checks: `Degree.SphereCube.Sphere n = SphereHomology.UnitSphere n` by `rfl`, and a degree-six equivalence under the four explicit lower-homotopy-group instances.

This is a retrospective check of the **implemented current interface**. It does not claim that
C10 or C13 existed at `856e4762`, nor that this newly assembled ledger was a pre-implementation
frozen Challenge. The separate C13 implementation interfaces were checked before their proofs
were written, as recorded in `C13-BOOTSTRAP.md` and `C13-CLASSIFICATION.md`.

## Provider

`C_InterfaceCheck.lean` used plain imports (its dependencies are non-module files), followed by
`noncomputable section` and an isolated namespace. Its complete output map was:

```lean
import Lib.AlgebraicTopology.Hurewicz.HopfDegree
import Lib.Topology.Homotopy.CellFilling
noncomputable section
namespace C_InterfaceCheck
abbrev C1 := @Mathoverflow1973.SingularHomology.crossProductHomology
abbrev C2 := @Mathoverflow1973.Hurewicz.CubeTriangulation.cubeSimplex
abbrev C3 := @Mathoverflow1973.Hurewicz.simplexCubeHomeomorph
abbrev C4 := @Mathoverflow1973.SecondHurewicz.SimplyConnected.extendBoundaryHomotopy
abbrev C5 := @Mathoverflow1973.SecondHurewicz.SimplyConnected.simplexPrismOperator
abbrev C6 := @Mathoverflow1973.Hurewicz.cubeChain_eq_sum_simplices
abbrev C7 := @Mathoverflow1973.Hurewicz.normalizationHomotopy
abbrev C8 := @Mathoverflow1973.Hurewicz.NativeSubdivision.nativeCubeSubdivision_class
abbrev C9 := @Mathoverflow1973.Hurewicz.CubeGluing.coherentCubeEndpoint
abbrev C10 := @Mathoverflow1973.Hurewicz.hurewiczLinearEquivOfTwoLE
abbrev C11 := @Mathoverflow1973.Degree.SphereCube.factorMap
abbrev C12 := @Mathoverflow1973.Degree.CylinderFilling.exists_filling
abbrev C13 := @Mathoverflow1973.Hurewicz.sphere_homotopicRel_of_topClass_eq
example (n : ℕ) : Mathoverflow1973.Degree.SphereCube.Sphere n =
    Mathoverflow1973.SphereHomology.UnitSphere n := rfl
end C_InterfaceCheck
```

Command (from the repository root):

```sh
PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH lake env lean -o C_InterfaceCheck.olean C_InterfaceCheck.lean
```

Exit **0**. Wall time **3 seconds**, epoch `1789261012` to `1789261015`.
Actual output: `/home/kimi/s6-notes/C-interface-provider.log`.

## Importing consumer

`C_InterfaceConsumerCheck.lean` imported `C_InterfaceCheck`, entered `noncomputable section`,
and checked `@C_InterfaceCheck.C1` through `@C_InterfaceCheck.C13` individually. It also
elaborated this consumer:

```lean
open Mathoverflow1973 Topology
example {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    Additive (π_ 6 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  C_InterfaceCheck.C10 x 6 (by decide)
    (by intro j hj hjn; interval_cases j <;> infer_instance)
```

Command:

```sh
LEAN_PATH=.:$LEAN_PATH PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH lake env lean C_InterfaceConsumerCheck.lean
```

Exit **0**. Successful run wall time **3 seconds**, epoch `1789261058` to `1789261061`.
The earlier consumer attempt omitted `noncomputable section`; it was corrected before the
successful run. Actual printed types and exit status:
`/home/kimi/s6-notes/C-interface-consumer.log`.

## Durable consumers and cleanup

- `Hopf/Hurewicz.lean` imports `Lib.AlgebraicTopology.Hurewicz.HopfDegree` and instantiates the
  general equivalence at degrees three, four, and five.
- `Hopf/Recognition.lean` uses the degree-six adapters and the general Hopf degree results.
- `Hopf/LibShims.lean` preserves the renamed public APIs for project consumers.
- `lake build Hopf.Recognition` passed after the mathematical changes and after both rename
  units. These are actual downstream import-boundary checks, not same-file `#check`s.
- Both disposable probe sources and the generated local provider `.olean` were removed.
  No temporary `axiom`, `sorry`, or challenge declaration was used in these probes.
- After cleanup the only untracked file was the requested recovered historical review,
  `Lib/docs/C-STAGE2-REVIEW.md`; there were no Lean source changes or probe artifacts.

Coordinating reviewer: **Devin**. Verdict: the thirteen implemented outputs are import-visible
with the types in the current ledger. This receipt does not certify the unimplemented optional
API wrappers or the historical prospective names retained in the superseded plan.
