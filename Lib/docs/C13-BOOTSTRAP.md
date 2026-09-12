# C13 bootstrap — typed boundary

Canonical source: `Lib/docs/C.md`, §15, the bootstrap induction paragraph. The complete Hurewicz equivalence is proved before this induction: at each degree k, the lower homotopy groups are supplied by strong induction and the target homology group vanishes. This is not an induction on the proof of the Hurewicz theorem itself.

Repository baseline: `0a3b870`, branch `lib/C-10-boundary`. Both nodes are FREE. Ordered outputs: C13.1, C13.2. Intended consumer: the general Hopf degree theorem and the existing `Degree.Sphere.piTwo_subsingleton` through `piFive_subsingleton` adapters.

## C13.1

```text
ChallengeNode
  id: C13.1
  source: Lib/docs/C.md §15, bootstrap induction
  class: FREE
  visibility: plain imports, namespace Mathoverflow1973.HigherHurewicz; declarations publicly importable
  imports: Lib.AlgebraicTopology.Hurewicz.CubeSphere
  dependencies: HigherHurewicz.hurewiczLinearEquivOfTwoLE, Nat.strong_induction_on, Function.Injective.subsingleton
  representation: Additive.ofMul and Additive.toMul preserve the underlying type; Fin.nontrivial_iff_two_le supplies the additive homotopy-group instance
  destination: Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean, Mathoverflow1973.HigherHurewicz.pi_subsingleton_of_homology_vanishing
  consumer: C13.2
  commit_boundary: C13-bootstrap
  focused_check: lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree
  return_seam: Axis 5 for elaboration; Axis 1 if strong induction fails to supply a mathematical input
```

```lean
theorem pi_subsingleton_of_homology_vanishing {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hH : ∀ k, 2 ≤ k → k < n → Subsingleton (SingularMayerVietoris.SingularHomology X k))
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) : Subsingleton (π_ k X x)
```

## C13.2

```text
ChallengeNode
  id: C13.2
  source: Lib/docs/C.md §15, sphere specialization of the bootstrap
  class: FREE
  visibility: plain imports, namespace Mathoverflow1973.HigherHurewicz; declarations publicly importable
  imports: Lib.AlgebraicTopology.Hurewicz.CubeSphere, Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere, Lib.AlgebraicTopology.SingularHomology.SphereHomology
  dependencies: C13.1, EuclideanSphere.simplyConnectedSpace, SphereHomology.unitSphere_homology_subsingleton
  representation: Degree.SphereCube.Sphere n = SphereHomology.UnitSphere n by rfl; n is at least 3 under the supplied hypotheses
  destination: Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean, Mathoverflow1973.HigherHurewicz.sphere_pi_subsingleton_of_lt
  consumer: general Hopf degree theorem; Degree.Sphere.piTwo_subsingleton through piFive_subsingleton
  commit_boundary: C13-bootstrap
  focused_check: lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree
  return_seam: Axis 5 for sphere-model/index conversion
```

```lean
theorem sphere_pi_subsingleton_of_lt (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (x : Degree.SphereCube.Sphere n) : Subsingleton (π_ k (Degree.SphereCube.Sphere n) x)
```

## Interface and independent review

The provider and importing consumer compiled at `0a3b870` using Lean v4.33.0:

```
PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH lake env lean -o C13_InterfaceCheck.olean C13_InterfaceCheck.lean
LEAN_PATH=.:$LEAN_PATH PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH lake env lean C13_InterfaceConsumerCheck.lean
```

Both exit statuses were 0. Two planned output signatures, four existing API checks, and the sphere-model definitional equality elaborated. Both outputs were visible to the separate consumer. Evidence: `/home/kimi/s6-notes/C13-interface-provider.log` and `C13-interface-consumer.log`.

Independent interface reviewer: Devin implementation agent; coordinating review: Devin. Verdict: GO for the two signatures with plain-import visibility. A `module`/`public import` header cannot yet be used: the imported legacy modules are non-module files. The final successful probes use exactly the plain-import context specified above. No mathematical hypothesis was changed. The temporary axioms used to elaborate signatures are not production declarations and must be removed before committing this boundary.
