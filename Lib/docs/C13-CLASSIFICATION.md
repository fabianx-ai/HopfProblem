# C13 classification

Typed ledger for the C13 classification seam. Baseline `26a4708`.

- source: `Lib/docs/C.md` §15–16
- class: FREE
- visibility: plain imports, namespace `Mathoverflow1973.HigherHurewicz`
- imports: `Lib.AlgebraicTopology.Hurewicz.HopfDegree` (probe); production existing imports
- destination: `Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean`
- consumer: `Hopf/Recognition.lean` `Degree.sphere_homotopicRel_of_topClass_eq` and `Degree.Sphere.homotopic_id_of_topClass`
- commit_boundary: C13-classification
- focused_check: `lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree`
- return_seam: Axis5 for type/coercion and Axis1 for mathematical input
- independent interface review: Devin implementation agent / coordinating review Devin GO

Interface-elaboration receipt: provider
`lake env lean -o C13_ClassificationInterfaceCheck.olean C13_ClassificationInterfaceCheck.lean` exit 0;
consumer `LEAN_PATH=.:$LEAN_PATH lake env lean C13_ClassificationInterfaceConsumerCheck.lean` exit 0.
11 output signatures visible, 14 external API checks, logs at
`logs/C/C13-classification-interface-provider.log` and
`logs/C/C13-classification-interface-consumer.log`, baseline `26a4708`.

## Nodes

### 1. `hurewiczMap_eq_second`

```lean
theorem hurewiczMap_eq_second {X : Type} [TopologicalSpace X] (x : X) :
    HigherHurewicz.hurewiczMap (m := 0) x = SecondHurewicz.hurewiczMap x
```

- deps: `HigherHurewicz.hurewiczMap_representative`, `HigherHurewicz.cubeHomologyClass_eq_squareHomologyClass`, `SecondHurewicz.hurewiczMap`
- representation equations: `HigherHurewicz.cubeHomologyClass_eq_squareHomologyClass` (cube class = square class in degree 2)

### 2. `hurewiczMap_injective`

```lean
theorem hurewiczMap_injective {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) {m : ℕ} (hpi : ∀ j, 2 ≤ j → j < m + 2 → Subsingleton (π_ j X x)) :
    Function.Injective (HigherHurewicz.hurewiczMap (m := m) x)
```

- deps: `hurewiczMap_eq_second`, `SecondHurewicz.SimplyConnected.hurewiczLinearEquiv`, `HigherHurewicz.hurewiczLinearEquiv`
- representation equations: `hurewiczMap_eq_second` at `m = 0`, `LinearEquiv.injective` otherwise

### 3. `factorMap_homotopy_apply`

```lean
theorem factorMap_homotopy_apply {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) (t : unitInterval)
    (u : Fin n → unitInterval) :
    Degree.SphereCube.factorMap_homotopy hn H (t, Degree.SphereCube.quotient n u) = H (t, u)
```

- deps: `Degree.SphereCube.factorMap_homotopy`, `Degree.SphereCube.cylinder_isQuotientMap`
- representation equations: `IsQuotientMap.lift_comp` on the cylinder quotient

### 4. `factorMap_homotopyRel`

```lean
def factorMap_homotopyRel {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (Degree.SphereCube.factorMap hn p).HomotopyRel (Degree.SphereCube.factorMap hn q)
      {Degree.SphereCube.point n}
```

- deps: `factorMap_homotopy`, `factorMap_homotopy_apply`, `Degree.SphereCube.factorMap_quotient`, `Degree.SphereCube.quotient_boundary`, `Degree.SphereCube.zero_boundary`
- representation equations: `factorMap_homotopy_apply`, `factorMap_quotient`

### 5. `basedSphereCube`

```lean
def basedSphereCube {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Degree.SphereCube.Sphere n, X)) (hf : f (Degree.SphereCube.point n) = x) :
    GenLoop (Fin n) X x
```

- deps: `Degree.SphereCube.quotient`, `Degree.SphereCube.quotient_boundary`
- representation equations: `quotient_boundary`

### 6. `factorMap_basedSphereCube`

```lean
theorem factorMap_basedSphereCube {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Degree.SphereCube.Sphere n, X)) (hf : f (Degree.SphereCube.point n) = x) :
    Degree.SphereCube.factorMap hn (basedSphereCube f hf) = f
```

- deps: `Degree.SphereCube.factorMap_unique`, `basedSphereCube`
- representation equations: `factorMap_unique`

### 7. `basedSphereCube_homologyClass`

```lean
theorem basedSphereCube_homologyClass {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Degree.SphereCube.Sphere (m + 2), X))
    (hf : f (Degree.SphereCube.point (m + 2)) = x) :
    HigherHurewicz.cubeHomologyClass (basedSphereCube f hf) =
      SingularMayerVietoris.singularHomologyMap f (m + 2)
        (HigherHurewicz.cubeHomologyClass (Degree.SphereCube.quotientLoop (m + 2)))
```

- deps: `Degree.SphereCube.factor_cubeHomologyClass_cycle`, `factorMap_basedSphereCube`
- representation equations: `factor_cubeHomologyClass_cycle`, `factorMap_basedSphereCube`

### 8. `sphere_homotopicRel_of_topClass_eq`

```lean
theorem sphere_homotopicRel_of_topClass_eq {m : ℕ} {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X}
    (hpi : ∀ j, 2 ≤ j → j < m + 2 → Subsingleton (π_ j X x))
    (f g : C(Degree.SphereCube.Sphere (m + 2), X))
    (hf : f (Degree.SphereCube.point (m + 2)) = x)
    (hg : g (Degree.SphereCube.point (m + 2)) = x)
    (h : SingularMayerVietoris.singularHomologyMap f (m + 2)
          (HigherHurewicz.cubeHomologyClass (Degree.SphereCube.quotientLoop (m + 2))) =
        SingularMayerVietoris.singularHomologyMap g (m + 2)
          (HigherHurewicz.cubeHomologyClass (Degree.SphereCube.quotientLoop (m + 2)))) :
    f.HomotopicRel g {Degree.SphereCube.point (m + 2)}
```

- deps: `hurewiczMap_injective`, `HigherHurewicz.hurewiczMap_representative`, `basedSphereCube`, `basedSphereCube_homologyClass`, `factorMap_homotopyRel`, `factorMap_basedSphereCube`, `Quotient.exact`
- representation equations: `hurewiczMap_representative`, `basedSphereCube_homologyClass`, `factorMap_basedSphereCube`

### 9. `exists_basepoint_adjustment`

```lean
theorem exists_basepoint_adjustment {n : ℕ} (hn : 0 < n) {Y : Type*} [TopologicalSpace Y] {y : Y}
    (u : C(Degree.SphereCube.Sphere n, Y)) (P : Path (u (Degree.SphereCube.point n)) y) :
    ∃ v : C(Degree.SphereCube.Sphere n, Y), v (Degree.SphereCube.point n) = y ∧ u.Homotopic v
```

- deps: `HigherHurewicz.simplexCubeHomeomorph`, `simplexCubeHomeomorph_boundary_iff`, `simplexCubeHomeomorph_symm_boundary_iff`, `SecondHurewicz.SimplyConnected.extendBoundaryHomotopy`, `extendBoundaryHomotopy_bottom`, `extendBoundaryHomotopy_side`, `Degree.SphereCube.cylinder_isQuotientMap`, `quotient_eq_iff`, `quotient_surjective`, `quotient_boundary`, `zero_boundary`
- representation equations: `extendBoundaryHomotopy_bottom`, `extendBoundaryHomotopy_side`, `IsQuotientMap.lift_comp`, `quotient_boundary`

### 10. `sphere_homotopic_id_of_topClass`

```lean
theorem sphere_homotopic_id_of_topClass {m : ℕ}
    (g : C(Degree.SphereCube.Sphere (m + 2), Degree.SphereCube.Sphere (m + 2)))
    (hd : SingularMayerVietoris.singularHomologyMap g (m + 2)
          (HigherHurewicz.cubeHomologyClass (Degree.SphereCube.quotientLoop (m + 2))) =
        HigherHurewicz.cubeHomologyClass (Degree.SphereCube.quotientLoop (m + 2))) :
    g.Homotopic (ContinuousMap.id (Degree.SphereCube.Sphere (m + 2)))
```

- deps: `exists_basepoint_adjustment`, `sphere_homotopicRel_of_topClass_eq`, `sphere_pi_subsingleton_of_lt`, `SingularHomology.homotopic_homologyMap`, `SingularHomology.singularHomologyMap_id`, `EuclideanSphere.simplyConnectedSpace`, `PathConnectedSpace.somePath`
- representation equations: `homotopic_homologyMap`, `singularHomologyMap_id`

### 11. `right_inverse_is_left_inverse`

```lean
theorem right_inverse_is_left_inverse {m : ℕ} {X : Type} [TopologicalSpace X]
    (F : C(Degree.SphereCube.Sphere (m + 2), X))
    (g : C(X, Degree.SphereCube.Sphere (m + 2)))
    (hF : Function.Injective (SingularMayerVietoris.singularHomologyMap F (m + 2)))
    (hfg : (F.comp g).Homotopic (ContinuousMap.id X)) :
    (g.comp F).Homotopic (ContinuousMap.id (Degree.SphereCube.Sphere (m + 2)))
```

- deps: `sphere_homotopic_id_of_topClass`, `SingularHomology.homotopic_homologyMap`, `SingularHomology.singularHomologyMap_comp`, `ContinuousMap.Homotopic.comp`, `ContinuousMap.Homotopic.refl`
- representation equations: `homotopic_homologyMap`, `singularHomologyMap_comp`

## Production verification receipt (historical: baseline `26a4708` and later `1a31384` state, superseded by the integrated receipt below)

- production build `lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree` exit 0,
  7 seconds (epoch 1789253240 → 1789253247), log `logs/C/C13-classification-build.log`
- production check `lake env lean C13_ClassificationProductionCheck.lean` exit 0,
  3 seconds, log `logs/C/C13-classification-production.log`
- 11 exported outputs checked; four audited declarations
  (`sphere_homotopicRel_of_topClass_eq`, `sphere_homotopic_id_of_topClass`,
  `right_inverse_is_left_inverse`, `exists_basepoint_adjustment`) use
  `[propext, Classical.choice, Quot.sound]`; temporary probes removed.

## Production verification receipt — integrated head `37fc1de8`

Integrated base `37fc1de8a74a3b294a54fd9e804c82c074ae9591` (branch
`lib/C-14-integrated-receipt`). At this head the standalone `Degree.` prefix was removed;
the interface names above are now `Mathoverflow1973.SphereCube.*`,
`Mathoverflow1973.CylinderFilling.*`, `Mathoverflow1973.Hurewicz.*`, and
`Mathoverflow1973.threefoldHomotopyEquiv`. The pre-integration `Degree.`-prefixed names
above are historical.

Two adapter-body edits in `Hopf/Recognition.lean` re-pointed the existing general
instantiations to the current namespace (`HigherHurewicz.` → `Hurewicz.`):
`sphere_homotopicRel_of_topClass_eq` and `Sphere.homotopic_id_of_topClass`. No statements
changed and no proofs were deleted.

- `lake build Hopf.Recognition` — exit 0, 8,813 jobs, epoch 1789264924 → 1789265765,
  log `logs/C/C13-integrated-recognition.log`
- `lake build Hopf.Final Solution` — exit 0, 8,816 jobs, epoch 1789265777 → 1789265786,
  log `logs/C/C13-integrated-final.log`
- consumer axiom probe `lake env lean C13_IntegratedConsumerAudit.lean` (`import Solution`,
  `#print axioms` on `sphere_homotopicRel_of_topClass_eq`, `Sphere.homotopic_id_of_topClass`,
  `threefoldHomotopyEquiv`, `mathoverflow_1973`) — exit 0, all four on
  `[propext, Classical.choice, Quot.sound]`, log `logs/C/C13-integrated-consumer-axioms.log`;
  probe source preserved at `logs/C/C13-integrated-consumer-audit.lean.txt` and removed from
  the repository.
