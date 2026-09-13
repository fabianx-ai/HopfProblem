# C14 — naturality of the Hurewicz equivalence and positive-degree vanishing

Typed ledger for the C14 follow-up: generalizing the degree-six naturality chain of
`Hopf/Recognition.lean` (`SixthHurewicz.*`) to every degree in `Lib/`, plus the
positive-degree homology-vanishing corollary. Integrated base `2550436`, branch
`lib/C-14-integrated-receipt`.

- source: `Lib/docs/C.md` §11 (the Hurewicz homomorphism) and §14 (vanishing below
  degree `n`); Hatcher Thm. 4.32 and Thm. 2A.1 as already cited in `Lib/docs/C.md`.
  No new textbook checking is claimed; the references are the ones already verified
  in the ledger.
- provenance: `Lib/AlgebraicTopology/Hurewicz/Naturality.lean` generalizes the
  degree-six `SixthHurewicz.*` naturality development of `Hopf/Recognition.lean`
  (lines 150–267 at base `2550436`). The proofs are adapted, not verbatim: the degree
  is generalized, the multiplication coordinate becomes a `Classical.choice` of the
  `Nonempty (Fin n)` instance instead of `(0 : Fin 6)`, `cubeChain_natural` uses a
  `change`-to-`inducedChain` proof, and the equivalence naturality takes explicit
  `hX`/`hY` hypotheses. Generalization executed by Devin.
- destination: new `Lib/AlgebraicTopology/Hurewicz/Naturality.lean`
  (plain imports of `HopfDegree` and `Degree1`; the legacy graph does not yet support
  the module system).
- consumer: `Hopf/Recognition.lean` `SixthHurewicz.homotopyMap` and the six naturality
  lemmas became adapters; all `Hopf` statements unchanged.
- review: the lead-authored design was reviewed (GO) by a Devin sub-agent pass over
  sources at `2550436` **before** implementation. Disclosure: the same sub-agent had
  earlier implemented the C-interface receipt and C13 adapter records; the review was
  a separate critical pass over the design, not independent human/model
  certification. **No compiled interface probe was run before implementation** — the
  pre-implementation evidence is the design review only; the provider/consumer
  interface probes below were run after implementation, at the working-tree state on
  top of base `2550436`. Future pipeline phases must produce the compiled interface
  receipt before implementation.

## Mathematical content

Naturality: for `f : C(X, Y)`, postcomposition on representative based cubes is
functorial on the chain level (`inducedChain_comp`), hence on cycles and homology
classes (`mapCycles_val`, `homologyMap_cycleClass`), hence descends through the
homotopy quotient to `hurewiczFunction`/`hurewiczMap` and to the linear equivalence
`hurewiczLinearEquiv`/`hurewiczLinearEquivOfTwoLE`. The inverse inherits naturality
automatically from the forward map.

Vanishing (C.md §14, Hatcher Thm. 4.32): for simply connected `X` with
`Subsingleton (π_ j X x)` for `2 ≤ j < n`, `Subsingleton (SingularHomology X k)` for
`0 < k < n`. For `2 ≤ k` this is transport across `hurewiczLinearEquivOfTwoLE`; for
`k = 1` it is the degree-one Hurewicz theorem — abelianization of the trivial
fundamental group (Hatcher Thm. 2A.1) — realized through
`AlgebraicTopology.Hurewicz.loopHomologyClass_surjective` with every loop homotopic
to `refl`. The `k = 1` bridge `AlgebraicTopology.SingularH1 X =
SingularMayerVietoris.SingularHomology X 1` is `rfl` (both unfold to the same
`singularComplex X` homology).

## Nodes (exact signatures, recorded retrospectively from the landed file)

The signatures below are the landed declarations in
`Lib/AlgebraicTopology/Hurewicz/Naturality.lean`, inside
`namespace Mathoverflow1973.Hurewicz`. This expansion was written after the file was
approved; it is not a pre-implementation frozen interface.

```lean
def homotopyMap {n : ℕ} [Nonempty (Fin n)] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) : π_ n X x →* π_ n Y (f x)

theorem cubeChain_natural {n : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin n) X x) :
    SingularChains.inducedChain f n (Hurewicz.cubeChain p) =
      Hurewicz.cubeChain (SecondHurewicz.mapGenLoop f x p)

theorem cubeCycle_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap f) (m + 2) (Hurewicz.cubeCycle p) =
      Hurewicz.cubeCycle (SecondHurewicz.mapGenLoop f x p)

theorem cubeHomologyClass_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.singularHomologyMap f (m + 2)
        (Hurewicz.cubeHomologyClass p) =
      Hurewicz.cubeHomologyClass (SecondHurewicz.mapGenLoop f x p)

theorem hurewiczFunction_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : π_ (m + 2) X x) :
    SingularMayerVietoris.singularHomologyMap f (m + 2)
        (Hurewicz.hurewiczFunction x a) =
      Hurewicz.hurewiczFunction (f x) (homotopyMap f x a)

theorem hurewiczMap_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : Additive (π_ (m + 2) X x)) :
    SingularMayerVietoris.singularHomologyMap f (m + 2) (Hurewicz.hurewiczMap x a) =
      Hurewicz.hurewiczMap (f x) ((homotopyMap f x).toAdditive a)

theorem hurewiczLinearEquiv_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X)
    (hX : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (hY : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j Y (f x)))
    (a : Additive (π_ (m + 3) X x)) :
    SingularMayerVietoris.singularHomologyMap f (m + 3)
        (Hurewicz.hurewiczLinearEquiv x hX a) =
      Hurewicz.hurewiczLinearEquiv (f x) hY ((homotopyMap f x).toAdditive a)

theorem hurewiczLinearEquivOfTwoLE_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) (n : ℕ) (hn : 2 ≤ n)
    (hX : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (hY : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j Y (f x))) :
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    ∀ a : Additive (π_ n X x),
      SingularMayerVietoris.singularHomologyMap f n
          (hurewiczLinearEquivOfTwoLE x n hn hX a) =
        hurewiczLinearEquivOfTwoLE (f x) n hn hY
          ((homotopyMap f x).toAdditive a)

theorem singularHomology_one_subsingleton {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    Subsingleton (SingularMayerVietoris.SingularHomology X 1)

theorem subsingleton_singularHomology_of_lt {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology X k)
```

## Production interface receipt (retrospective; base `2550436` plus working diff)

Provider `C14_InterfaceCheck.lean` (temporary, removed after run; source preserved at
`/home/kimi/s6-notes/C14-interface-provider.lean`):

```lean
import Lib.AlgebraicTopology.Hurewicz.Naturality
noncomputable section
namespace C14_InterfaceCheck
abbrev homotopyMap := @Mathoverflow1973.Hurewicz.homotopyMap
abbrev cubeChain_natural := @Mathoverflow1973.Hurewicz.cubeChain_natural
abbrev cubeCycle_natural := @Mathoverflow1973.Hurewicz.cubeCycle_natural
abbrev cubeHomologyClass_natural := @Mathoverflow1973.Hurewicz.cubeHomologyClass_natural
abbrev hurewiczFunction_natural := @Mathoverflow1973.Hurewicz.hurewiczFunction_natural
abbrev hurewiczMap_natural := @Mathoverflow1973.Hurewicz.hurewiczMap_natural
abbrev hurewiczLinearEquiv_natural :=
  @Mathoverflow1973.Hurewicz.hurewiczLinearEquiv_natural
abbrev hurewiczLinearEquivOfTwoLE_natural :=
  @Mathoverflow1973.Hurewicz.hurewiczLinearEquivOfTwoLE_natural
abbrev singularHomology_one_subsingleton :=
  @Mathoverflow1973.Hurewicz.singularHomology_one_subsingleton
abbrev subsingleton_singularHomology_of_lt :=
  @Mathoverflow1973.Hurewicz.subsingleton_singularHomology_of_lt
end C14_InterfaceCheck
```

Consumer `C14_InterfaceConsumerCheck.lean` (temporary, removed; source preserved at
`/home/kimi/s6-notes/C14-interface-consumer.lean`):

```lean
import C14_InterfaceCheck
noncomputable section
open Mathoverflow1973 Topology
#check @C14_InterfaceCheck.homotopyMap
#check @C14_InterfaceCheck.cubeChain_natural
#check @C14_InterfaceCheck.cubeCycle_natural
#check @C14_InterfaceCheck.cubeHomologyClass_natural
#check @C14_InterfaceCheck.hurewiczFunction_natural
#check @C14_InterfaceCheck.hurewiczMap_natural
#check @C14_InterfaceCheck.hurewiczLinearEquiv_natural
#check @C14_InterfaceCheck.hurewiczLinearEquivOfTwoLE_natural
#check @C14_InterfaceCheck.singularHomology_one_subsingleton
#check @C14_InterfaceCheck.subsingleton_singularHomology_of_lt

-- n = 2, empty lower-subsingleton hypotheses
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X) :
    letI : Nontrivial (Fin 2) := Fin.nontrivial_iff_two_le.mpr (by decide)
    ∀ a : Additive (π_ 2 X x),
      SingularMayerVietoris.singularHomologyMap f 2
          (Hurewicz.hurewiczLinearEquivOfTwoLE x 2 (by decide)
            (by intro j hj hjn; omega) a) =
        Hurewicz.hurewiczLinearEquivOfTwoLE (f x) 2 (by decide)
          (by intro j hj hjn; omega)
          ((Hurewicz.homotopyMap f x).toAdditive a) :=
  C14_InterfaceCheck.hurewiczLinearEquivOfTwoLE_natural f x 2 (by decide)
    (by intro j hj hjn; omega) (by intro j hj hjn; omega)

-- n = 6, four explicit lower-homotopy-group instances on both spaces
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
    [Subsingleton (π_ 4 Y (f x))] [Subsingleton (π_ 5 Y (f x))] :
    letI : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by decide)
    ∀ a : Additive (π_ 6 X x),
      SingularMayerVietoris.singularHomologyMap f 6
          (Hurewicz.hurewiczLinearEquivOfTwoLE x 6 (by decide)
            (by intro j hj hjn; interval_cases j <;> infer_instance) a) =
        Hurewicz.hurewiczLinearEquivOfTwoLE (f x) 6 (by decide)
          (by intro j hj hjn; interval_cases j <;> infer_instance)
          ((Hurewicz.homotopyMap f x).toAdditive a) :=
  C14_InterfaceCheck.hurewiczLinearEquivOfTwoLE_natural f x 6 (by decide)
    (by intro j hj hjn; interval_cases j <;> infer_instance)
    (by intro j hj hjn; interval_cases j <;> infer_instance)

-- vanishing at k = 1 and k = 2 below n = 3
example {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    Subsingleton (SingularMayerVietoris.SingularHomology X 1) :=
  C14_InterfaceCheck.subsingleton_singularHomology_of_lt x 3
    (by intro j hj hjn; interval_cases j <;> infer_instance) 1 (by decide) (by decide)

example {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    Subsingleton (SingularMayerVietoris.SingularHomology X 2) :=
  C14_InterfaceCheck.subsingleton_singularHomology_of_lt x 3
    (by intro j hj hjn; interval_cases j <;> infer_instance) 2 (by decide) (by decide)
```

Commands and results (all under
`PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH`):

- `lake build Lib.AlgebraicTopology.Hurewicz.Naturality` — exit 0;
  `~/s6-notes/C14-naturality-build.log`.
- `lake build Hopf.Recognition` — exit 0 (adapters elaborate definitionally);
  `~/s6-notes/C14-recognition-build.log`.
- `lake env lean -o C14_InterfaceCheck.olean C14_InterfaceCheck.lean` — exit 0;
  `~/s6-notes/C14-interface-provider.log`.
- `LEAN_PATH=.:$LEAN_PATH lake env lean C14_InterfaceConsumerCheck.lean` — exit 0;
  `~/s6-notes/C14-interface-consumer.log`.
- `#print axioms` on `homotopyMap`, `hurewiczLinearEquivOfTwoLE_natural`,
  `subsingleton_singularHomology_of_lt` — `[propext, Classical.choice, Quot.sound]`
  only; `~/s6-notes/C14-naturality-provider.log`.
- `python3 scripts/lib_stock_census.py --check` — PASS, 2663 ≤ 2663;
  `~/s6-notes/C14-census.log`.
