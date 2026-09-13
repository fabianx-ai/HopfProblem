/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HopfDegree
import Lib.AlgebraicTopology.Hurewicz.Degree1

/-!
# Naturality of the Hurewicz equivalence and vanishing below degree `n`

The Hurewicz map is natural in the space: postcomposition with a continuous map
`f : C(X, Y)` commutes with the cube class `Hurewicz.cubeHomologyClass`, because the
cube chain `Hurewicz.cubeChain p` is the pushforward `inducedChain p.val` of a fixed
fundamental cube chain and chain pushforward is functorial
(`SingularChains.inducedChain_comp`). Functoriality passes through cycles
(`ModuleHomology.mapCycles_val`) and homology classes
(`ModuleHomology.homologyMap_cycleClass`), and descends through the homotopy quotient
to `hurewiczFunction`, `hurewiczMap`, and the equivalences `hurewiczLinearEquiv` and
`hurewiczLinearEquivOfTwoLE` (`Lib/docs/C.md` §11, Hatcher Thm. 4.32).

A corollary of the equivalence (`Lib/docs/C.md` §14): for a simply
connected space `X` with `Subsingleton (π_ j X x)` for `2 ≤ j < n`, the singular
homology `SingularHomology X k` is a subsingleton for `0 < k < n`. For `k ≥ 2` this
follows from the Hurewicz equivalence; for `k = 1` it is the degree-one Hurewicz
theorem — the first homology is the abelianization of the trivial fundamental group —
via `AlgebraicTopology.Hurewicz.loopHomologyClass_surjective`.

This file uses plain imports until its legacy dependencies support the module system.
Spaces carrying singular homology are in `Type` because the chain interface is
universe zero.

## Outline of the proof

1. Chain functoriality: `cubeChain_natural` rewrites both sides to
   `inducedChain` of the fixed `fundamentalCubeChain` and applies
   `SingularChains.inducedChain_comp`.
2. Cycles and classes: `cubeCycle_natural` and `cubeHomologyClass_natural` transport
   the chain identity through `ModuleHomology.mapCycles_val` and
   `ModuleHomology.homologyMap_cycleClass`.
3. Quotient and equivalence: `hurewiczMap_natural` descends the class identity
   through the homotopy quotient; `hurewiczLinearEquiv_natural` and
   `hurewiczLinearEquivOfTwoLE_natural` extend it to the equivalences.
4. Positive-degree vanishing: `k = 1` uses
   `AlgebraicTopology.Hurewicz.loopHomologyClass_surjective` with every loop
   homotopic to `refl`; `k ≥ 2` transports `Subsingleton` across the equivalence.

## Main declarations

* `Hurewicz.homotopyMap`: the induced map `π_ n X x →* π_ n Y (f x)`.
* `Hurewicz.cubeChain_natural`, `cubeCycle_natural`, `cubeHomologyClass_natural`:
  naturality at the chain, cycle, and homology-class level.
* `Hurewicz.hurewiczFunction_natural`, `hurewiczMap_natural`: naturality descended to
  the homotopy quotient.
* `Hurewicz.hurewiczLinearEquiv_natural`,
  `Hurewicz.hurewiczLinearEquivOfTwoLE_natural`: naturality of the equivalences.
* `Hurewicz.singularHomology_one_subsingleton`,
  `Hurewicz.subsingleton_singularHomology_of_lt`: vanishing below degree `n`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02]; the argument is recorded in
  `Lib/docs/C.md`, §§11 and 14.
* `Lib/docs/C14-NATURALITY.md` (typed ledger).

## Tags

Hurewicz homomorphism, naturality, singular homology, homotopy groups
-/

open Topology

noncomputable section

namespace Mathoverflow1973.Hurewicz

/-! ### The induced map on homotopy groups -/

/-- Postcomposition with a continuous map on based cube loops descends to a monoid
homomorphism `π_ n X x →* π_ n Y (f x)` on homotopy groups. The multiplication
coordinate is the element of `Fin n` chosen by the `Nonempty` instance;
`HomotopyGroup.mul_spec` characterizes the product at an arbitrary coordinate. -/
def homotopyMap {n : ℕ} [Nonempty (Fin n)] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) : π_ n X x →* π_ n Y (f x) where
  toFun :=
    Quotient.map (SecondHurewicz.mapGenLoop f x)
      (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h)
  map_one' := by
    change (⟦SecondHurewicz.mapGenLoop f x GenLoop.const⟧ : π_ n Y (f x)) =
      ⟦GenLoop.const⟧
    rw [SecondHurewicz.mapGenLoop_const]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact
      (congrArg
            (Quotient.map (SecondHurewicz.mapGenLoop f x)
              (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h))
            (HomotopyGroup.mul_spec
              (i := Classical.choice (inferInstance : Nonempty (Fin n)))
              (p := p) (q := q))).trans
        ((congrArg (fun r : GenLoop (Fin n) Y (f x) => (⟦r⟧ : π_ n Y (f x)))
              (SecondHurewicz.mapGenLoop_transAt f x
                (Classical.choice (inferInstance : Nonempty (Fin n))) q p)).trans
          (HomotopyGroup.mul_spec
            (i := Classical.choice (inferInstance : Nonempty (Fin n)))
            (p := SecondHurewicz.mapGenLoop f x p)
            (q := SecondHurewicz.mapGenLoop f x q)).symm)

/-! ### Naturality of the cube chain, cycle, and homology class -/

/-- Postcomposition commutes with the cube chain: `f` applied to the chain of `p`
equals the chain of the postcomposed cube. -/
theorem cubeChain_natural {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin n) X x) :
    SingularChains.inducedChain f n (Hurewicz.cubeChain p) =
      Hurewicz.cubeChain (SecondHurewicz.mapGenLoop f x p) := by
  change SingularChains.inducedChain f n
      (SingularChains.inducedChain p.val n (fundamentalCubeChain n)) =
    SingularChains.inducedChain (f.comp p.val) n (fundamentalCubeChain n)
  rw [SingularChains.inducedChain_comp, LinearMap.comp_apply]

/-- Postcomposition commutes with the cube cycle. -/
theorem cubeCycle_natural {m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap f) (m + 2) (Hurewicz.cubeCycle p) =
      Hurewicz.cubeCycle (SecondHurewicz.mapGenLoop f x p) := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, Hurewicz.cubeCycle_val,
    Hurewicz.cubeCycle_val]
  exact cubeChain_natural f x p

/-- Postcomposition commutes with the cube homology class. -/
theorem cubeHomologyClass_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.singularHomologyMap f (m + 2) (Hurewicz.cubeHomologyClass p) =
      Hurewicz.cubeHomologyClass (SecondHurewicz.mapGenLoop f x p) := by
  change
    (HomologicalComplex.homologyMap (SingularChains.singularChainMap f) (m + 2)).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex X) (m + 2) (Hurewicz.cubeCycle p)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, cubeCycle_natural]
  rfl

/-! ### Naturality on homotopy classes and of the Hurewicz map -/

/-- The Hurewicz function commutes with the induced maps on `π_` and on homology. -/
theorem hurewiczFunction_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : π_ (m + 2) X x) :
    SingularMayerVietoris.singularHomologyMap f (m + 2)
        (Hurewicz.hurewiczFunction x a) =
      Hurewicz.hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p => ?_
  exact cubeHomologyClass_natural f x p

/-- The Hurewicz map is natural in the space. -/
theorem hurewiczMap_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : Additive (π_ (m + 2) X x)) :
    SingularMayerVietoris.singularHomologyMap f (m + 2) (Hurewicz.hurewiczMap x a) =
      Hurewicz.hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczFunction_natural f x a.toMul

/-- The Hurewicz equivalence is natural in the space: applying `f` on homology to the
equivalence at `x` equals the equivalence at `f x` applied to the induced class. -/
theorem hurewiczLinearEquiv_natural {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X)
    (hX : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (hY : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j Y (f x)))
    (a : Additive (π_ (m + 3) X x)) :
    SingularMayerVietoris.singularHomologyMap f (m + 3)
        (Hurewicz.hurewiczLinearEquiv x hX a) =
      Hurewicz.hurewiczLinearEquiv (f x) hY ((homotopyMap f x).toAdditive a) :=
  hurewiczMap_natural f x a

/-- The degree-`n ≥ 2` Hurewicz equivalence is natural in the space. The degree-two
case uses the identification of the higher Hurewicz map with the second Hurewicz map
(`hurewiczMap_eq_second`). -/
theorem hurewiczLinearEquivOfTwoLE_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) (n : ℕ) (hn : 2 ≤ n)
    (hX : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (hY : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j Y (f x))) :
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    ∀ a : Additive (π_ n X x),
      SingularMayerVietoris.singularHomologyMap f n
          (hurewiczLinearEquivOfTwoLE x n hn hX a) =
        hurewiczLinearEquivOfTwoLE (f x) n hn hY ((homotopyMap f x).toAdditive a) := by
  rcases n with _ | _ | m
  · omega
  · omega
  cases m with
  | zero =>
    intro a
    change SingularMayerVietoris.singularHomologyMap f 2
        (SecondHurewicz.hurewiczMap x a) =
      SecondHurewicz.hurewiczMap (f x) ((homotopyMap f x).toAdditive a)
    simpa only [hurewiczMap_eq_second] using hurewiczMap_natural (m := 0) f x a
  | succ m => exact hurewiczLinearEquiv_natural f x hX hY

/-! ### Vanishing below degree `n` -/

/-- The first singular homology of a simply connected space is a subsingleton: every
loop is null-homotopic, every class is the class of a loop, and the constant loop has
class zero. This is the degree-one Hurewicz theorem specialized to trivial `π₁`
(Hatcher Thm. 2A.1). -/
theorem singularHomology_one_subsingleton {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    Subsingleton (SingularMayerVietoris.SingularHomology X 1) := by
  change Subsingleton (AlgebraicTopology.SingularH1 X)
  have hz (a : AlgebraicTopology.SingularH1 X) : a = 0 := by
    obtain ⟨p, rfl⟩ := AlgebraicTopology.Hurewicz.loopHomologyClass_surjective x a
    calc
      AlgebraicTopology.Hurewicz.loopHomologyClass p =
          AlgebraicTopology.Hurewicz.loopHomologyClass (Path.refl x) :=
        AlgebraicTopology.Hurewicz.loopHomologyClass_homotopic
          (Path.Homotopic.Quotient.eq.mp (Subsingleton.elim _ _))
      _ = 0 := AlgebraicTopology.Hurewicz.loopHomologyClass_refl x
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- **Vanishing below degree `n`** (Hatcher Thm. 4.32, second half): for a simply
connected space `X` with `Subsingleton (π_ j X x)` for `2 ≤ j < n`, every positive
degree `k < n` has subsingleton singular homology. -/
theorem subsingleton_singularHomology_of_lt {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology X k) := by
  by_cases htwo : 2 ≤ k
  · letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr htwo
    letI := hpi k htwo hkn
    exact (hurewiczLinearEquivOfTwoLE x k htwo
      (fun j hj hjk => hpi j hj (by omega))).symm.injective.subsingleton
  · have : k = 1 := by omega
    subst k
    exact singularHomology_one_subsingleton x

end Mathoverflow1973.Hurewicz
