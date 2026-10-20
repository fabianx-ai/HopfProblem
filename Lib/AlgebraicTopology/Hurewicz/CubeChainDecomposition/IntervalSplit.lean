/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.CubeChain

/-!
# Splitting the interval chain and the scaled cube

Scaling the coordinate `i` of the cube onto `[0, 1/2]` or `[1/2, 1]`
(`Hurewicz.cubeScaleLeft`, `Hurewicz.cubeScaleRight`) is the cube-level form of the two
half-interval paths `intervalPathLeft`, `intervalPathRight`, whose concatenation is the
identity path. The interval chain splits accordingly: the sum of the two half-interval
chains minus the interval chain is the boundary of the concatenation `2`-simplex
(`intervalChain_split`), and the same identity holds for the fundamental `(n + 2)`-cube
chain scaled in the coordinate `0`, with the cross product of that boundary against the
remaining fundamental cube (`cubeScale_zero_sum_fundamentalCubeChain`).

This is the chain-level input for the additivity of the cube chain under concatenation
`GenLoop.transAt 0`, by which this development shows that the Hurewicz map is a homomorphism
(the argument is recorded in `Lib/docs/C.md`).

## Main definitions

* `Hurewicz.cubeScaleLeft`, `Hurewicz.cubeScaleRight`
* `Hurewicz.intervalScaleLeft`, `Hurewicz.intervalScaleRight`,
  `Hurewicz.intervalPathLeft`, `Hurewicz.intervalPathRight`

## Main results

* `Hurewicz.intervalPathLeft_trans_intervalPathRight`
* `Hurewicz.intervalChain_split`
* `Hurewicz.cubeScale_zero_sum_fundamentalCubeChain`
-/

open Set Function Topology

noncomputable section

/-! ### Scaling the cube and the interval -/

/-- Scale coordinate `i` of the cube onto the left half `[0, 1/2]`. -/
def Hurewicz.cubeScaleLeft {n : ℕ} (i : Fin n) :
    C(Fin n → (unitInterval), Fin n → (unitInterval)) where
  toFun t := Function.update t i ⟨(t i : ℝ) / 2, by
    constructor
    · linarith [unitInterval.nonneg (t i)]
    · have := unitInterval.le_one (t i)
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale coordinate `i` of the cube onto the right half `[1/2, 1]`. -/
def Hurewicz.cubeScaleRight {n : ℕ} (i : Fin n) :
    C(Fin n → (unitInterval), Fin n → (unitInterval)) where
  toFun t := Function.update t i ⟨((t i : ℝ) + 1) / 2, by
    constructor
    · have := unitInterval.nonneg (t i)
      linarith
    · have := unitInterval.le_one (t i)
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale the interval onto the left half `[0, 1/2]`. -/
def Hurewicz.intervalScaleLeft : C((unitInterval), (unitInterval)) where
  toFun t := ⟨(t : ℝ) / 2, by
    constructor
    · linarith [unitInterval.nonneg t]
    · have := unitInterval.le_one t
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale the interval onto the right half `[1/2, 1]`. -/
def Hurewicz.intervalScaleRight : C((unitInterval), (unitInterval)) where
  toFun t := ⟨((t : ℝ) + 1) / 2, by
    constructor
    · have := unitInterval.nonneg t
      linarith
    · have := unitInterval.le_one t
      linarith⟩
  continuous_toFun := by fun_prop

/-- The path along `intervalScaleLeft`, from `0` to `1/2`. -/
def Hurewicz.intervalPathLeft : Path (0 : (unitInterval)) ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ where
  toContinuousMap := Hurewicz.intervalScaleLeft
  source' := by
    apply Subtype.ext
    change (0 : ℝ) / 2 = 0
    norm_num
  target' := by
    apply Subtype.ext
    change (1 : ℝ) / 2 = (1 : ℝ) / 2
    rfl

/-- The path along `intervalScaleRight`, from `1/2` to `1`. -/
def Hurewicz.intervalPathRight :
    Path ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ (1 : (unitInterval)) where
  toContinuousMap := Hurewicz.intervalScaleRight
  source' := by
    apply Subtype.ext
    change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
    norm_num
  target' := by
    apply Subtype.ext
    change ((1 : ℝ) + 1) / 2 = 1
    norm_num

/-- Concatenating the two half-interval paths recovers the identity path. -/
theorem Hurewicz.intervalPathLeft_trans_intervalPathRight :
    Hurewicz.intervalPathLeft.trans Hurewicz.intervalPathRight = Path.id := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · change (2 * (t : ℝ)) / 2 = (t : ℝ)
    ring
  · change ((2 * (t : ℝ) - 1) + 1) / 2 = (t : ℝ)
    ring

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The identity interval chain is the sum of the two half-interval chains, up to the
boundary of the concatenation 2-simplex. -/
theorem Hurewicz.intervalChain_split :
    SingularChains.inducedChain Hurewicz.intervalScaleLeft 1 Hurewicz.DegreeTwo.intervalChain +
        SingularChains.inducedChain Hurewicz.intervalScaleRight 1
          Hurewicz.DegreeTwo.intervalChain -
      Hurewicz.DegreeTwo.intervalChain =
      ((SingularChains.singularComplex (unitInterval)).d 2 1).hom
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight) := by
  have h :=
    SingularChains.boundaryTwo_concatChain Hurewicz.intervalPathLeft
      Hurewicz.intervalPathRight
  rw [show ((SingularChains.singularComplex (unitInterval)).d 2 1).hom = SingularChains.boundaryTwo
      (unitInterval) from rfl, h, Hurewicz.intervalPathLeft_trans_intervalPathRight,
    ← Hurewicz.DegreeTwo.induced_intervalChain Hurewicz.intervalPathLeft,
    ← Hurewicz.DegreeTwo.induced_intervalChain Hurewicz.intervalPathRight]
  simp only [Hurewicz.intervalPathLeft, Hurewicz.intervalPathRight]
  abel

/-- Left scaling on coordinate `0` is left scaling of the interval factor. -/
theorem Hurewicz.cubeScaleLeft_zero_comp_cubeCoordinates (n : ℕ) :
    (Hurewicz.cubeScaleLeft (0 : Fin (n + 1))).comp
        (Hurewicz.cubeCoordinates n) =
      (Hurewicz.cubeCoordinates n).comp
        (Hurewicz.intervalScaleLeft.prodMap (ContinuousMap.id _)) := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self,
      Hurewicz.cubeCoordinates_zero, Hurewicz.intervalScaleLeft]
  · have hj : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_of_ne hj,
      Hurewicz.cubeCoordinates_succ]

/-- Right scaling on coordinate `0` is right scaling of the interval factor. -/
theorem Hurewicz.cubeScaleRight_zero_comp_cubeCoordinates (n : ℕ) :
    (Hurewicz.cubeScaleRight (0 : Fin (n + 1))).comp
        (Hurewicz.cubeCoordinates n) =
      (Hurewicz.cubeCoordinates n).comp
        (Hurewicz.intervalScaleRight.prodMap (ContinuousMap.id _)) := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self,
      Hurewicz.cubeCoordinates_zero, Hurewicz.intervalScaleRight]
  · have hj : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_of_ne hj,
      Hurewicz.cubeCoordinates_succ]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Scaling the zeroth coordinate of the fundamental `(n+2)`-cube onto each half, then
subtracting the unscaled cube, is the cross product of the interval-split 2-chain
against the remaining fundamental cube. -/
theorem Hurewicz.cubeScale_zero_sum_fundamentalCubeChain (n : ℕ) :
    SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2)) +
        SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2)) -
      Hurewicz.fundamentalCubeChain (n + 2) =
      SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
        (SingularHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1))) := by
  rw [Hurewicz.fundamentalCubeChain_succ]
  have hL :
      SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1) Hurewicz.DegreeTwo.intervalChain
              (Hurewicz.fundamentalCubeChain (n + 1)))) =
        SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
          (SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
            (SingularChains.inducedChain Hurewicz.intervalScaleLeft 1
              Hurewicz.DegreeTwo.intervalChain)
            (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.cubeScaleLeft_zero_comp_cubeCoordinates, SingularChains.inducedChain_comp,
      LinearMap.comp_apply, SingularHomology.crossProductEdge_natural,
      SingularChains.inducedChain_id, LinearMap.id_apply]
  have hR :
      SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1) Hurewicz.DegreeTwo.intervalChain
              (Hurewicz.fundamentalCubeChain (n + 1)))) =
        SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
          (SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
            (SingularChains.inducedChain Hurewicz.intervalScaleRight 1
              Hurewicz.DegreeTwo.intervalChain)
            (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.cubeScaleRight_zero_comp_cubeCoordinates, SingularChains.inducedChain_comp,
      LinearMap.comp_apply, SingularHomology.crossProductEdge_natural,
      SingularChains.inducedChain_id, LinearMap.id_apply]
  rw [hL, hR, ← map_add, ← map_sub]
  rw [← LinearMap.add_apply, ← LinearMap.sub_apply, ← map_add, ← map_sub,
    Hurewicz.intervalChain_split]
