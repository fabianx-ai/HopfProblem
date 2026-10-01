/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.IntervalSplit

/-!
# The cube chain of a concatenation

For based cubes `p q : GenLoop (Fin (n + 2)) X x`, the cube chains of `p`, `q` and of the
concatenation `GenLoop.transAt 0 p q` satisfy

`cubeChain p + cubeChain q - cubeChain (transAt 0 p q) = ∂(…) - (extra term)`

(`Hurewicz.cubeChain_transAt_zero_diff_boundary`): the difference is the pushforward of
the interval-split identity along the uncurrying of the concatenation, and the extra
term is the cross product of the concatenation `2`-simplex with the boundary of the
remaining fundamental cube. That boundary is supported on the cube boundary
(`fundamentalCubeChain_boundary_supported`), where the concatenation is constant, so the
extra term is a multiple of the constant simplex (`cubeChain_transAt_zero_extra_eq_smul`)
and vanishes outright in degree `2` (`cubeChain_transAt_zero_extra_zero`).

The general lemmas on supported chains used along the way (a pushforward along a map into
`V` is `V`-supported; the point chain is supported where its point lies; the pushforward
of a point chain is a point chain) are stated for the singular chains of
`Lib.AlgebraicTopology.SingularHomology`.

This is the chain-level form of the additivity of the Hurewicz map in this development's proof
of the Hurewicz theorem (statement: Hatcher, *Algebraic Topology*, Theorem 4.32; the argument is
recorded in `Lib/docs/C.md`).

## Main results

* `Hurewicz.transAt_comp_cubeScaleLeft`, `Hurewicz.transAt_comp_cubeScaleRight`
* `Hurewicz.cubeChain_transAt_zero_diff`, `Hurewicz.cubeChain_transAt_zero_diff_boundary`
* `Hurewicz.fundamentalCubeChain_boundary_supported`
* `Hurewicz.cubeChain_transAt_zero_extra_zero`, `Hurewicz.cubeChain_transAt_zero_extra_eq_smul`
-/

open Set Function Topology

noncomputable section

/-! ### Concatenation and scaling -/

/-- Concatenation along `i` composed with left scaling recovers the first cube. -/
theorem Hurewicz.transAt_comp_cubeScaleLeft {n : ℕ} [DecidableEq (Fin n)] {X : Type}
    [TopologicalSpace X] {x : X} (i : Fin n) (p q : GenLoop (Fin n) X x) :
    (GenLoop.transAt i p q).val.comp (Hurewicz.cubeScaleLeft i) = p.val := by
  apply ContinuousMap.ext
  intro t
  have hle : ((Hurewicz.cubeScaleLeft i t) i : ℝ) ≤ 1 / 2 := by
    simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self]
    have := unitInterval.le_one (t i)
    linarith
  have ht :
      (GenLoop.transAt i p q).val (Hurewicz.cubeScaleLeft i t) =
        if ((Hurewicz.cubeScaleLeft i t) i : ℝ) ≤ 1 / 2 then
          p (Function.update (Hurewicz.cubeScaleLeft i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleLeft i t) i : ℝ))))
        else
          q (Function.update (Hurewicz.cubeScaleLeft i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleLeft i t) i : ℝ) - 1))) :=
    rfl
  rw [ContinuousMap.comp_apply, ht, if_pos hle]
  apply congrArg p
  funext j
  by_cases hj : j = i
  · simp [hj, Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self]
    apply Subtype.ext
    have hti := unitInterval.nonneg (t i)
    have hti' := unitInterval.le_one (t i)
    have hm : 2 * ((t i : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
      have hx : 2 * ((t i : ℝ) / 2) = (t i : ℝ) := by ring
      rw [hx]
      exact ⟨hti, hti'⟩
    rw [Set.projIcc_of_mem (hx := hm)]
    ring
  · simp [hj, Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_of_ne]

/-- Concatenation along `i` composed with right scaling recovers the second cube. -/
theorem Hurewicz.transAt_comp_cubeScaleRight {n : ℕ} [DecidableEq (Fin n)] {X : Type}
    [TopologicalSpace X] {x : X} (i : Fin n) (p q : GenLoop (Fin n) X x) :
    (GenLoop.transAt i p q).val.comp (Hurewicz.cubeScaleRight i) = q.val := by
  apply ContinuousMap.ext
  intro t
  have hri : ((Hurewicz.cubeScaleRight i t) i : ℝ) = ((t i : ℝ) + 1) / 2 := by
    simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self]
  have ht :
      (GenLoop.transAt i p q).val (Hurewicz.cubeScaleRight i t) =
        if ((Hurewicz.cubeScaleRight i t) i : ℝ) ≤ 1 / 2 then
          p (Function.update (Hurewicz.cubeScaleRight i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ))))
        else
          q (Function.update (Hurewicz.cubeScaleRight i t) i
            (Set.projIcc 0 1 zero_le_one
              (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ) - 1))) :=
    rfl
  by_cases hle : ((Hurewicz.cubeScaleRight i t) i : ℝ) ≤ 1 / 2
  · have ht0 : (t i : ℝ) = 0 := by
      have := unitInterval.nonneg (t i)
      linarith
    rw [ContinuousMap.comp_apply, ht, if_pos hle]
    have hp : p (Function.update (Hurewicz.cubeScaleRight i t) i
        (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ)))) = x := by
      apply p.property
      refine ⟨i, Or.inr ?_⟩
      simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self, hri, ht0]
    have hq : q t = x := by
      apply q.property
      refine ⟨i, Or.inl ?_⟩
      apply Subtype.ext
      exact ht0
    exact hp.trans hq.symm
  · rw [ContinuousMap.comp_apply, ht, if_neg hle]
    apply congrArg q
    funext j
    by_cases hj : j = i
    · simp [hj, Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self]
      apply Subtype.ext
      have hti := unitInterval.nonneg (t i)
      have hti' := unitInterval.le_one (t i)
      have hm : 2 * (((t i : ℝ) + 1) / 2) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        have hx : 2 * (((t i : ℝ) + 1) / 2) - 1 = (t i : ℝ) := by ring
        rw [hx]
        exact ⟨hti, hti'⟩
      rw [Set.projIcc_of_mem (hx := hm)]
      ring
    · simp [hj, Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_of_ne]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cube chains of `p`, `q`, and `transAt 0 p q` differ by the pushforward of the
interval-split identity along the uncurrying of `transAt`. -/
theorem Hurewicz.cubeChain_transAt_zero_diff {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
        Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
      SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
        (SingularHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1))) := by
  -- `Fin (n + 2)` already has `DecidableEq`.
  have hp : Hurewicz.cubeChain p =
      SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
        (SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2))) := by
    rw [Hurewicz.cubeChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.transAt_comp_cubeScaleLeft]
  have hq : Hurewicz.cubeChain q =
      SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
        (SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2))) := by
    rw [Hurewicz.cubeChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.transAt_comp_cubeScaleRight]
  calc
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
          Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
        SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
            (SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
                (Hurewicz.fundamentalCubeChain (n + 2)) +
              SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
                (Hurewicz.fundamentalCubeChain (n + 2)) -
              Hurewicz.fundamentalCubeChain (n + 2)) := by
      rw [hp, hq, Hurewicz.cubeChain]
      simp only [map_add, map_sub]
    _ = SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
                (SingularChains.concatChain Hurewicz.intervalPathLeft
                  Hurewicz.intervalPathRight))
              (Hurewicz.fundamentalCubeChain (n + 1)))) := by
      rw [Hurewicz.cubeScale_zero_sum_fundamentalCubeChain]
    _ = _ := by
      rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `transAt 0` cube-chain difference is a boundary minus the extra term coming from
the remaining cube's own boundary. -/
theorem Hurewicz.cubeChain_transAt_zero_diff_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
        Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
      ((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom
          (SingularChains.inducedChain
            ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
              (Hurewicz.cubeCoordinates (n + 1))) (n + 3)
            (SingularHomology.crossProductTriangle (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (SingularChains.concatChain Hurewicz.intervalPathLeft
                Hurewicz.intervalPathRight)
              (Hurewicz.fundamentalCubeChain (n + 1)))) -
        SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
          (SingularHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (Hurewicz.fundamentalCubeChain (n + 1)))) := by
  rw [Hurewicz.cubeChain_transAt_zero_diff]
  have h := SingularHomology.crossProductTriangle_boundary n
    (SingularChains.concatChain Hurewicz.intervalPathLeft
      Hurewicz.intervalPathRight)
    (Hurewicz.fundamentalCubeChain (n + 1))
  have h' :
      SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1)) =
        ((SingularChains.singularComplex
              (unitInterval × (Fin (n + 1) → (unitInterval)))).d (n + 3) (n + 2)).hom
            (SingularHomology.crossProductTriangle (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (SingularChains.concatChain Hurewicz.intervalPathLeft
                Hurewicz.intervalPathRight)
              (Hurewicz.fundamentalCubeChain (n + 1))) -
          SingularHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [h]
    abel
  rw [h', map_sub, SingularChains.inducedChain_boundary]

/-- Concatenation along coordinate `0` is based on every remaining-coordinate slice that
lies on the remaining cube's boundary. -/
theorem Hurewicz.transAt_cubeCoordinates_of_mem_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) (s : (unitInterval))
    {u : Fin (n + 1) → (unitInterval)} (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    (GenLoop.transAt (0 : Fin (n + 2)) p q).val
        (Hurewicz.cubeCoordinates (n + 1) (s, u)) = x :=
  (GenLoop.transAt (0 : Fin (n + 2)) p q).property _
    (Hurewicz.cubeCoordinates_boundary_right (n + 1) s hu)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The extra term vanishes in degree `2`: the remaining cube is an interval, whose
boundary is two points, and concatenation is based at both. -/
theorem Hurewicz.cubeChain_transAt_zero_extra_zero {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin 2) X x) :
    SingularChains.inducedChain
        ((GenLoop.transAt (0 : Fin 2) p q).val.comp (Hurewicz.cubeCoordinates 1)) 2
      (SingularHomology.crossProductTriangle (unitInterval)
        (Fin 1 → (unitInterval)) 0
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight)
        (((SingularChains.singularComplex (Fin 1 → (unitInterval))).d 1 0).hom
          (Hurewicz.fundamentalCubeChain 1))) = 0 := by
  have hfun :
      (Hurewicz.fundamentalCubeChain 1) =
        SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain :=
    rfl
  rw [hfun, ← SingularChains.inducedChain_boundary, Hurewicz.DegreeTwo.intervalChain_boundary, map_sub]
  have hnat (c : SingularChains.Chains (unitInterval) 0) :
      SingularHomology.crossProductTriangle (unitInterval)
            (Fin 1 → (unitInterval)) 0
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight)
          (SingularChains.inducedChain
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval))) 0 c) =
        SingularChains.inducedChain
          ((ContinuousMap.id (unitInterval)).prodMap
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval)))) 2
          (SingularHomology.crossProductTriangle (unitInterval) (unitInterval) 0
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight) c) := by
    have h := SingularHomology.crossProductTriangle_natural
      (ContinuousMap.id (unitInterval))
      ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
        Fin 1 → (unitInterval))) 0
      (SingularChains.concatChain Hurewicz.intervalPathLeft
        Hurewicz.intervalPathRight) c
    simpa [SingularChains.inducedChain_id] using h.symm
  rw [map_sub, hnat (SingularChains.pointChain 1), hnat (SingularChains.pointChain 0),
    ← map_sub]
  simp only [Hurewicz.DegreeTwo.crossProductTriangle_point_right]
  have hx (y : (unitInterval))
      (hy : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm y) ∈ Cube.boundary (Fin 1)) :
      ((GenLoop.transAt (0 : Fin 2) p q).val.comp (Hurewicz.cubeCoordinates 1)).comp
          (((ContinuousMap.id (unitInterval)).prodMap
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval)))).comp
            (SingularHomology.crossInsertRight y)) =
        ContinuousMap.const (unitInterval) x := by
    apply ContinuousMap.ext
    intro s
    exact Hurewicz.transAt_cubeCoordinates_of_mem_boundary p q s hy
  have h0 : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm (0 : (unitInterval))) ∈
      Cube.boundary (Fin 1) := ⟨0, Or.inl (by simp [Homeomorph.funUnique])⟩
  have h1 : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm (1 : (unitInterval))) ∈
      Cube.boundary (Fin 1) := ⟨0, Or.inr (by simp [Homeomorph.funUnique])⟩
  simp only [map_sub, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
  rw [hx 1 h1, hx 0 h0, sub_self]

/-- Pushforward along a map whose image lies in `V` lands in the `V`-supported chains. -/
theorem SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (V : Set Y)
    (hf : ∀ x, f x ∈ V) (n : ℕ) (a : SingularChains.Chains X n) :
    SingularChains.inducedChain f n a ∈
      SingularMayerVietoris.supportedChainSubmodule V n := by
  have hle : (⊤ : Submodule ℤ (SingularChains.Chains X n)) ≤
      (SingularMayerVietoris.supportedChainSubmodule V n).comap
        (SingularChains.inducedChain f n) := by
    rw [← SingularChains.simplexChain_span X n]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, rfl⟩
    change SingularChains.inducedChain f n (SingularChains.simplexChain X n σ) ∈
      SingularMayerVietoris.supportedChainSubmodule V n
    rw [SingularChains.inducedChain_simplex]
    apply SingularMayerVietoris.simplexChain_mem_supported
    rintro y ⟨s, rfl⟩
    exact hf (σ s)
  exact hle (Submodule.mem_top)

/-- The zero-simplex value of the constant `0`-simplex at `x` is `x`. -/
theorem SingularHomology.zeroSimplexValue_const {X : Type} [TopologicalSpace X]
    (x : X) :
    SingularHomology.zeroSimplexValue
      (ContinuousMap.const (SingularChains.Simplex 0) x) = x :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degree-`0`-left cross product of the point chain at `x` with `b` is the
`x`-insertion pushforward of `b`. -/
theorem SingularHomology.crossProductZeroLeft_pointChain {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (x : X)
    (b : SingularChains.Chains Y n) :
    SingularHomology.crossProductZeroLeft X Y n (SingularChains.pointChain x) b =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft x) n b := by
  rw [SingularChains.pointChain, SingularHomology.crossProductZeroLeft_simplex_left,
    SingularHomology.zeroSimplexValue_const]

/-- The pushforward of the point chain at `x` along `f` is the point chain at `f x`. -/
theorem SingularChains.inducedChain_pointChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularChains.inducedChain f 0 (SingularChains.pointChain x) =
      SingularChains.pointChain (f x) := by
  simp [SingularChains.pointChain, SingularChains.inducedChain_simplex, ContinuousMap.const_comp]

/-- The point chain at `x ∈ U` is supported on `U`. -/
theorem SingularChains.pointChain_mem_supported {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) (hx : x ∈ U) :
    SingularChains.pointChain x ∈ SingularMayerVietoris.supportedChainSubmodule U 0 := by
  apply SingularMayerVietoris.simplexChain_mem_supported
  rintro y ⟨s, rfl⟩
  simpa [ContinuousMap.const_apply] using hx

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of the fundamental `(n+1)`-cube is supported on the cube boundary. -/
theorem Hurewicz.fundamentalCubeChain_boundary_supported :
    ∀ n : ℕ,
      ((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
          (Hurewicz.fundamentalCubeChain (n + 1)) ∈
        SingularMayerVietoris.supportedChainSubmodule (Cube.boundary (Fin (n + 1))) n
  | 0 => by
    have hfun :
        Hurewicz.fundamentalCubeChain 1 =
          SingularChains.inducedChain
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain :=
      rfl
    rw [hfun, ← SingularChains.inducedChain_boundary, Hurewicz.DegreeTwo.intervalChain_boundary,
      map_sub, SingularChains.inducedChain_pointChain, SingularChains.inducedChain_pointChain]
    apply Submodule.sub_mem
    · apply SingularChains.pointChain_mem_supported
      refine ⟨0, Or.inr ?_⟩
      simp [Homeomorph.funUnique]
    · apply SingularChains.pointChain_mem_supported
      refine ⟨0, Or.inl ?_⟩
      simp [Homeomorph.funUnique]
  | n + 1 => by
    have ih := Hurewicz.fundamentalCubeChain_boundary_supported n
    rw [Hurewicz.fundamentalCubeChain_succ, ← SingularChains.inducedChain_boundary,
      SingularHomology.crossProductEdge_boundary n Hurewicz.DegreeTwo.intervalChain
        (Hurewicz.fundamentalCubeChain (n + 1)), map_sub]
    apply Submodule.sub_mem
    · have hd : ((SingularChains.singularComplex (unitInterval)).d 1 0).hom
          Hurewicz.DegreeTwo.intervalChain =
        SingularChains.pointChain (1 : (unitInterval)) -
          SingularChains.pointChain (0 : (unitInterval)) :=
        Hurewicz.DegreeTwo.intervalChain_boundary
      rw [hd, map_sub, LinearMap.sub_apply, SingularHomology.crossProductZeroLeft_pointChain,
        SingularHomology.crossProductZeroLeft_pointChain, map_sub]
      apply Submodule.sub_mem
      · rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
        apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
        intro u
        exact Hurewicz.cubeCoordinates_boundary_left (n + 1) 1 u (Or.inr rfl)
      · rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
        apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
        intro u
        exact Hurewicz.cubeCoordinates_boundary_left (n + 1) 0 u (Or.inl rfl)
    · rw [← SingularMayerVietoris.subtypeInclusion_chain_range
          (Cube.boundary (Fin (n + 1))) n] at ih
      obtain ⟨c, hc⟩ := ih
      rw [← hc]
      have hinterval : Hurewicz.DegreeTwo.intervalChain =
          SingularChains.inducedChain (ContinuousMap.id (unitInterval)) 1
            Hurewicz.DegreeTwo.intervalChain := by
        rw [SingularChains.inducedChain_id, LinearMap.id_apply]
      rw [hinterval, ← SingularHomology.crossProductEdge_natural
          (ContinuousMap.id (unitInterval))
          (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1)))) n
          Hurewicz.DegreeTwo.intervalChain c, ← LinearMap.comp_apply,
        ← SingularChains.inducedChain_comp]
      apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
      intro z
      exact Hurewicz.cubeCoordinates_boundary_right (n + 1) z.1 z.2.property

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The extra term of the `transAt 0` cube-chain difference is a multiple of the constant
simplex: concatenation is based on the remaining boundary, and `d(fund)` is supported
there. -/
theorem Hurewicz.cubeChain_transAt_zero_extra_eq_smul {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    ∃ k : ℤ,
      SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
        (SingularHomology.crossProductTriangle (unitInterval)
          (Fin (n + 1) → (unitInterval)) n
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight)
          (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
            (Hurewicz.fundamentalCubeChain (n + 1)))) =
        k • SingularChains.simplexChain X (n + 2)
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) := by
  have hsup := Hurewicz.fundamentalCubeChain_boundary_supported n
  rw [← SingularMayerVietoris.subtypeInclusion_chain_range (Cube.boundary (Fin (n + 1))) n]
    at hsup
  obtain ⟨c, hc⟩ := hsup
  have hconcat :
      SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight =
        SingularChains.inducedChain (ContinuousMap.id (unitInterval)) 2
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight) := by
    rw [SingularChains.inducedChain_id, LinearMap.id_apply]
  have hconst :
      ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))).comp
          ((ContinuousMap.id (unitInterval)).prodMap
            (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1))))) =
        ContinuousMap.const
          ((unitInterval) × Cube.boundary (Fin (n + 1))) x := by
    apply ContinuousMap.ext
    intro z
    exact Hurewicz.transAt_cubeCoordinates_of_mem_boundary p q z.1 z.2.property
  refine ⟨Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation
      ((unitInterval) × Cube.boundary (Fin (n + 1))) (n + 2)
      (SingularHomology.crossProductTriangle (unitInterval)
        (Cube.boundary (Fin (n + 1))) n
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight) c), ?_⟩
  rw [← hc, hconcat, ← SingularHomology.crossProductTriangle_natural
      (ContinuousMap.id (unitInterval))
      (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1)))) n
      (SingularChains.concatChain Hurewicz.intervalPathLeft
        Hurewicz.intervalPathRight) c, ← LinearMap.comp_apply,
    ← SingularChains.inducedChain_comp, hconst, SingularChains.inducedChain_const, ← hconcat]
