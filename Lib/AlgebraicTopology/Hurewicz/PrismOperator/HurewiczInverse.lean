/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.TetrahedronRelation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.TwoTriangles
/-!
# The inverse of the degree-two Hurewicz map

For a simply connected space `X` the operator `triangleClassOperator x` sends a singular
`2`-simplex to the `π_2`-class of its normalized based triangle.  It vanishes on boundaries by
the tetrahedron relation, so it descends to `hurewiczInverse x : H_2 X →ₗ[ℤ] Additive (π_ 2 X x)`
through `secondHomologyDesc`.  Since the Hurewicz map of a based triangle class is the class of
its cycle (`hurewicz_basedTriangleClass`) and the normalized cycle is homologous to the original
one, `hurewiczMap x ∘ hurewiczInverse x = id` (`hurewiczMap_comp_hurewiczInverse`): the
Hurewicz map is surjective (Hatcher, Thm 4.32, first half of the `n = 2` case).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.basedTriangleCycle`, `hurewicz_basedTriangleClass`.
* `Hurewicz.DegreeTwo.SimplyConnected.secondHomologyDesc`: descent of a linear map on `2`-chains
  that kills `3`-boundaries.
* `Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation`, `chainLift_sub_constant_twoCycle`.
* `Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator`, `normalizedTriangleCycleOperator`,
  `hurewiczInverse`, `hurewiczMap_comp_hurewiczInverse`.
-/

open Set Function Topology

noncomputable section

/-! ### Descending to second homology -/

/-- The `2`-cycle of a based triangle (its square chain with boundary correction). -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTriangleCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (SingularChains.simplexChain X 2 τ.val -
      SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x))
    (by
      rw [← squareChain_basedTriangleLoop]
      exact Hurewicz.DegreeTwo.squareChain_boundary (basedTriangleLoop τ))

/-- The underlying chain of `basedTriangleCycle τ`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleCycle_val {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) :=
  rfl

/-- The Hurewicz map on the class of a based triangle equals its cycle class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewicz_basedTriangleClass {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    Hurewicz.DegreeTwo.hurewiczMap x (basedTriangleClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (basedTriangleCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (Hurewicz.DegreeTwo.squareCycle (basedTriangleLoop τ)) =
      _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

/-- The descent of a normalized `2`-cycle to a `π_2`-class: the based triangle
classes summed over the cycle. -/
def Hurewicz.DegreeTwo.SimplyConnected.secondHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] M :=
  SingularHomology.homologyDesc (SingularChains.singularComplex X) 2
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2).subtype)
    (fun b => hF b)

/-- `hurewiczMap` of `secondHomologyDesc c` returns the class of `c`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.secondHomologyDesc_cycleClass {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    secondHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      F c.1 :=
  SingularHomology.homologyDesc_cycleClass (SingularChains.singularComplex X) 2 _ _ c

/-- `hurewiczMap ∘ secondHomologyDesc` is the identity on homology classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.comp_secondHomologyDesc_eq_id {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

/-! ### Chain augmentation and the inverse map -/

/-- The augmentation `Chains X n → ℤ` sending every simplex generator to `1`. -/
def Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] ℤ :=
  SingularChains.chainLift X n fun _ => 1

/-- `chainAugmentation` of a simplex generator is `1`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (smp : SingularChains.SingularSimplex X n) :
    chainAugmentation X n (SingularChains.simplexChain X n smp) = 1 :=
  SingularChains.chainLift_simplex X n _ smp

/-- `chainAugmentation` of a degree-`2` boundary equals `chainAugmentation` of the `2`-chain. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_boundaryTwo (X : Type)
    [TopologicalSpace X] (c : SingularChains.Chains X 2) :
    chainAugmentation X 1 (SingularChains.boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (SingularChains.boundaryTwo X) = chainAugmentation X 2 := by
    apply SingularChains.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

/-- `chainAugmentation` vanishes on `2`-cycles. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_twoCycle (X : Type) [TopologicalSpace X]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc :=
    SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 c
  change SingularChains.boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

/-- `chainLift` of `f - m` equals `chainLift` of `f` minus the augmentation times `m`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant (X : Type) [TopologicalSpace X]
    {M : Type} [AddCommGroup M] [Module ℤ M] (n : ℕ) (f : SingularChains.SingularSimplex X n → M)
    (m : M) (c : SingularChains.Chains X n) :
    SingularChains.chainLift X n (fun smp => f smp - m) c =
      SingularChains.chainLift X n f c - chainAugmentation X n c • m := by
  have h :
    SingularChains.chainLift X n (fun smp => f smp - m) =
      SingularChains.chainLift X n f -
        (LinearMap.toSpanSingleton ℤ M m).comp (chainAugmentation X n) := by
    apply SingularChains.chainMap_ext X n
    intro smp
    simp only [SingularChains.chainLift_simplex, LinearMap.sub_apply, LinearMap.comp_apply,
      chainAugmentation_simplex, LinearMap.toSpanSingleton_apply_one]
  exact
    (LinearMap.congr_fun h c).trans
      (congrArg (fun z : M => SingularChains.chainLift X n f c - z)
        (int_smul_eq_zsmul (inferInstance : Module ℤ M) (chainAugmentation X n c) m))

/-- On a `2`-cycle, `chainLift` of `f - m` equals `chainLift` of `f`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant_twoCycle (X : Type)
    [TopologicalSpace X] {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularChains.SingularSimplex X 2 → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularChains.chainLift X 2 (fun smp => f smp - m) c.1 = SingularChains.chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

/-- The operator `Chains X 2 →ₗ[ℤ] Additive (π_2 X x)` summing the based triangle
classes. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : SingularChains.Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  SingularChains.chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

/-- `triangleClassOperator` applied to a simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    triangleClassOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

/-- `triangleClassOperator` vanishes on `3`-boundaries (the tetrahedron signed
relation). -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (b : SingularChains.Chains X 3) :
    triangleClassOperator x (((SingularChains.singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((SingularChains.singularComplex X).d 3 2).hom = 0 := by
    apply SingularChains.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

/-- The normalized cycle operator on `2`-chains. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularChains.chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

/-- `normalizedTriangleCycleOperator` applied to a simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

/-- The underlying chain of `normalizedTriangleCycleOperator c` is the `chainLift` of the normalized triangle minus the constant simplex. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_val {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (c : SingularChains.Chains X 2) :
    (normalizedTriangleCycleOperator x c).val =
      SingularChains.chainLift X 2
        (fun smp =>
          SingularChains.simplexChain X 2 (normalizedTriangle x smp).val -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2).subtype.comp
        (normalizedTriangleCycleOperator x) =
      SingularChains.chainLift X 2
        (fun smp =>
          SingularChains.simplexChain X 2 (normalizedTriangle x smp).val -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x)) := by
    apply SingularChains.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, normalizedTriangleCycleOperator_simplex,
      Submodule.subtype_apply, basedTriangleCycle_val, SingularChains.chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- On a `2`-cycle value, `normalizedTriangleCycleOperator` agrees with `normalizedTwoCycle`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

/-- Hurewicz after `triangleClassOperator` is `cycleClass` after `normalizedTriangleCycleOperator`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_comp_triangleClassOperator {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (Hurewicz.DegreeTwo.hurewiczMap x).comp (triangleClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply SingularChains.chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

/-- `hurewiczMap` of the triangle-class operator on a `2`-cycle returns its class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_triangleClassOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    Hurewicz.DegreeTwo.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change
    Hurewicz.DegreeTwo.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

/-- The inverse Hurewicz map `H_2 X →ₗ[ℤ] Additive (π_2 X x)` for simply
connected `X`. -/
def Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

/-- `hurewiczInverse` on a cycle class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

/-- `hurewiczMap ∘ hurewiczInverse` is the identity on `H_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_comp_hurewiczInverse {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (Hurewicz.DegreeTwo.hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (Hurewicz.DegreeTwo.hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

/-- `hurewiczMap` of `hurewiczInverse` of a class returns the class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (c : SingularMayerVietoris.SingularHomology X 2) :
    Hurewicz.DegreeTwo.hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c
