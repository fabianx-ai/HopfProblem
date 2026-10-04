/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.CrossProductPoint
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
/-!
# The prism operator

For a homotopy `H : C(I × A, X)` the prism operator
`Hurewicz.Prism.prismOperator n H : Chains A n →ₗ[ℤ] Chains X (n + 1)`
is the `H`-pushforward of the cross product with the fundamental chain of the interval.  It
satisfies the prism boundary identity `∂(P c) = H₁# c - H₀# c - P(∂c)` (Hatcher, Thm 2.10), so
homotopic maps induce chain-homotopic maps on singular chains.

The simplex-family version `simplexPrismOperator n H` takes a homotopy `H smp` for every
singular `n`-simplex `smp`; for families `H`, `H'` in consecutive degrees that are
face-compatible (`FaceCompatibleHomotopies n H H'`) the same identity holds
(`simplexPrismOperator_boundary`) with the endpoint operators `simplexEndpointOperator`.  As a
consequence, the time-`1` endpoint of a `2`-cycle is homologous to the cycle
(`straightenedTwoCycle_class`).

## Main definitions

* `Hurewicz.Prism.timeSlice`: the time-`t` slice of a homotopy.
* `Hurewicz.Prism.prismOperator`, `prismOperator_boundary`.
* `Hurewicz.Prism.simplexPrism`, `simplexPrism_boundary`.
* `Hurewicz.Prism.simplexPrismOperator`, `simplexEndpointOperator`,
  `FaceCompatibleHomotopies`, `simplexPrismOperator_boundary`.
* `Hurewicz.Prism.straightenedTwoCycle`, `straightenedTwoCycle_class`.
-/

open Set Function Topology
open Hurewicz.DegreeTwo.SimplyConnected (crossPoint_left)

noncomputable section

/-! ### The prism operator -/

/-- The time-`t` slice of a homotopy `H : C(I × A, X)`, as a map `C(A, X)`. -/
def Hurewicz.Prism.timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  H.comp (SingularHomology.crossInsertLeft t)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `H`-pushforward of a `crossInsertLeft t` chain is the `timeSlice H t`
pushforward. -/
theorem Hurewicz.Prism.inducedChain_timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) (n : ℕ)
    (c : SingularChains.Chains A n) :
    SingularChains.inducedChain H n
        (SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n c) =
      SingularChains.inducedChain (timeSlice H t) n c := by
  change
    ((SingularChains.inducedChain H n).comp
          (SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n))
        c =
      _
  rw [← SingularChains.inducedChain_comp]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism operator of a homotopy `H : C(I × A, X)`: `Chains A n →ₗ[ℤ]
Chains X (n+1)`, built from the degree-`n` cross product with `intervalChain`. -/
def Hurewicz.Prism.prismOperator {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) :
    SingularChains.Chains A n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  (SingularChains.inducedChain H (n + 1)).comp
    (SingularHomology.crossProductEdge (unitInterval) A n Hurewicz.DegreeTwo.intervalChain)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `prismOperator n H c` is the `H`-pushforward of `c × intervalChain`. -/
@[simp]
theorem Hurewicz.Prism.prismOperator_apply {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) (c : SingularChains.Chains A n) :
    prismOperator n H c =
      SingularChains.inducedChain H (n + 1)
        (SingularHomology.crossProductEdge (unitInterval) A n
          Hurewicz.DegreeTwo.intervalChain c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism boundary identity: `∂(prism c) = H₁# c - H₀# c - prism(∂c)`. -/
theorem Hurewicz.Prism.prismOperator_boundary {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (c : SingularChains.Chains A (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      SingularChains.inducedChain (timeSlice H 1) (n + 1) c -
          SingularChains.inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((SingularChains.singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← SingularChains.inducedChain_boundary,
    SingularHomology.crossProductEdge_boundary n]
  change
    SingularChains.inducedChain H (n + 1)
        (SingularHomology.crossProductZeroLeft (unitInterval) A (n + 1)
            (SingularChains.boundaryOne (unitInterval) Hurewicz.DegreeTwo.intervalChain) c -
          SingularHomology.crossProductEdge (unitInterval) A n
            Hurewicz.DegreeTwo.intervalChain
            (((SingularChains.singularComplex A).d (n + 1) n).hom c)) =
      _
  simp only [Hurewicz.DegreeTwo.intervalChain_boundary, map_sub, LinearMap.sub_apply, crossPoint_left,
    inducedChain_timeSlice, prismOperator_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Precomposing the homotopy with `id × f` equals pushing the chain forward by `f` first. -/
theorem Hurewicz.Prism.prismOperator_domain {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] (n : ℕ) (f : C(A, B)) (H : C((unitInterval) × B, X))
    (c : SingularChains.Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id (unitInterval)).prodMap f)) c =
      prismOperator n H (SingularChains.inducedChain f n c) := by
  have h :=
    SingularHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f n
      Hurewicz.DegreeTwo.intervalChain c
  rw [SingularChains.inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, SingularChains.inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (SingularChains.inducedChain H (n + 1)) h

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism chain of a homotopy of the standard `n`-simplex:
`prismOperator n H` applied to the identity simplex chain. -/
def Hurewicz.Prism.simplexPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : C((unitInterval) × SingularChains.Simplex n, X)) : SingularChains.Chains X (n + 1) :=
  prismOperator n H
    (SingularChains.simplexChain (SingularChains.Simplex n) n
      (ContinuousMap.id (SingularChains.Simplex n)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `prismOperator` on a simplex chain is the `H`-pushforward of the simplex prism. -/
theorem Hurewicz.Prism.prismOperator_simplex {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (smp : SingularChains.SingularSimplex A n) :
    prismOperator n H (SingularChains.simplexChain A n smp) =
      simplexPrism n (H.comp ((ContinuousMap.id (unitInterval)).prodMap smp)) := by
  have h :=
    prismOperator_domain n smp H
      (SingularChains.simplexChain (SingularChains.Simplex n) n
        (ContinuousMap.id (SingularChains.Simplex n)))
  rw [SingularChains.inducedChain_simplex, ContinuousMap.comp_id] at h
  exact h.symm

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `simplexPrism n H` is `H₁# id - H₀# id - ∑` face prisms. -/
theorem Hurewicz.Prism.simplexPrism_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (H : C((unitInterval) × SingularChains.Simplex (n + 1), X)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom (simplexPrism (n + 1) H) =
      SingularChains.simplexChain X (n + 1) (timeSlice H 1) -
          SingularChains.simplexChain X (n + 1) (timeSlice H 0) -
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            simplexPrism n
              (H.comp
                ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i))) := by
  rw [simplexPrism, prismOperator_boundary, SingularChains.inducedChain_simplex,
    SingularChains.inducedChain_simplex, ContinuousMap.comp_id, ContinuousMap.comp_id]
  rw [SingularChains.boundary_simplex, map_sum]
  simp only [map_zsmul, ContinuousMap.id_comp, prismOperator_simplex]

/-- The endpoint operator `Chains X n →ₗ[ℤ] Chains X n` sending each simplex to its
time-`t` slice under `H`. -/
def Hurewicz.Prism.simplexEndpointOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) : SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n :=
  SingularChains.chainLift X n fun smp => SingularChains.simplexChain X n (timeSlice (H smp) t)

/-- `simplexEndpointOperator` sends a simplex to its time-`t` slice `timeSlice (H
smp) t`. -/
@[simp]
theorem Hurewicz.Prism.simplexEndpointOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) (smp : SingularChains.SingularSimplex X n) :
    simplexEndpointOperator n H t (SingularChains.simplexChain X n smp) =
      SingularChains.simplexChain X n (timeSlice (H smp) t) :=
  SingularChains.chainLift_simplex X n _ smp

/-- The simplexwise prism operator: `Chains X n →ₗ[ℤ] Chains X (n+1)` sending each
simplex `smp` to `simplexPrism n (H smp)`. -/
def Hurewicz.Prism.simplexPrismOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  SingularChains.chainLift X n fun smp => simplexPrism n (H smp)

/-- `simplexPrismOperator` sends a simplex `smp` to `simplexPrism n (H smp)`. -/
@[simp]
theorem Hurewicz.Prism.simplexPrismOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (smp : SingularChains.SingularSimplex X n) :
    simplexPrismOperator n H (SingularChains.simplexChain X n smp) = simplexPrism n (H smp) :=
  SingularChains.chainLift_simplex X n _ smp

/-- `H` and `H'` are face-compatible if `H'` restricted to each face equals `H` of
the face simplex. -/
def Hurewicz.Prism.FaceCompatibleHomotopies {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)) :
    Prop :=
  ∀ smp i,
    (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
      H (smp.comp (SingularChains.simplexFace n i))

/-- For face-compatible families, the `i`-th face of a time slice of `H'` is the corresponding time slice of `H`. -/
theorem Hurewicz.Prism.timeSlice_face {X : Type} [TopologicalSpace X] {n : ℕ}
    {H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)}
    {H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : (unitInterval)) :
    (timeSlice (H' smp) t).comp (SingularChains.simplexFace n i) =
      timeSlice (H (smp.comp (SingularChains.simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

/-- For a face-compatible family, `simplexEndpointOperator` commutes with the
boundary map. -/
theorem Hurewicz.Prism.simplexEndpointOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (t : (unitInterval))
    (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (simplexEndpointOperator (n + 1) H' t c) =
      simplexEndpointOperator n H t (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((SingularChains.singularComplex X).d (n + 1) n).hom).comp
        (simplexEndpointOperator (n + 1) H' t) =
      (simplexEndpointOperator n H t).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, simplexEndpointOperator_simplex,
      SingularChains.boundary_simplex, map_sum, map_zsmul, timeSlice_face h]
  exact LinearMap.congr_fun hc c

/-- For a face-compatible family, the simplexwise prism boundary identity holds:
`∂(prism c) = H₁# c - H₀# c - prism(∂c)`. -/
theorem Hurewicz.Prism.simplexPrismOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
        (simplexPrismOperator (n + 1) H' c) =
      simplexEndpointOperator (n + 1) H' 1 c - simplexEndpointOperator (n + 1) H' 0 c -
        simplexPrismOperator n H (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom).comp
        (simplexPrismOperator (n + 1) H') =
      simplexEndpointOperator (n + 1) H' 1 - simplexEndpointOperator (n + 1) H' 0 -
        (simplexPrismOperator n H).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    have hface := h smp
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, simplexPrismOperator_simplex,
      simplexPrism_boundary, simplexEndpointOperator_simplex, SingularChains.boundary_simplex,
      map_sum, map_zsmul, hface]
  exact LinearMap.congr_fun hc c

/-- If every homotopy starts at its simplex, the time-`0` endpoint operator is the identity. -/
theorem Hurewicz.Prism.simplexEndpointOperator_zero {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) : simplexEndpointOperator n H 0 = LinearMap.id := by
  apply SingularChains.chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

/-- The `2`-cycle obtained by applying the time-`1` endpoint operator of `H₂` to a
`2`-cycle `c`. -/
def Hurewicz.Prism.straightenedTwoCycle {X : Type} [TopologicalSpace X]
    (H₁ : SingularChains.SingularSimplex X 1 → C((unitInterval) × SingularChains.Simplex 1, X))
    (H₂ : SingularChains.SingularSimplex X 2 → C((unitInterval) × SingularChains.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (simplexEndpointOperator 2 H₂ 1 c.1)
    (by
      rw [simplexEndpointOperator_boundary 1 H₁ H₂ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2
          c,
        map_zero])

/-- The straightened `2`-cycle is homologous to the original cycle (the prism is
its homology witness). -/
theorem Hurewicz.Prism.straightenedTwoCycle_class {X : Type} [TopologicalSpace X]
    (H₁ : SingularChains.SingularSimplex X 1 → C((unitInterval) × SingularChains.Simplex 1, X))
    (H₂ : SingularChains.SingularSimplex X 2 → C((unitInterval) × SingularChains.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂) (h₀ : ∀ smp, timeSlice (H₂ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (straightenedTwoCycle H₁ H₂ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
  refine ⟨simplexPrismOperator 2 H₂ c.1, ?_⟩
  rw [simplexPrismOperator_boundary 1 H₁ H₂ h, simplexEndpointOperator_zero 2 H₂ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 c,
    map_zero, sub_zero]
  rfl
