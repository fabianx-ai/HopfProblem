/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Topology.Homotopy.CellAttachment

/-!
# `H₀` detects path components

Two points of a space `X` have the same class in `H₀(X; ℤ)` if and only if they are joined by a
path (`MorseCancellation.pointClass_eq_iff_joined`; Hatcher, *Algebraic Topology*,
Proposition 2.7).  The proof evaluates the *component weight* `componentChainWeight x`, the
linear functional on `0`-chains counting the simplices in the component of `x`, which vanishes on
boundaries.  Consequences: a map injective on `H₀` reflects path-connectedness
(`pathConnectedSpace_of_homologyZero_injective`), a homotopy equivalence preserves it
(`pathConnectedSpace_of_homotopyEquiv`), a linear map out of `H₀` is determined by its values on
point classes (`homologyZero_linearMap_ext`), and a cell attached along an empty sphere to a
preconnected space leaves nothing of the old part (`cell_old_empty_of_empty_boundary`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The linear functional on singular `0`-chains of `X` counting, with multiplicity, the
simplices whose vertex is joined to `x` by a path. -/
def MorseCancellation.componentChainWeight {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains X 0 →ₗ[ℤ] ℤ :=
  SingularChains.chainLift X 0 (fun σ => if Joined x (σ (stdSimplex.vertex 0)) then 1 else 0)

attribute [local instance 100] Classical.propDecidable in
/-- `componentChainWeight x` of the point chain at `y` is `1` if `x` and `y` are joined, else `0`.
-/
theorem MorseCancellation.componentChainWeight_point {X : Type} [TopologicalSpace X] (x y : X) :
    componentChainWeight x (SingularChains.pointChain y) = if Joined x y then 1 else 0 := by
  exact SingularChains.chainLift_simplex X 0 _ _

/-- `componentChainWeight x` vanishes on boundaries of `1`-chains. -/
theorem MorseCancellation.componentChainWeight_boundary {X : Type} [TopologicalSpace X] (x : X)
    (b : SingularChains.Chains X 1) : componentChainWeight x (SingularChains.boundaryOne X b) = 0 :=
  by
  classical
  have heq : (componentChainWeight x).comp (SingularChains.boundaryOne X) = 0 := by
    apply SingularChains.chainMap_ext X 1
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, SingularChains.boundaryOne_simplex,
      map_sub, componentChainWeight, SingularChains.chainLift_simplex, ContinuousMap.comp_apply,
      SingularChains.simplexFace_zero_zero, SingularChains.simplexFace_zero_one]
    have hp : Joined (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) :=
      ⟨SingularChains.simplexPath σ⟩
    have hi : Joined x (σ (stdSimplex.vertex 1)) ↔ Joined x (σ (stdSimplex.vertex 0)) :=
      ⟨fun h => h.trans hp.symm, fun h => h.trans hp⟩
    rw [hi, sub_self]
  exact LinearMap.congr_fun heq b

/-- Hatcher, Proposition 2.7: two points `x`, `y` of `X` have the same class in `H₀(X)` iff they
are joined by a path. -/
theorem MorseCancellation.pointClass_eq_iff_joined {X : Type} [TopologicalSpace X] (x y : X) :
    SingularHomology.pointClass x = SingularHomology.pointClass y ↔
      Joined x y := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨b, hb⟩ :=
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 0
            (SingularHomology.pointCycle x) (SingularHomology.pointCycle y)).mp
        h
    have he := congrArg (componentChainWeight x) hb
    change
      componentChainWeight x (SingularChains.boundaryOne X b) =
        componentChainWeight x (SingularChains.pointChain x - SingularChains.pointChain y) at he
    rw [componentChainWeight_boundary, map_sub, componentChainWeight_point,
      componentChainWeight_point, if_pos (Joined.refl x), if_neg hn] at he
    norm_num at he
  · rintro ⟨p⟩
    apply
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 0
          (SingularHomology.pointCycle x) (SingularHomology.pointCycle y)).mpr
    exact ⟨SingularChains.pathChain p.symm, SingularChains.boundaryOne_pathChain p.symm⟩

/-- If `f : C(X, Y)` is injective on `H₀`, then `f x` and `f y` are joined iff `x` and `y` are. -/
theorem MorseCancellation.joined_iff_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y := by
  rw [← pointClass_eq_iff_joined, ← pointClass_eq_iff_joined, ←
    SingularHomology.singularHomologyMap_pointClass f, ←
    SingularHomology.singularHomologyMap_pointClass f, hf.eq_iff]

/-- If `X` is nonempty, `Y` is path-connected and `f : C(X, Y)` is injective on `H₀`, then `X` is
path-connected. -/
theorem MorseCancellation.pathConnectedSpace_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PathConnectedSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) :
    PathConnectedSpace X := by
  exact
    ⟨inferInstance, fun x y =>
      (joined_iff_of_homologyZero_injective f hf x y).mp (PathConnectedSpace.joined (f x) (f y))⟩

/-- A space homotopy equivalent to a path-connected space is path-connected. -/
theorem MorseCancellation.pathConnectedSpace_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  let : Nonempty X := ⟨e.invFun (Classical.arbitrary Y)⟩
  exact
    pathConnectedSpace_of_homologyZero_injective e.toFun
      (SingularHomology.homotopyEquivHomologyEquiv e 0).injective

/-- If the unit sphere of `N` is empty and `X` is preconnected, then the old part of an
embedded cell attachment `D : EmbeddedCellAttachment N X` is empty (the cell is all of `X`). -/
theorem MorseCancellation.cell_old_empty_of_empty_boundary {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] [PreconnectedSpace X]
    (D : EmbeddedCellAttachment N X) [IsEmpty (Metric.sphere (0 : N) 1)] : D.old = ∅ := by
  have hdisjoint (z : MorseHandle.UnitDisk N) : D.cell z ∉ D.old := by
    intro hz
    exact
      isEmptyElim
        (⟨z.val, mem_sphere_zero_iff_norm.mpr ((D.boundary z).mp hz)⟩ : Metric.sphere (0 : N) 1)
  have heq : D.old = (Set.range D.cell)ᶜ := by
    ext x
    constructor
    · intro hx ⟨z, hz⟩
      exact hdisjoint z (hz ▸ hx)
    · intro hx
      have hc : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
      exact hc.resolve_right hx
  have hc : IsClopen D.old := ⟨D.old_closed, heq.symm ▸ D.cell_closed.isClosed_range.isOpen_compl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact h
  · let z : MorseHandle.UnitDisk N := ⟨0, by simp⟩
    exact False.elim (hdisjoint z (h ▸ Set.mem_univ _))

/-- Every singular `0`-chain is a cycle: the linear map `Chains X 0 → Cycle (singularComplex X) 0`.
-/
def MorseCancellation.zeroChainCycle {X : Type} [TopologicalSpace X] :
    SingularChains.Chains X 0 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 0
    where
  toFun
    z :=
    SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 0 z
      (by
        have h := (SingularChains.singularComplex X).shape 0 0 (by simp)
        exact congrArg (fun f => f.hom z) h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear map `Chains X 0 → H₀(X)` sending a `0`-chain to the class of the cycle it is. -/
def MorseCancellation.zeroChainClass {X : Type} [TopologicalSpace X] :
    SingularChains.Chains X 0 →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 0 :=
  (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 0).comp
    zeroChainCycle

/-- `zeroChainClass : Chains X 0 → H₀(X)` is surjective. -/
theorem MorseCancellation.zeroChainClass_surjective {X : Type} [TopologicalSpace X] :
    Function.Surjective (zeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 0
      a
  exact ⟨c.val, rfl⟩

/-- Two linear maps `L K : H₀(X) → A` agreeing on every point class `pointClass x` are equal. -/
theorem MorseCancellation.homologyZero_linearMap_ext {X : Type} [TopologicalSpace X] {A : Type}
    [AddCommGroup A] [Module ℤ A] {L K : SingularMayerVietoris.SingularHomology X 0 →ₗ[ℤ] A}
    (h :
      ∀ x : X,
        L (SingularHomology.pointClass x) = K (SingularHomology.pointClass x)) :
    L = K := by
  have heq : L.comp zeroChainClass = K.comp zeroChainClass := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    have hσ : σ = ContinuousMap.const (SingularChains.Simplex 0) (σ (stdSimplex.vertex 0)) := by
      ext t
      exact congrArg σ (SingularChains.simplexZero_eq_vertex t)
    rw [hσ]
    exact h _
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := zeroChainClass_surjective a
  exact LinearMap.congr_fun heq z

end
