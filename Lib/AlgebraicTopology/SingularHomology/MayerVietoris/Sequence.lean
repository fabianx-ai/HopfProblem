/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallSimplices

/-!
# The Mayer–Vietoris sequence

For open sets `U`, `V` with `U ∪ V = X`, the maps
`leftHomologyMap U V n : H_n(U ∩ V) →ₗ[ℤ] H_n U × H_n V`, `a ↦ (i_* a, −j_* a)`,
`rightHomologyMap U V n : H_n U × H_n V →ₗ[ℤ] H_n X`, `(a, b) ↦ i_* a + j_* b`, and the
connecting homomorphism `connectingHomomorphism U V hU hV hcover n : H_{n+1} X →ₗ[ℤ] H_n(U ∩ V)`
form the long exact Mayer–Vietoris sequence
`… → H_{n+1} X → H_n(U ∩ V) → H_n U ⊕ H_n V → H_n X → H_{n-1}(U ∩ V) → …`
(Hatcher, *Algebraic Topology*, §2.2, Mayer–Vietoris sequences), stated as the three
range-equals-kernel identities `exact_at_intersection`, `exact_at_pair`, `exact_at_ambient`;
in degree `0` the right map is surjective (`rightHomologyMap_zero_surjective`).  The sequence is
the homology sequence of the small chain sequence with its third term transported along the
small simplices equivalence `H^{U,V}_n X ≃ H_n X` (`rightHomologyMap_eq_transport`,
`connectingHomomorphism_comparison`).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### The Mayer–Vietoris sequence -/

/-- The left Mayer–Vietoris homology map. -/
abbrev SingularMayerVietoris.leftHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ] (SingularHomology U n × SingularHomology V n) :=
  smallLeftHomologyMap U V n

/-- The right Mayer–Vietoris homology map. -/
def SingularMayerVietoris.rightHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SingularHomology X n := by
  let f :=
    (singularHomologyMap (subtypeInclusion U) n).toAddMonoidHom.coprod
      (singularHomologyMap (subtypeInclusion V) n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r
        a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

/-- The left map computes the signed inclusion pair. -/
theorem SingularMayerVietoris.leftHomologyMap_apply {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    leftHomologyMap U V n a =
      (singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n
            a) :=
  smallLeftHomologyMap_apply U V n a

/-- The right map computes the sum of inclusions. -/
@[simp]
theorem SingularMayerVietoris.rightHomologyMap_apply {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    rightHomologyMap U V n a =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 :=
  rfl

/-- The right map transports through the small-homology comparison. -/
theorem SingularMayerVietoris.rightHomologyMap_eq_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    rightHomologyMap U V n = (smallHomologyComparison U V n).comp (smallRightHomologyMap U V n) :=
  by
  apply LinearMap.ext
  intro a
  exact (smallHomologyComparison_right U V n a).symm

/-- The left map after the connecting map is zero. -/
theorem SingularMayerVietoris.leftHomologyMap_comp_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : (rightHomologyMap U V n).comp (leftHomologyMap U V n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun (smallLeftHomologyMap_comp_right U V n) a
  change smallRightHomologyMap U V n (smallLeftHomologyMap U V n a) = 0 at ha
  rw [rightHomologyMap_eq_comparison]
  change
    smallHomologyComparison U V n (smallRightHomologyMap U V n (smallLeftHomologyMap U V n a)) = 0
  rw [ha, map_zero]

/-- The equivalence computes the comparison map. -/
theorem SingularMayerVietoris.smallHomologyEquiv_eq_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallHomologyEquiv U V hU hV hcover n).toLinearMap = smallHomologyComparison U V n :=
  smallHomologyEquiv_toLinearMap U V hU hV hcover n

/-- The Mayer–Vietoris connecting homomorphism. -/
def SingularMayerVietoris.connectingHomomorphism {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularHomology X (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  (smallConnectingMap U V n).comp (smallHomologyEquiv U V hU hV hcover (n + 1)).symm.toLinearMap

/-- The connecting homomorphism transports through the comparison. -/
theorem SingularMayerVietoris.connectingHomomorphism_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SmallHomology U V (n + 1)) :
    connectingHomomorphism U V hU hV hcover n (smallHomologyComparison U V (n + 1) a) =
      smallConnectingMap U V n a := by
  rw [← smallHomologyEquiv_eq_comparison U V hU hV hcover]
  exact
    congrArg (smallConnectingMap U V n)
      ((smallHomologyEquiv U V hU hV hcover (n + 1)).symm_apply_apply a)

/-- The right map equals the transported small right map. -/
theorem SingularMayerVietoris.rightHomologyMap_eq_transport {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    rightHomologyMap U V n =
      (smallHomologyEquiv U V hU hV hcover n).toLinearMap.comp (smallRightHomologyMap U V n) := by
  rw [smallHomologyEquiv_eq_comparison, rightHomologyMap_eq_comparison]

/-- Mayer–Vietoris exactness at the intersection term. -/
theorem SingularMayerVietoris.exact_at_intersection {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (connectingHomomorphism U V hU hV hcover n) =
      LinearMap.ker (leftHomologyMap U V n) := by
  rw [connectingHomomorphism, rightTransport_connecting_range]
  exact small_exact_at_intersection U V n

/-- Mayer–Vietoris exactness at the pair term. -/
theorem SingularMayerVietoris.exact_at_pair {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (leftHomologyMap U V n) = LinearMap.ker (rightHomologyMap U V n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover, rightTransport_second_ker]
  exact small_exact_at_pair U V n

/-- The Mayer-Vietoris exactness statement: for open `U`, `V` covering `X`, the long exact sequence assembled from the short exact chain sequence is exact at the ambient homology - the connecting homomorphism `H_n(U cap V) -> H_{n-1}(U + V)` makes the braid exact (Hatcher, Algebraic Topology, Theorem 2.20). -/
theorem SingularMayerVietoris.exact_at_ambient {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (rightHomologyMap U V (n + 1)) =
      LinearMap.ker (connectingHomomorphism U V hU hV hcover n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact
    rightTransport_range_eq_ker (smallHomologyEquiv U V hU hV hcover (n + 1))
      (smallRightHomologyMap U V (n + 1)) (smallConnectingMap U V n)
      (small_exact_at_smallHomology U V n)

/-- The degree-zero right map is surjective. -/
theorem SingularMayerVietoris.rightHomologyMap_zero_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Function.Surjective (rightHomologyMap U V 0) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact
    rightTransport_second_surjective (smallHomologyEquiv U V hU hV hcover 0)
      (smallRightHomologyMap U V 0) (smallRightHomologyMap_zero_surjective U V)

/-- The connecting map after the left map is zero. -/
theorem SingularMayerVietoris.connectingHomomorphism_comp_left {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (leftHomologyMap U V n).comp (connectingHomomorphism U V hU hV hcover n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha :
    connectingHomomorphism U V hU hV hcover n a ∈
      LinearMap.range (connectingHomomorphism U V hU hV hcover n) :=
    ⟨a, rfl⟩
  rw [exact_at_intersection] at ha
  exact ha
