/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Topology.Homotopy.Suspension
public import Lib.AlgebraicTopology.SingularHomology.Sphere
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.AlgebraicTopology.SingularHomology.Suspension
public import Lib.AlgebraicTopology.SingularHomology.Sum
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct

/-!
# The homology of the sphere

`H_n(Sⁿ) ≅ ℤ` and `H_k(Sⁿ) = 0` for `k ∉ {0, n}` (Hatcher, Corollary 2.14), together with the
circle dictionary `H_1(S¹) ≅ ℤ`:

* `SphereHomology.unitSphereTopClass` — the top class of `Sⁿ` generating `H_n(Sⁿ)`;
* `SphereHomology.unitSphere_homology_subsingleton` — no higher homology;
* `SphereHomology.unitCircleAddCircleHomeomorph` — the circle as `ℝ/ℤ`, identifying the two
  circle models used in the sources;
* the Mayer–Vietoris injectivity helpers (`singularHomologyMap_zero_injective`,
  `leftHomologyMap_zero_ker`) and `suspension_middleBand_pathConnectedSpace`.

## Outline of the proof

1. *The circle.*  `unitCircleAddCircleHomeomorph` transfers the `AddCircle`-model results;
   `sphereCircleHomologyEquiv` (Suspension.lean) gives `H_*(S¹)`.
2. *Induction on the dimension by two hemispheres.*  `Sⁿ` is the union of two balls; MV
   reduces `H_k(Sⁿ)` to `H_k(Sⁿ⁻¹)` (`suspension_middleBand_pathConnectedSpace`,
   the injectivity helpers), yielding vanishing in between
   (`unitSphere_homology_subsingleton`) and the top class at `n`
   (`unitSphereTopClass`).

## Main definitions and results

* `SphereHomology.unitSphereTopClass` : the generator of `H_n(Sⁿ)`.
* `SphereHomology.unitSphere_homology_subsingleton` : `H_k(Sⁿ) = 0` away from `0, n`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Corollary 2.14

## Tags

sphere, homology, top class
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def SphereHomology.unitCircleAddCircleHomeomorph :
    _root_.Circle ≃ₜ SingularHomology.CircleTopology.Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

def SphereHomology.unitCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology _root_.Circle n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SingularHomology.CircleTopology.Circle n :=
  SingularHomology.homeomorphHomologyEquiv unitCircleAddCircleHomeomorph n

def SphereHomology.unitCircleHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 0 ≃ₗ[ℤ] ℤ :=
  SingularHomology.connectedHomologyZeroEquiv _root_.Circle

def SphereHomology.unitCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (unitCircleHomologyEquiv 1).trans SingularHomology.circleHomologyOneEquiv

theorem SphereHomology.unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology _root_.Circle (n + 2)) := by
  let := SingularHomology.circle_homology_subsingleton n
  exact (unitCircleHomologyEquiv (n + 2)).injective.subsingleton

def SphereHomology.sphereCircleHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        0 ≃ₗ[ℤ]
      ℤ :=
  (sphereCircleHomologyEquiv 0).trans unitCircleHomologyZeroEquiv

def SphereHomology.sphereCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        1 ≃ₗ[ℤ]
      ℤ :=
  (sphereCircleHomologyEquiv 1).trans unitCircleHomologyOneEquiv

theorem SphereHomology.sphereCircle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (sphereCircleHomologyEquiv (n + 2)).injective.subsingleton

def SphereHomology.unitSphereHomologyZeroEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ℤ :=
  SingularHomology.connectedHomologyZeroEquiv (UnitSphere (n + 1))

def SphereHomology.unitSphereHomologyTopEquiv :
    (n : ℕ) → SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ℤ
  | 0 => sphereCircleHomologyOneEquiv
  | n + 1 => (unitSphereHomologySuspensionEquiv (n + 1) n).trans (unitSphereHomologyTopEquiv n)

def SphereHomology.unitSphereTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) :=
  (unitSphereHomologyTopEquiv n).symm 1

theorem SphereHomology.singularHomologyMap_zero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Injective (SingularMayerVietoris.singularHomologyMap f 0) := by
  intro a b h
  apply (SingularHomology.connectedHomologyZeroEquiv X).injective
  simpa only [SingularHomology.connectedHomologyZeroEquiv_natural] using
    congrArg (SingularHomology.connectedHomologyZeroEquiv Y) h

theorem SphereHomology.singularHomologyMap_zero_surjective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f 0) := by
  intro b
  refine
    ⟨(SingularHomology.connectedHomologyZeroEquiv X).symm
        (SingularHomology.connectedHomologyZeroEquiv Y b),
      ?_⟩
  apply (SingularHomology.connectedHomologyZeroEquiv Y).injective
  rw [SingularHomology.connectedHomologyZeroEquiv_natural, LinearEquiv.apply_symm_apply]

theorem SphereHomology.singularHomologyMap_zero_bijective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap f 0) :=
  ⟨singularHomologyMap_zero_injective f, singularHomologyMap_zero_surjective f⟩

theorem SphereHomology.leftHomologyMap_zero_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    Function.Injective (SingularMayerVietoris.leftHomologyMap U V 0) := by
  intro a b h
  apply
    singularHomologyMap_zero_injective
      (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))
  simpa only [SingularMayerVietoris.leftHomologyMap_apply] using congrArg Prod.fst h

theorem SphereHomology.leftHomologyMap_zero_ker {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (leftHomologyMap_zero_injective U V)

instance SphereHomology.suspension_middleBand_pathConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : PathConnectedSpace (Suspension.Suspension.middleBand X) :=
  (Suspension.Suspension.middleBandHomeomorph (X :=
        X)).symm.surjective.pathConnectedSpace
    (Suspension.Suspension.middleBandHomeomorph (X := X)).symm.continuous

def SphereHomology.suspensionHomologyOneEquivKernel (X : Type) [TopologicalSpace X] [Nonempty X] :
    SingularMayerVietoris.SingularHomology (Suspension.Suspension X) 1 ≃ₗ[ℤ]
      LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((Suspension.Suspension.northOpen : Set (Suspension.Suspension X)))
          ((Suspension.Suspension.southOpen : Set (Suspension.Suspension X)))
          0) :=
  Suspension.contractibleCoverHomologyOneEquivKernel
    ((Suspension.Suspension.northOpen : Set (Suspension.Suspension X)))
    ((Suspension.Suspension.southOpen : Set (Suspension.Suspension X)))
    Suspension.Suspension.northOpen_isOpen
    Suspension.Suspension.southOpen_isOpen Suspension.Suspension.open_cover

theorem SphereHomology.suspensionLeftHomologyMap_zero_ker (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((Suspension.Suspension.northOpen : Set (Suspension.Suspension X)))
          ((Suspension.Suspension.southOpen : Set (Suspension.Suspension X)))
          0) =
      ⊥ :=
  leftHomologyMap_zero_ker
    ((Suspension.Suspension.northOpen : Set (Suspension.Suspension X)))
    ((Suspension.Suspension.southOpen : Set (Suspension.Suspension X)))

theorem SphereHomology.suspension_homology_one_subsingleton (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    Subsingleton (SingularMayerVietoris.SingularHomology (Suspension.Suspension X) 1) := by
  let :
    Subsingleton
      (LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((Suspension.Suspension.northOpen : Set (Suspension.Suspension X)))
          ((Suspension.Suspension.southOpen : Set (Suspension.Suspension X)))
          0)) := by
    rw [suspensionLeftHomologyMap_zero_ker X]
    infer_instance
  exact (suspensionHomologyOneEquivKernel X).injective.subsingleton

theorem SphereHomology.unitSphere_homology_one_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 2)) 1) := by
  let := suspension_homology_one_subsingleton (UnitSphere (n + 1))
  exact
    (SingularHomology.homeomorphHomologyEquiv (suspensionSphereHomeomorph (n + 1)).symm
        1).injective.subsingleton

theorem SphereHomology.unitSphere_homology_subsingleton (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact (hkn rfl).elim
      | succ k => exact sphereCircle_homology_subsingleton k
  | succ n ih =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact unitSphere_homology_one_subsingleton n
      | succ k =>
        let := ih (k + 1) (Nat.succ_ne_zero _) (by omega)
        exact (unitSphereHomologySuspensionEquiv (n + 1) k).injective.subsingleton
end Mathoverflow1973
