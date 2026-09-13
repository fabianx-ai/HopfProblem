/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology
public import Lib.AlgebraicTopology.SingularHomology.Coproduct

/-!
# Localization of the connecting homomorphism over covers

The Mayer–Vietoris connecting homomorphism is local: it can be computed from a single
component of a chain, and it commutes with the localization of homology over a disjoint
family of open sets:

* `DisjointOpenHomology.inclusion`-family — for a disjoint family of opens, the homology of
  the union is the coproduct of the homologies and the connecting homomorphism is computed
  componentwise;
* `CoverLocalContributions.map_union`, `.inclusion` — the union map and inclusion presentation.

Consumed by the recognition files (local degree bookkeeping) and the basis of the
`SurgeryWindows` homology rows that stay in `Hopf/` pending lanes D1/E1
(see Lib/reports/A.md, obstructions).

## Main definitions and results

* `DisjointOpenHomology.*` : componentwise computation over disjoint opens.
* `CoverLocalContributions.inclusion`, `.map_union` : the localization presentation.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.2 (local computation of the
  connecting homomorphism)

## Tags

localization, connecting homomorphism, disjoint opens
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

def Smale.DisjointOpenHomology.inclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (i : ι) : C(W i, ↥(⋃ j, W j)) :=
  ⟨Set.inclusion (Set.subset_iUnion W i), continuous_subtype_val.subtype_mk _⟩

def Smale.DisjointOpenHomology.unionHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) :
    (Σ i, W i) ≃ₜ ↥(⋃ i, W i) :=
  let e := Equiv.ofBijective (Set.sigmaToiUnion W) (Set.sigmaToiUnion_bijective W hd)
  e.toHomeomorphOfContinuousOpen
    (by
      apply continuous_sigma
      intro i
      exact (Smale.DisjointOpenHomology.inclusion W i).continuous)
    (by
      apply isOpenMap_sigma.mpr
      intro i
      exact (hW i).isOpenMap_inclusion (Set.subset_iUnion W i))

def Smale.DisjointOpenHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(⋃ i, W i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (W i) k) :=
  (SingularHomology.homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).trans
    (Coproduct.sigmaHomologyEquiv (fun i => W i) k)

theorem Smale.DisjointOpenHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W))
    [Fintype ι] (k : ℕ) (a : ∀ i, SingularMayerVietoris.SingularHomology (W i) k) :
    (homologyEquiv W hW hd k).symm a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (Smale.DisjointOpenHomology.inclusion W i) k
          (a i) := by
  change
    (SingularHomology.homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).symm
        ((Coproduct.sigmaHomologyEquiv (fun i => W i) k).symm a) =
      _
  rw [SingularHomology.homeomorphHomologyEquiv_symm_apply, Homeomorph.symm_symm,
    Coproduct.sigmaHomologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

def Smale.CoverOverlapHomology.componentInclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (i : ι) : C(↥(U ∩ V i), ↥(U ∩ ⋃ j, V j)) :=
  ⟨fun x => ⟨x.val, ⟨x.property.1, Set.mem_iUnion.mpr ⟨i, x.property.2⟩⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

def Smale.CoverOverlapHomology.distributeHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) : ↥(U ∩ ⋃ i, V i) ≃ₜ ↥(⋃ i, U ∩ V i) :=
  Homeomorph.setCongr (by ext x; simp)

theorem Smale.CoverOverlapHomology.disjoint_intersections {X : Type} {ι : Type} (U : Set X)
    (V : ι → Set X) (hd : Pairwise (Disjoint on V)) : Pairwise (Disjoint on (fun i => U ∩ V i)) :=
  by
  intro i j hij
  exact (hd hij).mono Set.inter_subset_right Set.inter_subset_right

def Smale.CoverOverlapHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (SingularHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).trans
    (Smale.DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
      (disjoint_intersections U V hd) k)

theorem Smale.CoverOverlapHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : ∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm a =
      ∑ i, SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k (a i) := by
  change
    (SingularHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).symm
        ((Smale.DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
              (disjoint_intersections U V hd) k).symm
          a) =
      _
  rw [SingularHomology.homeomorphHomologyEquiv_symm_apply,
    Smale.DisjointOpenHomology.homologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

theorem Smale.CoverOverlapHomology.homology_decomposition {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k
          (homologyEquiv U V hU hV hd k a i) := by
  have h := homologyEquiv_symm_apply U V hU hV hd k (homologyEquiv U V hU hV hd k a)
  rwa [LinearEquiv.symm_apply_apply] at h

theorem Smale.CoverOverlapHomology.homology_map_out {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] {Y : Type} [TopologicalSpace Y]
    (f : C(↥(U ∩ ⋃ i, V i), Y)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    SingularMayerVietoris.singularHomologyMap f k a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (f.comp (componentInclusion U V i)) k
          (homologyEquiv U V hU hV hd k a i) := by
  calc
    SingularMayerVietoris.singularHomologyMap f k a =
        SingularMayerVietoris.singularHomologyMap f k
          (∑ i,
            SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k
              (homologyEquiv U V hU hV hd k a i)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap f k)
        (homology_decomposition U V hU hV hd k a)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply]

def Smale.CoverLocalContributions.componentConnecting {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (Smale.CoverOverlapHomology.homologyEquiv U V hU hV hd k).toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism U (⋃ i, V i) hU (isOpen_iUnion hV) hc k)

theorem Smale.CoverLocalContributions.map_union {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (V : ι → Set X) (V' : Set Y) (f : C(X, Y))
    (hfV : ∀ i, Set.MapsTo f (V i) V') : Set.MapsTo f (⋃ i, V i) V' := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hfV i hi
end Mathoverflow1973
