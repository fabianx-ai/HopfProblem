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

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Homology of a disjoint open union -/

/-- The inclusion of one piece `W i` into the union. -/
def DisjointOpenHomology.inclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (i : ι) : C(W i, ↥(⋃ j, W j)) :=
  ⟨Set.inclusion (Set.subset_iUnion W i), continuous_subtype_val.subtype_mk _⟩

/-- A pairwise disjoint open union is homeomorphic to the sigma type of its pieces. -/
def DisjointOpenHomology.unionHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) :
    (Σ i, W i) ≃ₜ ↥(⋃ i, W i) :=
  let e := Equiv.ofBijective (Set.sigmaToiUnion W) (Set.sigmaToiUnion_bijective W hd)
  e.toHomeomorphOfContinuousOpen
    (by
      apply continuous_sigma
      intro i
      exact (DisjointOpenHomology.inclusion W i).continuous)
    (by
      apply isOpenMap_sigma.mpr
      intro i
      exact (hW i).isOpenMap_inclusion (Set.subset_iUnion W i))

/-- Singular homology of a disjoint open union is the product of the piece homologies. -/
def DisjointOpenHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(⋃ i, W i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (W i) k) :=
  (SingularHomology.homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).trans
    (Coproduct.sigmaHomologyEquiv (fun i => W i) k)

/-- The inverse decomposition maps a tuple of classes to the sum of their included classes. -/
theorem DisjointOpenHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W))
    [Fintype ι] (k : ℕ) (a : ∀ i, SingularMayerVietoris.SingularHomology (W i) k) :
    (homologyEquiv W hW hd k).symm a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (DisjointOpenHomology.inclusion W i) k
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

/-! ### Homology over intersected cover pieces -/

/-- The inclusion of `U ∩ V i` into `U` intersected with the union. -/
def CoverOverlapHomology.componentInclusion {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (i : ι) : C(↥(U ∩ V i), ↥(U ∩ ⋃ j, V j)) :=
  ⟨fun x => ⟨x.val, ⟨x.property.1, Set.mem_iUnion.mpr ⟨i, x.property.2⟩⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Intersecting with `U` distributes over a union, as a homeomorphism. -/
def CoverOverlapHomology.distributeHomeomorph {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) : ↥(U ∩ ⋃ i, V i) ≃ₜ ↥(⋃ i, U ∩ V i) :=
  Homeomorph.setCongr (by ext x; simp)

/-- Intersecting a pairwise disjoint family with a fixed set stays pairwise disjoint. -/
theorem CoverOverlapHomology.disjoint_intersections {X : Type} {ι : Type} (U : Set X)
    (V : ι → Set X) (hd : Pairwise (Disjoint on V)) : Pairwise (Disjoint on (fun i => U ∩ V i)) :=
  by
  intro i j hij
  exact (hd hij).mono Set.inter_subset_right Set.inter_subset_right

/-- Homology of `U` over a disjoint open union decomposes as the product over the intersections. -/
def CoverOverlapHomology.homologyEquiv {X : Type} [TopologicalSpace X] {ι : Type}
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (SingularHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).trans
    (DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
      (disjoint_intersections U V hd) k)

/-- The inverse decomposition maps intersection classes to the sum of their included classes. -/
theorem CoverOverlapHomology.homologyEquiv_symm_apply {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : ∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm a =
      ∑ i, SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k (a i) := by
  change
    (SingularHomology.homeomorphHomologyEquiv (distributeHomeomorph U V) k).symm
        ((DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i) (fun i => hU.inter (hV i))
              (disjoint_intersections U V hd) k).symm
          a) =
      _
  rw [SingularHomology.homeomorphHomologyEquiv_symm_apply,
    DisjointOpenHomology.homologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

/-- A homology class on `U` over the union is the sum of its contributions on each intersection. -/
theorem CoverOverlapHomology.homology_decomposition {X : Type} [TopologicalSpace X]
    {ι : Type} (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) [Fintype ι] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    a =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k
          (homologyEquiv U V hU hV hd k a i) := by
  have h := homologyEquiv_symm_apply U V hU hV hd k (homologyEquiv U V hU hV hd k a)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- Pushing a class out of the overlap union splits into the pushed contributions on each piece. -/
theorem CoverOverlapHomology.homology_map_out {X : Type} [TopologicalSpace X] {ι : Type}
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

/-- In local piece and overlap coordinates, the left Mayer–Vietoris map is the
sum of regular attachments paired with the negative componentwise filling maps.

The overlap union is a disjoint union, so the inverse homology decomposition is
the sum of the maps induced by its component inclusions. Apply the regular
inclusion to that sum and use the regular commuting squares and functoriality.
For the filling component, the filling squares identify the same sum with the
inverse disjoint-filling decomposition. Passing to filling coordinates recovers
each component, retaining the negative sign of the Mayer–Vietoris convention.
This argument includes degree zero and empty finite families; it requires no
connectivity, orientation, smoothness or homology-vanishing assumption. -/
theorem CoverLocalContributions.leftHomologyMap_in_coordinates
    {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    {R : Type} [TopologicalSpace R] {P A : ι → Type}
    [∀ i, TopologicalSpace (P i)] [∀ i, TopologicalSpace (A i)]
    (r : R ≃ₜ U) (p : ∀ i, P i ≃ₜ V i) (a : ∀ i, A i ≃ₜ ↥(U ∩ V i))
    (α : ∀ i, C(A i, R)) (β : ∀ i, C(A i, P i))
    (hr : ∀ i, (r : C(R, U)).comp (α i) =
      (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V i ⊆ U)).comp
        (a i : C(A i, ↥(U ∩ V i))))
    (hp : ∀ i, (p i : C(P i, V i)).comp (β i) =
      (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V i ⊆ V i)).comp
        (a i : C(A i, ↥(U ∩ V i))))
    (n : ℕ) (c : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) n) :
    let E : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) n ≃ₗ[ℤ]
        (∀ i, SingularMayerVietoris.SingularHomology (A i) n) :=
      (CoverOverlapHomology.homologyEquiv U V hU hV hd n).trans
      (AddEquiv.piCongrRight fun i =>
        (SingularHomology.homeomorphHomologyEquiv (a i) n).symm.toAddEquiv).toIntLinearEquiv
    let Q : (SingularMayerVietoris.SingularHomology U n ×
        SingularMayerVietoris.SingularHomology (↥(⋃ i, V i)) n) ≃ₗ[ℤ]
        (SingularMayerVietoris.SingularHomology R n ×
          (∀ i, SingularMayerVietoris.SingularHomology (P i) n)) :=
      ((SingularHomology.homeomorphHomologyEquiv r n).symm.toAddEquiv.prodCongr
      ((DisjointOpenHomology.homologyEquiv V hV hd n).toAddEquiv.trans
        (AddEquiv.piCongrRight fun i =>
          (SingularHomology.homeomorphHomologyEquiv (p i) n).symm.toAddEquiv))).toIntLinearEquiv
    Q (SingularMayerVietoris.leftHomologyMap U (⋃ i, V i) n c) =
      (∑ i, SingularMayerVietoris.singularHomologyMap (α i) n (E c i),
        fun i => -SingularMayerVietoris.singularHomologyMap (β i) n (E c i)) := by
  let d := CoverOverlapHomology.homologyEquiv U V hU hV hd n c
  let b := fun i => (SingularHomology.homeomorphHomologyEquiv (a i) n).symm (d i)
  have hab (i : ι) :
      SingularMayerVietoris.singularHomologyMap (a i : C(A i, ↥(U ∩ V i))) n (b i) =
        d i :=
    (SingularHomology.homeomorphHomologyEquiv (a i) n).apply_symm_apply (d i)
  let jU := ContinuousMap.inclusion
    (Set.inter_subset_left : U ∩ ⋃ i, V i ⊆ U)
  let jV := ContinuousMap.inclusion
    (Set.inter_subset_right : U ∩ ⋃ i, V i ⊆ ⋃ i, V i)
  have hreg : SingularMayerVietoris.singularHomologyMap jU n c =
      ∑ i, SingularMayerVietoris.singularHomologyMap (r : C(R, U)) n
        (SingularMayerVietoris.singularHomologyMap (α i) n (b i)) := by
    rw [CoverOverlapHomology.homology_map_out U V hU hV hd jU n c]
    apply Finset.sum_congr rfl
    intro i _
    change SingularMayerVietoris.singularHomologyMap
      (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V i ⊆ U)) n (d i) = _
    rw [← hab i, ← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
      ← hr i, SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply]
  have hfill : SingularMayerVietoris.singularHomologyMap jV n c =
      (DisjointOpenHomology.homologyEquiv V hV hd n).symm
        (fun i => SingularMayerVietoris.singularHomologyMap (p i : C(P i, V i)) n
          (SingularMayerVietoris.singularHomologyMap (β i) n (b i))) := by
    rw [CoverOverlapHomology.homology_map_out U V hU hV hd jV n c,
      DisjointOpenHomology.homologyEquiv_symm_apply]
    apply Finset.sum_congr rfl
    intro i _
    change SingularMayerVietoris.singularHomologyMap
      (jV.comp (CoverOverlapHomology.componentInclusion U V i)) n (d i) = _
    rw [← hab i, ← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
    have hs : (jV.comp (CoverOverlapHomology.componentInclusion U V i)).comp
        (a i : C(A i, ↥(U ∩ V i))) =
        (DisjointOpenHomology.inclusion V i).comp
          ((p i : C(P i, V i)).comp (β i)) := by
      rw [hp i]
      rfl
    rw [hs, SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply,
      SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply]
  dsimp only
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  apply Prod.ext
  · change (SingularHomology.homeomorphHomologyEquiv r n).symm
      (SingularMayerVietoris.singularHomologyMap jU n c) =
        ∑ i, SingularMayerVietoris.singularHomologyMap (α i) n (b i)
    rw [hreg, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (SingularHomology.homeomorphHomologyEquiv r n).symm_apply_apply _
  · funext i
    change (SingularHomology.homeomorphHomologyEquiv (p i) n).symm
      ((DisjointOpenHomology.homologyEquiv V hV hd n)
        (-SingularMayerVietoris.singularHomologyMap jV n c) i) =
      -SingularMayerVietoris.singularHomologyMap (β i) n (b i)
    rw [hfill, map_neg, LinearEquiv.apply_symm_apply]
    change (SingularHomology.homeomorphHomologyEquiv (p i) n).symm
      (-(SingularHomology.homeomorphHomologyEquiv (p i) n)
        (SingularMayerVietoris.singularHomologyMap (β i) n (b i))) = _
    rw [map_neg, LinearEquiv.symm_apply_apply]

/-! ### Local contributions of a cover -/

/-- The connecting map from degree `k+1` homology of `X` to the product of degree `k` homologies of the cover overlaps. -/
def CoverLocalContributions.componentConnecting {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :=
  (CoverOverlapHomology.homologyEquiv U V hU hV hd k).toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism U (⋃ i, V i) hU (isOpen_iUnion hV) hc k)

/-- A map sending each `V i` into `V'` sends the union into `V'`. -/
theorem CoverLocalContributions.map_union {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (V : ι → Set X) (V' : Set Y) (f : C(X, Y))
    (hfV : ∀ i, Set.MapsTo f (V i) V') : Set.MapsTo f (⋃ i, V i) V' := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hfV i hi
