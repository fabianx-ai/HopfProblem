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



open Set Function Filter Manifold Topology

@[expose] public noncomputable section

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

/-- Surjectivity of the actual regular attachment sum and vanishing of filling
homology in degree `n+1` make the signed Mayer–Vietoris left map surjective.
The preimage uses the inverse of the fixed overlap coordinates; negative filling
components vanish in their own groups. Textbook: `CENTER_NATIVE_H5_INJECTIVITY_TEXTBOOK.md`,
HI1–HI4. No regular or lower-filling vanishing is required. -/
theorem CoverLocalContributions.leftHomologyMap_surjective_of_regular_surjective
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
    (n : ℕ)
    (hregular : Function.Surjective
      (fun z : ∀ i, SingularMayerVietoris.SingularHomology (A i) (n + 1) =>
        ∑ i, SingularMayerVietoris.singularHomologyMap (α i) (n + 1) (z i)))
    (hPnext : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) (n + 1))) :
    Function.Surjective
      (SingularMayerVietoris.leftHomologyMap U (⋃ i, V i) (n + 1)) := by
  classical
  let E : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) (n + 1) ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (A i) (n + 1)) :=
    (CoverOverlapHomology.homologyEquiv U V hU hV hd (n + 1)).trans
      (AddEquiv.piCongrRight fun i =>
        (SingularHomology.homeomorphHomologyEquiv (a i) (n + 1)).symm.toAddEquiv).toIntLinearEquiv
  let Q : (SingularMayerVietoris.SingularHomology U (n + 1) ×
      SingularMayerVietoris.SingularHomology (↥(⋃ i, V i)) (n + 1)) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology R (n + 1) ×
        (∀ i, SingularMayerVietoris.SingularHomology (P i) (n + 1))) :=
    ((SingularHomology.homeomorphHomologyEquiv r (n + 1)).symm.toAddEquiv.prodCongr
      ((DisjointOpenHomology.homologyEquiv V hV hd (n + 1)).toAddEquiv.trans
        (AddEquiv.piCongrRight fun i =>
          (SingularHomology.homeomorphHomologyEquiv (p i) (n + 1)).symm.toAddEquiv))).toIntLinearEquiv

  intro y
  obtain ⟨z, hz⟩ := hregular (Q y).1
  refine ⟨E.symm z, Q.injective ?_⟩
  have hs := CoverLocalContributions.leftHomologyMap_in_coordinates
    U V hU hV hd hc r p a α β hr hp (n + 1) (E.symm z)
  change Q (SingularMayerVietoris.leftHomologyMap U (⋃ i, V i) (n + 1) (E.symm z)) =
    (∑ i, SingularMayerVietoris.singularHomologyMap (α i) (n + 1) (E (E.symm z) i),
      fun i => -SingularMayerVietoris.singularHomologyMap (β i) (n + 1)
        (E (E.symm z) i)) at hs
  rw [E.apply_symm_apply] at hs
  rw [hs]
  apply Prod.ext
  · exact hz
  · funext i
    exact (hPnext i).elim _ _

/-- Under regular-sum surjectivity and filling degree-`n+1` vanishing, the
actual cover connecting map from degree `n+1` to degree `n` is injective.
Exactness makes the intervening right map zero. Textbook:
`CENTER_NATIVE_H5_INJECTIVITY_TEXTBOOK.md`, HI5–HI6. -/
theorem CoverLocalContributions.connectingHomomorphism_injective_of_regular_surjective
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
    (n : ℕ)
    (hregular : Function.Surjective
      (fun z : ∀ i, SingularMayerVietoris.SingularHomology (A i) (n + 1) =>
        ∑ i, SingularMayerVietoris.singularHomologyMap (α i) (n + 1) (z i)))
    (hPnext : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) (n + 1))) :
    Function.Injective
      (SingularMayerVietoris.connectingHomomorphism U (⋃ i, V i)
        hU (isOpen_iUnion hV) hc n) := by
  have hleft := CoverLocalContributions.leftHomologyMap_surjective_of_regular_surjective
    U V hU hV hd hc r p a α β hr hp n hregular hPnext
  have hpair := LinearMap.exact_iff.mpr
    (SingularMayerVietoris.exact_at_pair U (⋃ i, V i)
      hU (isOpen_iUnion hV) hc (n + 1)).symm
  have hright := (LinearMap.surjective_iff_eq_zero_of_exact hpair).mp hleft
  have hambient := LinearMap.exact_iff.mpr
    (SingularMayerVietoris.exact_at_ambient U (⋃ i, V i)
      hU (isOpen_iUnion hV) hc n).symm
  exact (LinearMap.injective_iff_eq_zero_of_exact hambient).mpr hright


/-- If the regular piece has zero degree-`n+1` homology and every filling piece has
zero degree-`n+1` and degree-`n` homology, the actual Mayer–Vietoris connecting map,
in the specified local overlap coordinates, identifies ambient degree-`n+1` homology
with the kernel of the sum of regular attachment maps.

The proof transfers the local vanishings, uses exactness at the ambient and overlap
terms, and applies the signed local-coordinate identity. Its forward value is the
chosen connecting map followed by the fixed overlap-coordinate equivalence.
This is the general argument in `CENTER_NATIVE_CONNECTING_KERNEL_TEXTBOOK.md`,
sections CK1–CK4; it includes degree zero and empty finite families. -/
noncomputable def CoverLocalContributions.connectingRegularKernelEquiv
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
    (n : ℕ)
    (hR : Subsingleton (SingularMayerVietoris.SingularHomology R (n + 1)))
    (hPnext : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) (n + 1)))
    (hP : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) n)) :
    let f : (∀ i, SingularMayerVietoris.SingularHomology (A i) n) →+
        SingularMayerVietoris.SingularHomology R n :=
      ∑ i, (SingularMayerVietoris.singularHomologyMap (α i) n).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom
          (fun i => SingularMayerVietoris.SingularHomology (A i) n) i)

    let F : (∀ i, SingularMayerVietoris.SingularHomology (A i) n) →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology R n :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := by
          intro c x
          convert! f.map_zsmul c x using 1
          exact int_smul_eq_zsmul .. }
    SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ] LinearMap.ker F := by
  let f : (∀ i, SingularMayerVietoris.SingularHomology (A i) n) →+
      SingularMayerVietoris.SingularHomology R n :=
    ∑ i, (SingularMayerVietoris.singularHomologyMap (α i) n).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom
        (fun i => SingularMayerVietoris.SingularHomology (A i) n) i)

  let F : (∀ i, SingularMayerVietoris.SingularHomology (A i) n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology R n :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        convert! f.map_zsmul c x using 1
        exact int_smul_eq_zsmul .. }
  change SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ] LinearMap.ker F
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
  let δ := SingularMayerVietoris.connectingHomomorphism
    U (⋃ i, V i) hU (isOpen_iUnion hV) hc n
  let L := SingularMayerVietoris.leftHomologyMap U (⋃ i, V i) n
  let J := SingularMayerVietoris.rightHomologyMap U (⋃ i, V i) (n + 1)
  -- Transfer the local degree-(n+1) vanishings to both members of the open cover.
  letI := hR
  letI := hPnext
  letI := hP
  letI : Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1)) :=
    (SingularHomology.homeomorphHomologyEquiv r (n + 1)).symm.injective.subsingleton
  letI : ∀ i, Subsingleton (SingularMayerVietoris.SingularHomology (V i) (n + 1)) :=
    fun i => (SingularHomology.homeomorphHomologyEquiv (p i) (n + 1)).symm.injective.subsingleton
  letI : Subsingleton (SingularMayerVietoris.SingularHomology (↥(⋃ i, V i)) (n + 1)) :=
    (DisjointOpenHomology.homologyEquiv V hV hd (n + 1)).injective.subsingleton
  -- Exactness at ambient homology gives a zero kernel, since the preceding source is zero.
  have hδzero (x : SingularMayerVietoris.SingularHomology X (n + 1))
      (hx : δ x = 0) : x = 0 := by
    have hxrange : x ∈ LinearMap.range J := by
      rw [show LinearMap.range J = LinearMap.ker δ from
        SingularMayerVietoris.exact_at_ambient U (⋃ i, V i) hU (isOpen_iUnion hV) hc n]
      exact hx
    obtain ⟨z, hz⟩ := hxrange
    have hz0 : z = 0 := Subsingleton.elim _ _
    exact hz.symm.trans (by rw [hz0, map_zero])
  have hδinj : Function.Injective δ := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hδzero
    rw [map_sub, hxy, sub_self]
  -- The second exactness statement identifies the connecting image with the left-map kernel.
  have hexact : LinearMap.range δ = LinearMap.ker L :=
    SingularMayerVietoris.exact_at_intersection U (⋃ i, V i) hU (isOpen_iUnion hV) hc n
  have hFeval (c : ∀ i, SingularMayerVietoris.SingularHomology (A i) n) :
      F c = ∑ i, SingularMayerVietoris.singularHomologyMap (α i) n (c i) := by
    change f c = _
    simp [f]
  -- Keep the signed comparison; its filling component vanishes only by the stated local input.
  have hcoord (c : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) n) :
      Q (L c) = (F (E c),
        fun i => -SingularMayerVietoris.singularHomologyMap (β i) n (E c i)) := by
    rw [hFeval]
    exact CoverLocalContributions.leftHomologyMap_in_coordinates
      U V hU hV hd hc r p a α β hr hp n c
  have hker (c : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) n) :
      L c = 0 ↔ F (E c) = 0 := by
    constructor
    · intro hc0
      have h := congrArg Prod.fst (hcoord c)
      rw [hc0, map_zero] at h
      exact h.symm
    · intro hc0
      apply Q.injective
      rw [map_zero, hcoord, hc0]
      exact Prod.ext rfl (Subsingleton.elim _ _)
  -- Restrict exactly E composed with the chosen connecting map, and prove that restriction bijective.
  let T := E.toLinearMap.comp δ
  have hT : ∀ x, T x ∈ LinearMap.ker F := by
    intro x
    apply (hker (δ x)).mp
    have hx : δ x ∈ LinearMap.range δ := LinearMap.mem_range_self δ x
    rw [hexact] at hx
    exact hx
  let K := LinearMap.codRestrict (LinearMap.ker F) T hT
  have hB : Function.Bijective K := by
    constructor
    · intro x y hxy
      apply hδinj
      apply E.injective
      exact congrArg Subtype.val hxy
    · intro c
      have hc0 : L (E.symm c.val) = 0 := by
        apply (hker (E.symm c.val)).mpr
        rw [E.apply_symm_apply]
        exact c.property
      have hcRange : E.symm c.val ∈ LinearMap.range δ := by
        rw [hexact]
        exact hc0
      obtain ⟨x, hx⟩ := hcRange
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change E (δ x) = c.val
      rw [hx, E.apply_symm_apply]
  exact LinearEquiv.ofBijective K hB

/-- The kernel equivalence retains the actual connecting map in the fixed local overlap
coordinates, as in formula (2) of the general connecting/kernel argument. -/
theorem CoverLocalContributions.connectingRegularKernelEquiv_apply
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
    (n : ℕ)
    (hR : Subsingleton (SingularMayerVietoris.SingularHomology R (n + 1)))
    (hPnext : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) (n + 1)))
    (hP : ∀ i, Subsingleton
      (SingularMayerVietoris.SingularHomology (P i) n))
    (x : SingularMayerVietoris.SingularHomology X (n + 1)) :
    let E : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) n ≃ₗ[ℤ]
        (∀ i, SingularMayerVietoris.SingularHomology (A i) n) :=
      (CoverOverlapHomology.homologyEquiv U V hU hV hd n).trans
        (AddEquiv.piCongrRight fun i =>
          (SingularHomology.homeomorphHomologyEquiv (a i) n).symm.toAddEquiv).toIntLinearEquiv
    (CoverLocalContributions.connectingRegularKernelEquiv
      U V hU hV hd hc r p a α β hr hp n hR hPnext hP x).val =
      E (SingularMayerVietoris.connectingHomomorphism
        U (⋃ i, V i) hU (isOpen_iUnion hV) hc n x) := by
  rfl


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
