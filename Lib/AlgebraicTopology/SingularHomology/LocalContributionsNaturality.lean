/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LocalContributions

/-!
# Naturality of the localized homology over a disjoint cover

For an open set `U` and a finite disjoint family of open sets `V i`,
`CoverOverlapHomology.homologyEquiv` identifies the homology of `U ∩ ⋃ i, V i` with the product
of the homologies of the pieces `U ∩ V i`. This file records:

* `CoverOverlapHomology.homologyEquiv_symm_single`, `homologyEquiv_inclusion` — the equivalence
  sends the image of a single piece to the corresponding coordinate vector;
* `CoverOverlapHomology.componentMap`, `overlapMap`, `overlapMap_component`,
  `homologyEquiv_map` — a continuous map preserving the cover pieces induces maps on the pieces
  and on the overlap, and the equivalence is natural for them;
* `CoverLocalContributions.componentConnecting_enlarge` — the component of the localized
  connecting homomorphism is unchanged when `U` is enlarged to `U'` as long as `U' ∪ V i` still
  covers the space.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher02], §2.2 (the Mayer-Vietoris sequence and its
  naturality for maps of covers, p. 150).
-/

open Set Function Filter Manifold Topology

noncomputable section

/-- Hypotheses: `U` an open set, `V` a finite family of pairwise disjoint open sets (`hU`, `hV`,
`hd`), a degree `k`, an index `i` and a class `a` in the homology of `U ∩ V i`.  Conclusion: the
inverse of `CoverOverlapHomology.homologyEquiv` takes the coordinate vector `Pi.single i a` to
the image of `a` under the map induced by the inclusion `U ∩ V i ⊆ U ∩ ⋃ j, V j`. -/
theorem CoverOverlapHomology.homologyEquiv_symm_single {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a := by
  rw [homologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- Hypotheses: `U` an open set, `V` a finite family of pairwise disjoint open sets (`hU`, `hV`,
`hd`), a degree `k`, an index `i` and a class `a` in the homology of `U ∩ V i`.  Conclusion:
`CoverOverlapHomology.homologyEquiv` takes the image of `a` under the map induced by the
inclusion `U ∩ V i ⊆ U ∩ ⋃ j, V j` to the coordinate vector `Pi.single i a`; the statement
`homologyEquiv_symm_single` read through the equivalence. -/
theorem CoverOverlapHomology.homologyEquiv_inclusion {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    homologyEquiv U V hU hV hd k
        (SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a) =
      Pi.single i a := by
  apply (homologyEquiv U V hU hV hd k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_single]

/-- Hypotheses: sets `U`, `V i` in `X` and `U'`, `V' i` in `Y` indexed by the same `ι`, a
continuous `f : X → Y` with `Set.MapsTo f U U'` and `Set.MapsTo f (V i) (V' i)` for every `i`,
and an index `i`.  Definition: the restriction of `f` to a continuous map
`U ∩ V i → U' ∩ V' i`. -/
def CoverOverlapHomology.componentMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    C(↥(U ∩ V i), ↥(U' ∩ V' i)) :=
  SingularMayerVietoris.coverRestriction f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

/-- Hypotheses: sets `U`, `V i` in `X` and `U'`, `V' i` in `Y` indexed by the same `ι` and a
continuous `f : X → Y` with `Set.MapsTo f U U'` and `Set.MapsTo f (V i) (V' i)` for every `i`.
Definition: the restriction of `f` to a continuous map
`U ∩ ⋃ i, V i → U' ∩ ⋃ i, V' i`. -/
def CoverOverlapHomology.overlapMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) :
    C(↥(U ∩ ⋃ i, V i), ↥(U' ∩ ⋃ i, V' i)) :=
  SingularMayerVietoris.coverRestriction f _ _
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.2
      exact ⟨hfU hx.1, Set.mem_iUnion.mpr ⟨i, hfV i hi⟩⟩)

/-- Hypotheses: the data of `CoverOverlapHomology.overlapMap` (sets `U`, `V` in `X` and `U'`,
`V'` in `Y`, a continuous `f` with `Set.MapsTo f U U'` and `Set.MapsTo f (V i) (V' i)` for every
`i`) together with an index `i`.  Conclusion: the square of continuous maps commutes, that is
`overlapMap … ∘ componentInclusion U V i = componentInclusion U' V' i ∘ componentMap … i`; both
sides restrict `f`, so this holds by `rfl`. -/
theorem CoverOverlapHomology.overlapMap_component {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    (overlapMap U V U' V' f hfU hfV).comp (componentInclusion U V i) =
      (componentInclusion U' V' i).comp (componentMap U V U' V' f hfU hfV i) :=
  rfl

/-- Naturality of `CoverOverlapHomology.homologyEquiv` for a map of covers.  Hypotheses: a
continuous `f : X → Y` with `Set.MapsTo f U U'` and `Set.MapsTo f (V i) (V' i)` for every `i`, a
`Fintype ι`, both `U`, `V` and `U'`, `V'` open with both families pairwise disjoint (`hU`, `hV`,
`hd`, `hU'`, `hV'`, `hd'`), a degree `k` and a class `a` in the homology of `U ∩ ⋃ i, V i`.
Conclusion: the coordinates under `homologyEquiv` of the image of `a` along `overlapMap` are the
images along the `componentMap`s of the coordinates of `a`. -/
theorem CoverOverlapHomology.homologyEquiv_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) [Fintype ι]
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hU' : IsOpen U')
    (hV' : ∀ i, IsOpen (V' i)) (hd' : Pairwise (Disjoint on V')) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    homologyEquiv U' V' hU' hV' hd' k
        (SingularMayerVietoris.singularHomologyMap (overlapMap U V U' V' f hfU hfV) k a) =
      fun i =>
      SingularMayerVietoris.singularHomologyMap (componentMap U V U' V' f hfU hfV i) k
        (homologyEquiv U V hU hV hd k a i) := by
  apply (homologyEquiv U' V' hU' hV' hd' k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_apply, homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [overlapMap_component, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

/-- Hypotheses: open sets `U ⊆ U'` (`hU`, `hU'`, `hsub`), a finite family `V` of pairwise
disjoint open sets (`hV`, `hd`) with `U ∪ ⋃ i, V i = Set.univ` (`hc`), an index `i` with
`U' ∪ V i = Set.univ` (`hci`), a degree `k` and a class `a` in the homology of `X` in degree
`k + 1`.  Conclusion: pushing the `i`-th component of the localized connecting homomorphism
`CoverLocalContributions.componentConnecting` of the cover `U`, `V` forward along the inclusion
`U ∩ V i ⊆ U' ∩ V i` gives the Mayer-Vietoris connecting homomorphism of the two-set cover `U'`,
`V i` applied to `a`; enlarging `U` to `U'` leaves the component unchanged. -/
theorem CoverLocalContributions.componentConnecting_enlarge {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] (U U' : Set X) (V : ι → Set X) (hU : IsOpen U) (hU' : IsOpen U')
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (hsub : U ⊆ U') (i : ι) (hci : U' ∪ V i = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (CoverOverlapHomology.componentMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx) i)
        k (componentConnecting U V hU hV hd hc k a i) =
      SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a := by
  classical
  have hc' : U' ∪ (⋃ j, V j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ (⋃ j, V j) := hc.symm ▸ Set.mem_univ x
    exact hx.elim (fun hu => Or.inl (hsub hu)) Or.inr
  have hbig :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply (ContinuousMap.id X) U
      (⋃ j, V j) U' (⋃ j, V j) hsub (fun _ hx => hx) hU (isOpen_iUnion hV) hc hU'
      (isOpen_iUnion hV) hc' k a
  rw [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] at hbig
  change
    SingularMayerVietoris.singularHomologyMap
        (CoverOverlapHomology.overlapMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx))
        k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hbig
  have hcoord :=
    congrArg (fun b => CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hbig
  have hnat :=
    congrFun
      (CoverOverlapHomology.homologyEquiv_map U V U' V (ContinuousMap.id X) hsub
        (fun _ _ hx => hx) hU hV hd hU' hV hd k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a))
      i
  rw [hnat] at hcoord
  have hsmall :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply (ContinuousMap.id X) U' (V i)
      U' (⋃ j, V j) (fun _ hx => hx) (Set.subset_iUnion V i) hU' (hV i) hci hU'
      (isOpen_iUnion hV) hc' k a
  rw [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] at hsmall
  change
    SingularMayerVietoris.singularHomologyMap
        (CoverOverlapHomology.componentInclusion U' V i) k
        (SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hsmall
  have hsingle :=
    congrArg (fun b => CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hsmall
  rw [CoverOverlapHomology.homologyEquiv_inclusion, Pi.single_eq_same] at hsingle
  exact hcoord.trans hsingle.symm

end
