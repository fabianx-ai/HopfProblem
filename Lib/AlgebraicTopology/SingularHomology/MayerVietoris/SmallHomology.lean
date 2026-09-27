/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.ChainSequence
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.BiprodSequence
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology

/-!
# The homology sequence of the small chain sequence

Applying the long exact homology sequence to the short exact sequence of chain complexes
`0 → C(U ∩ V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0` gives, for any sets `U V : Set X`, an exact
sequence `… → H_{n+1}^{U,V}(X) → H_n(U ∩ V) → H_n U × H_n V → H_n^{U,V}(X) → …`
(`smallConnectingMap`, `smallLeftHomologyMap`, `smallRightHomologyMap`; exactness
`small_exact_at_intersection`, `small_exact_at_pair`, `small_exact_at_smallHomology`), where
`SmallHomology U V n` is the homology of the small chain complex.  The comparison
`smallHomologyComparison U V n : H_n^{U,V}(X) →ₗ[ℤ] H_n X` is induced by the inclusion of small
chains and intertwines the right maps (`smallHomologyComparison_right`).  The lemmas
`rightTransport_*` transport exactness along a linear equivalence of the third term, ready for
replacing `H^{U,V}` by `H` once the inclusion is known to be a quasi-isomorphism (Hatcher,
*Algebraic Topology*, §2.2, Mayer–Vietoris sequences).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Small homology and the comparison -/

/-- The homology of the small-chains complex. -/
abbrev SingularMayerVietoris.SmallHomology {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :=
  (smallComplex U V).homology n

/-- The left map on small homology. -/
def SingularMayerVietoris.smallLeftHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ] (SingularHomology U n × SingularHomology V n) :=
  biprodSequenceFirstMap (leftMap U V) n

/-- The right map on small homology. -/
def SingularMayerVietoris.smallRightHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SmallHomology U V n :=
  biprodSequenceSecondMap (rightMap U V) n

/-- The connecting map of the small homology sequence. -/
def SingularMayerVietoris.smallConnectingMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : SmallHomology U V (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  connectingMap (chainSequence_shortExact U V) n

/-- The comparison from small homology to singular homology. -/
def SingularMayerVietoris.smallHomologyComparison {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : SmallHomology U V n →ₗ[ℤ] SingularHomology X n :=
  homologyLinearMap (smallInclusion U V) n

/-- The left small-homology map in components. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_components {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (homologyLinearMap
          (leftMap U V ≫
            (CategoryTheory.Limits.biprod.fst :
              middleComplex U V ⟶ SingularChains.singularComplex U))
          n a,
        homologyLinearMap
          (leftMap U V ≫
            (CategoryTheory.Limits.biprod.snd :
              middleComplex U V ⟶ SingularChains.singularComplex V))
          n a) := by
  apply Prod.ext
  · exact
      (LinearMap.congr_fun
          (homologyLinearMap_comp (leftMap U V) CategoryTheory.Limits.biprod.fst n) a).symm
  · exact
      (LinearMap.congr_fun
          (homologyLinearMap_comp (leftMap U V) CategoryTheory.Limits.biprod.snd n) a).symm

/-- The right small-homology map in components. -/
theorem SingularMayerVietoris.smallRightHomologyMap_components {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap
          ((CategoryTheory.Limits.biprod.inl :
              SingularChains.singularComplex U ⟶ middleComplex U V) ≫
            rightMap U V)
          n a.1 +
        homologyLinearMap
          ((CategoryTheory.Limits.biprod.inr :
              SingularChains.singularComplex V ⟶ middleComplex U V) ≫
            rightMap U V)
          n a.2 := by
  rw [inl_rightMap, inr_rightMap]
  exact biprodSequenceSecondMap_desc (toSmallLeft U V) (toSmallRight U V) n a

/-- The left small-homology map on a class. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n
            a) := by
  rw [smallLeftHomologyMap_components, leftMap_fst, leftMap_snd, homologyLinearMap_neg]
  rfl

/-- The right small-homology map on a class. -/
theorem SingularMayerVietoris.smallRightHomologyMap_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap (toSmallLeft U V) n a.1 + homologyLinearMap (toSmallRight U V) n a.2 := by
  rw [smallRightHomologyMap_components, inl_rightMap, inr_rightMap]

/-- The comparison intertwines the right maps. -/
theorem SingularMayerVietoris.smallHomologyComparison_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallHomologyComparison U V n (smallRightHomologyMap U V n a) =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 := by
  rw [smallRightHomologyMap_apply, map_add]
  apply congrArg₂ (· + ·)
  · change
      homologyLinearMap (smallInclusion U V) n (homologyLinearMap (toSmallLeft U V) n a.1) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallLeft_inclusion]
  · change
      homologyLinearMap (smallInclusion U V) n (homologyLinearMap (toSmallRight U V) n a.2) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallRight_inclusion]

/-- The small sequence is exact at the intersection homology. -/
theorem SingularMayerVietoris.small_exact_at_intersection {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    LinearMap.range (smallConnectingMap U V n) = LinearMap.ker (smallLeftHomologyMap U V n) :=
  biprodSequence_exact_at_leftHomology (chainSequence_shortExact U V) n

/-- The small sequence is exact at the pair homology. -/
theorem SingularMayerVietoris.small_exact_at_pair {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    LinearMap.range (smallLeftHomologyMap U V n) = LinearMap.ker (smallRightHomologyMap U V n) :=
  biprodSequence_exact_at_middleHomology (chainSequence_shortExact U V) n

/-- The small sequence is exact at the small homology. -/
theorem SingularMayerVietoris.small_exact_at_smallHomology {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    LinearMap.range (smallRightHomologyMap U V (n + 1)) =
      LinearMap.ker (smallConnectingMap U V n) :=
  biprodSequence_exact_at_rightHomology (chainSequence_shortExact U V) n

/-- The degree-zero right small map is surjective. -/
theorem SingularMayerVietoris.smallRightHomologyMap_zero_surjective {X : Type}
    [TopologicalSpace X] (U V : Set X) : Function.Surjective (smallRightHomologyMap U V 0) :=
  biprodSequence_second_zero_surjective (chainSequence_shortExact U V)

/-- The left map after the connecting map is zero. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_comp_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : (smallRightHomologyMap U V n).comp (smallLeftHomologyMap U V n) = 0 :=
  by
  apply LinearMap.ext
  intro a
  have ha : smallLeftHomologyMap U V n a ∈ LinearMap.range (smallLeftHomologyMap U V n) :=
    ⟨a, rfl⟩
  rw [small_exact_at_pair] at ha
  exact ha

/-- Transported exactness: the range is the kernel. -/
theorem SingularMayerVietoris.rightTransport_range_eq_ker {A P B C : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup P] [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C]
    [Module ℤ C] (e : B ≃ₗ[ℤ] C) (g : P →ₗ[ℤ] B) (δ : B →ₗ[ℤ] A)
    (h : LinearMap.range g = LinearMap.ker δ) :
    LinearMap.range (e.toLinearMap.comp g) = LinearMap.ker (δ.comp e.symm.toLinearMap) := by
  ext c
  change (∃ p, e (g p) = c) ↔ δ (e.symm c) = 0
  constructor
  · rintro ⟨p, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hp : g p ∈ LinearMap.range g := ⟨p, rfl⟩
    rw [h] at hp
    exact hp
  · intro hc
    have hp : e.symm c ∈ LinearMap.range g := by
      rw [h]
      exact hc
    obtain ⟨p, hp⟩ := hp
    exact ⟨p, (congrArg e hp).trans (e.apply_symm_apply c)⟩

/-- The transported connecting range. -/
theorem SingularMayerVietoris.rightTransport_connecting_range {A B C : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (δ : B →ₗ[ℤ] A) : LinearMap.range (δ.comp e.symm.toLinearMap) = LinearMap.range δ :=
  e.symm.range_comp δ

/-- The transported second map's kernel. -/
theorem SingularMayerVietoris.rightTransport_second_ker {P B C : Type*} [AddCommGroup P]
    [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (g : P →ₗ[ℤ] B) : LinearMap.ker (e.toLinearMap.comp g) = LinearMap.ker g :=
  e.ker_comp g

/-- The transported second map is surjective. -/
theorem SingularMayerVietoris.rightTransport_second_surjective {P B C : Type*} [AddCommGroup P]
    [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (g : P →ₗ[ℤ] B) (hg : Function.Surjective g) : Function.Surjective (e.toLinearMap.comp g) :=
  e.surjective.comp hg
