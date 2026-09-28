/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.MayerVietorisShortExact
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains

/-!
# The Mayer–Vietoris short exact sequence of chain complexes

For sets `U V : Set X`, the chain maps `leftMap U V : C(U ∩ V) ⟶ C(U) ⊞ C(V)`,
`c ↦ (i_* c, −j_* c)`, and `rightMap U V : C(U) ⊞ C(V) ⟶ C^{U,V}(X)`, `(a, b) ↦ i_* a + j_* b`,
form a short exact sequence of chain complexes
`0 → C(U ∩ V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0` (`chainSequence`, `chainSequence_shortExact`),
where `C^{U,V}(X) = smallComplex U V` is the complex of `(U, V)`-small chains.  This is the
short exact sequence underlying the Mayer–Vietoris sequence (Hatcher, *Algebraic Topology*,
§2.2, Mayer–Vietoris sequences); no openness of `U`, `V` is needed at this stage.

## Main results

* `SingularMayerVietoris.toSmall_jointly_surjective` — every small chain is the sum of a chain
  of `U` and a chain of `V`;
* `SingularMayerVietoris.toSmall_overlap_lift` — a chain of `U` and a chain of `V` that agree
  in `X` come from one chain of `U ∩ V`;
* `SingularMayerVietoris.chainSequence_shortExact`.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### The Mayer–Vietoris short complex -/

/-- The left map of the Mayer–Vietoris short complex into small chains. -/
def SingularMayerVietoris.toSmallLeft {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex U ⟶ smallComplex U V :=
  liftToSmall U V (SingularChains.singularChainMap (subtypeInclusion U))
    (fun n c =>
      (show supportedChainSubmodule U n ≤ smallChainSubmodule U V n from le_sup_left)
        (subtypeInclusion_chain_mem U n c))

/-- The right map from small chains to the ambient chains. -/
def SingularMayerVietoris.toSmallRight {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex V ⟶ smallComplex U V :=
  liftToSmall U V (SingularChains.singularChainMap (subtypeInclusion V))
    (fun n c =>
      (show supportedChainSubmodule V n ≤ smallChainSubmodule U V n from le_sup_right)
        (subtypeInclusion_chain_mem V n c))

/-- The left map computes through the intersection inclusions. -/
@[simp]
theorem SingularMayerVietoris.toSmallLeft_inclusion {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    toSmallLeft U V ≫ smallInclusion U V = SingularChains.singularChainMap (subtypeInclusion U) :=
  liftToSmall_inclusion U V _ _

/-- The right map computes the signed sum of inclusions. -/
@[simp]
theorem SingularMayerVietoris.toSmallRight_inclusion {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    toSmallRight U V ≫ smallInclusion U V = SingularChains.singularChainMap (subtypeInclusion V) :=
  liftToSmall_inclusion U V _ _

/-- The two cover inclusions are jointly surjective onto small chains. -/
theorem SingularMayerVietoris.toSmall_jointly_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (s : (smallComplex U V).X n) :
    ∃ x : SingularChains.Chains U n,
      ∃ y : SingularChains.Chains V n,
        ((toSmallLeft U V).f n).hom x + ((toSmallRight U V).f n).hom y = s := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp s.2
  rw [← subtypeInclusion_chain_range U n] at hc
  rw [← subtypeInclusion_chain_range V n] at hd
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hd
  refine ⟨x, y, ?_⟩
  apply Subtype.ext
  change
    SingularChains.inducedChain (subtypeInclusion U) n x +
        SingularChains.inducedChain (subtypeInclusion V) n y =
      s.1
  rw [hx, hy]
  exact hcd

/-- The chain map of the intersection into the left cover. -/
def SingularMayerVietoris.intersectionToLeft {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ SingularChains.singularComplex U :=
  SingularChains.singularChainMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))

/-- The chain map of the intersection into the right cover. -/
def SingularMayerVietoris.intersectionToRight {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ SingularChains.singularComplex V :=
  SingularChains.singularChainMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))

/-- The left intersection map viewed in the ambient chains. -/
theorem SingularMayerVietoris.intersectionToLeft_ambient {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToLeft U V ≫ SingularChains.singularChainMap (subtypeInclusion U) =
      SingularChains.singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.ofHom (subtypeInclusion U))
  exact h.symm

/-- The right intersection map viewed in the ambient chains. -/
theorem SingularMayerVietoris.intersectionToRight_ambient {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToRight U V ≫ SingularChains.singularChainMap (subtypeInclusion V) =
      SingularChains.singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.ofHom (subtypeInclusion V))
  exact h.symm

/-- The left intersection map computes through the subtype inclusion. -/
@[simp]
theorem SingularMayerVietoris.intersectionToLeft_ambient_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (c : SingularChains.Chains (U ∩ V : Set X) n) :
    SingularChains.inducedChain (subtypeInclusion U) n (((intersectionToLeft U V).f n).hom c) =
      SingularChains.inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToLeft_ambient U V)

/-- The right intersection map computes through the subtype inclusion. -/
@[simp]
theorem SingularMayerVietoris.intersectionToRight_ambient_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (c : SingularChains.Chains (U ∩ V : Set X) n) :
    SingularChains.inducedChain (subtypeInclusion V) n (((intersectionToRight U V).f n).hom c) =
      SingularChains.inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToRight_ambient U V)

/-- The left intersection chain map is injective. -/
theorem SingularMayerVietoris.intersectionToLeft_f_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : Function.Injective ((intersectionToLeft U V).f n).hom := by
  intro a b hab
  apply subtypeInclusion_chain_injective (U ∩ V) n
  calc
    _ =
        SingularChains.inducedChain (subtypeInclusion U) n
          (((intersectionToLeft U V).f n).hom a) :=
      (intersectionToLeft_ambient_apply U V n a).symm
    _ =
        SingularChains.inducedChain (subtypeInclusion U) n
          (((intersectionToLeft U V).f n).hom b) :=
      (congrArg (SingularChains.inducedChain (subtypeInclusion U) n) hab)
    _ = _ := intersectionToLeft_ambient_apply U V n b

/-- The two intersection inclusions commute with the cover inclusions. -/
theorem SingularMayerVietoris.intersection_toSmall_comm {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToLeft U V ≫ toSmallLeft U V = intersectionToRight U V ≫ toSmallRight U V := by
  apply (CategoryTheory.cancel_mono (smallInclusion U V)).mp
  simp only [CategoryTheory.Category.assoc, toSmallLeft_inclusion, toSmallRight_inclusion,
    intersectionToLeft_ambient, intersectionToRight_ambient]

/-- A small chain over the overlap lifts to the left. -/
theorem SingularMayerVietoris.toSmall_overlap_lift {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (x : SingularChains.Chains U n) (y : SingularChains.Chains V n)
    (hxy : ((toSmallLeft U V).f n).hom x = ((toSmallRight U V).f n).hom y) :
    ∃ z : SingularChains.Chains (U ∩ V : Set X) n,
      ((intersectionToLeft U V).f n).hom z = x ∧ ((intersectionToRight U V).f n).hom z = y := by
  have hxy' :
    SingularChains.inducedChain (subtypeInclusion U) n x =
      SingularChains.inducedChain (subtypeInclusion V) n y :=
    congrArg (fun s : (smallComplex U V).X n => s.1) hxy
  have hy : SingularChains.inducedChain (subtypeInclusion U) n x ∈ supportedChainSubmodule V n := by
    rw [hxy']
    exact subtypeInclusion_chain_mem V n y
  have hi :
    SingularChains.inducedChain (subtypeInclusion U) n x ∈
      supportedChainSubmodule U n ⊓ supportedChainSubmodule V n :=
    ⟨subtypeInclusion_chain_mem U n x, hy⟩
  rw [supportedChainSubmodule_inf, ← subtypeInclusion_chain_range (U ∩ V) n] at hi
  obtain ⟨z, hz⟩ := hi
  refine ⟨z, ?_, ?_⟩
  · apply subtypeInclusion_chain_injective U n
    rw [intersectionToLeft_ambient_apply]
    exact hz
  · apply subtypeInclusion_chain_injective V n
    rw [intersectionToRight_ambient_apply]
    exact hz.trans hxy'

/-- The middle term of the Mayer–Vietoris short complex. -/
def SingularMayerVietoris.middleComplex {X : Type} [TopologicalSpace X] (U V : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  SingularChains.singularComplex U ⊞ SingularChains.singularComplex V

/-- The left short-complex map `c ↦ (i_* c, −j_* c)`. -/
def SingularMayerVietoris.leftMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ middleComplex U V :=
  CategoryTheory.Limits.biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V))

/-- The right short-complex map `(a, b) ↦ i_* a + j_* b`. -/
def SingularMayerVietoris.rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    middleComplex U V ⟶ smallComplex U V :=
  CategoryTheory.Limits.biprod.desc (toSmallLeft U V) (toSmallRight U V)

/-- The first component of the left map. -/
@[simp]
theorem SingularMayerVietoris.leftMap_fst {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫
        (CategoryTheory.Limits.biprod.fst : middleComplex U V ⟶ SingularChains.singularComplex U) =
      intersectionToLeft U V :=
  CategoryTheory.Limits.biprod.lift_fst _ _

/-- The second component of the left map. -/
@[simp]
theorem SingularMayerVietoris.leftMap_snd {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫
        (CategoryTheory.Limits.biprod.snd : middleComplex U V ⟶ SingularChains.singularComplex V) =
      -(intersectionToRight U V) :=
  CategoryTheory.Limits.biprod.lift_snd _ _

/-- The right map on the left summand is the `U` inclusion. -/
@[simp]
theorem SingularMayerVietoris.inl_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    (CategoryTheory.Limits.biprod.inl : SingularChains.singularComplex U ⟶ middleComplex U V) ≫
        rightMap U V =
      toSmallLeft U V :=
  CategoryTheory.Limits.biprod.inl_desc _ _

/-- The right map on the right summand is the `V` inclusion. -/
@[simp]
theorem SingularMayerVietoris.inr_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    (CategoryTheory.Limits.biprod.inr : SingularChains.singularComplex V ⟶ middleComplex U V) ≫
        rightMap U V =
      toSmallRight U V :=
  CategoryTheory.Limits.biprod.inr_desc _ _

/-- The composite `leftMap ∘ rightMap` is zero. -/
theorem SingularMayerVietoris.leftMap_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫ rightMap U V = 0 := by
  change
    CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.lift _ _)
        (CategoryTheory.Limits.biprod.desc _ _) =
      0
  rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp,
    intersection_toSmall_comm, add_neg_cancel]

/-- The short exact sequence of chain complexes `0 -> C(U cap V) -> C(U) +" C(V) -> C^{U,V}(X) -> 0` underlying the Mayer-Vietoris long exact sequence. -/
def SingularMayerVietoris.chainSequence {X : Type} [TopologicalSpace X] (U V : Set X) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  CategoryTheory.ShortComplex.mk (leftMap U V) (rightMap U V) (leftMap_rightMap U V)

/-- The chain sequence of a two-open cover is short exact: injectivity on the intersection, kernel = image at the sum, and surjectivity onto the small chains (Hatcher, Algebraic Topology, Theorem 2.20). -/
theorem SingularMayerVietoris.chainSequence_shortExact {X : Type} [TopologicalSpace X]
    (U V : Set X) : (chainSequence U V).ShortExact :=
  SmallChainBiprod.shortExactOfComplexes (intersectionToLeft U V) (intersectionToRight U V)
    (toSmallLeft U V) (toSmallRight U V) (intersection_toSmall_comm U V)
    (intersectionToLeft_f_injective U V) (toSmall_jointly_surjective U V)
    (toSmall_overlap_lift U V)
