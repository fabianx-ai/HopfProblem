/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyLongExact

/-!
# The long exact homology sequence through a biproduct

For chain complexes `K`, `L` of `ℤ`-modules, the homology of the biproduct `K ⊞ L` is the
product of the homologies (`homologyBiprodEquiv K L n : H_n(K ⊞ L) ≃ₗ[ℤ] H_n K × H_n L`).  For a
short exact sequence `0 → A → K ⊞ L → B → 0` the long exact homology sequence is rewritten with
middle term `H_n K × H_n L` (`biprodSequenceFirstMap`, `biprodSequenceSecondMap`) and the three
exactness statements `biprodSequence_exact_at_leftHomology`, `_middleHomology`,
`_rightHomology`; this is the shape in which the Mayer–Vietoris sequence
`… → H_n(U ∩ V) → H_n U ⊕ H_n V → H_n X → …` is read (Hatcher, *Algebraic Topology*, §2.2).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

universe u

/-! ### Homology of the short complex -/

/-- The left component of an `inl` homology class. -/
theorem SingularMayerVietoris.homology_fst_inl
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (a : K.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          a) =
      a := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.fst n
  rw [CategoryTheory.Limits.biprod.inl_fst, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

/-- The right component of an `inl` homology class. -/
theorem SingularMayerVietoris.homology_snd_inl
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (a : K.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          a) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.snd n
  rw [CategoryTheory.Limits.biprod.inl_snd, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

/-- The left component of an `inr` homology class. -/
theorem SingularMayerVietoris.homology_fst_inr
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (b : L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          b) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.fst n
  rw [CategoryTheory.Limits.biprod.inr_fst, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom b) h).symm

/-- The right component of an `inr` homology class. -/
theorem SingularMayerVietoris.homology_snd_inr
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (b : L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          b) =
      b := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.snd n
  rw [CategoryTheory.Limits.biprod.inr_snd, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom b) h).symm

/-- Every pair-homology class splits into `inl` and `inr` parts. -/
theorem SingularMayerVietoris.homology_biprod_total
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (a : (K ⊞ L).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
            a) +
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
            a) =
      a := by
  have h :
    HomologicalComplex.homologyMap
        (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst
              CategoryTheory.Limits.biprod.inl +
            CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.snd
              CategoryTheory.Limits.biprod.inr :
          K ⊞ L ⟶ K ⊞ L)
        n =
      𝟙 ((K ⊞ L).homology n) := by
    rw [CategoryTheory.Limits.biprod.total, HomologicalComplex.homologyMap_id]
  rw [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun f => f.hom a) h

/-! ### Homology of a bipod sequence -/

/-- Homology of a bipod complex is the product of homologies. -/
def SingularMayerVietoris.homologyBiprodEquiv (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≃ₗ[ℤ] (K.homology n × L.homology n) :=
  ({    toFun
          a :=
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
              a,
            (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
              a)
        invFun
          a :=
          (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
              a.1 +
            (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
              a.2
        left_inv := homology_biprod_total K L n
        right_inv
          a := by
          apply Prod.ext
          · change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K)
                      n).hom
                  ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
                          n).hom
                      a.1 +
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
                          n).hom
                      a.2) =
                a.1
            rw [map_add, homology_fst_inl, homology_fst_inr, add_zero]
          · change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L)
                      n).hom
                  ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
                          n).hom
                      a.1 +
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
                          n).hom
                      a.2) =
                a.2
            rw [map_add, homology_snd_inl, homology_snd_inr, zero_add]
        map_add' a
          b := by
          change (_, _) = (_, _)
          rw [map_add, map_add] } :
      (K ⊞ L).homology n ≃+ (K.homology n × L.homology n)).toIntLinearEquiv

/-- The inverse equivalence computes the pair class. -/
theorem SingularMayerVietoris.homologyBiprodEquiv_symm_apply
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (a : K.homology n × L.homology n) :
    (homologyBiprodEquiv K L n).symm a =
      (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          a.2 :=
  rfl

/-- The equivalence descends a pair of homology maps. -/
theorem SingularMayerVietoris.homologyBiprodEquiv_desc {K : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (n : ℕ) {A : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ A) (g : L ⟶ A) (a : K.homology n × L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.desc f g) n).hom
        ((homologyBiprodEquiv K L n).symm a) =
      (HomologicalComplex.homologyMap f n).hom a.1 +
        (HomologicalComplex.homologyMap g n).hom a.2 := by
  rw [homologyBiprodEquiv_symm_apply, map_add]
  congr 1
  · have h :=
      HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
        (CategoryTheory.Limits.biprod.desc f g) n
    rw [CategoryTheory.Limits.biprod.inl_desc] at h
    exact (congrArg (fun k => k.hom a.1) h).symm
  · have h :=
      HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
        (CategoryTheory.Limits.biprod.desc f g) n
    rw [CategoryTheory.Limits.biprod.inr_desc] at h
    exact (congrArg (fun k => k.hom a.2) h).symm

/-- The first map of the bipod sequence. -/
def SingularMayerVietoris.biprodSequenceFirstMap {A K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : A ⟶ K ⊞ L) (n : ℕ) : A.homology n →ₗ[ℤ] (K.homology n × L.homology n) :=
  (homologyBiprodEquiv K L n).toLinearMap.comp (homologyLinearMap f n)

/-- The second map of the bipod sequence. -/
def SingularMayerVietoris.biprodSequenceSecondMap {K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (g : K ⊞ L ⟶ B) (n : ℕ) : (K.homology n × L.homology n) →ₗ[ℤ] B.homology n :=
  (homologyLinearMap g n).comp (homologyBiprodEquiv K L n).symm.toLinearMap

/-- The second map descends the two components. -/
theorem SingularMayerVietoris.biprodSequenceSecondMap_desc
    {K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ B) (g : L ⟶ B) (n : ℕ)
    (a : K.homology n × L.homology n) :
    biprodSequenceSecondMap (CategoryTheory.Limits.biprod.desc f g) n a =
      homologyLinearMap f n a.1 + homologyLinearMap g n a.2 :=
  homologyBiprodEquiv_desc n f g a

/-- The bipod sequence is exact at the left term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_leftHomology
    {A K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (connectingMap hS n) = LinearMap.ker (biprodSequenceFirstMap f n) := by
  rw [exact_at_leftHomology hS n]
  ext a
  change homologyLinearMap f n a = 0 ↔ homologyBiprodEquiv K L n (homologyLinearMap f n a) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (homologyBiprodEquiv K L n).injective (h.trans (map_zero _).symm)

/-- The bipod sequence is exact at the middle term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_middleHomology
    {A K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (biprodSequenceFirstMap f n) = LinearMap.ker (biprodSequenceSecondMap g n) := by
  ext a
  change
    (∃ b, homologyBiprodEquiv K L n (homologyLinearMap f n b) = a) ↔
      homologyLinearMap g n ((homologyBiprodEquiv K L n).symm a) = 0
  constructor
  · rintro ⟨b, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hb : homologyLinearMap f n b ∈ LinearMap.range (homologyLinearMap f n) := ⟨b, rfl⟩
    rw [exact_at_middleHomology hS n] at hb
    exact hb
  · intro ha
    have hb : (homologyBiprodEquiv K L n).symm a ∈ LinearMap.range (homologyLinearMap f n) := by
      rw [exact_at_middleHomology hS n]
      exact ha
    obtain ⟨b, hb⟩ := hb
    exact
      ⟨b,
        (congrArg (homologyBiprodEquiv K L n) hb).trans
          ((homologyBiprodEquiv K L n).apply_symm_apply a)⟩

/-- The bipod sequence is exact at the right term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_rightHomology
    {A K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (biprodSequenceSecondMap g (n + 1)) = LinearMap.ker (connectingMap hS n) := by
  rw [← exact_at_rightHomology hS n]
  ext b
  change
    (∃ a, homologyLinearMap g (n + 1) ((homologyBiprodEquiv K L (n + 1)).symm a) = b) ↔
      ∃ a, homologyLinearMap g (n + 1) a = b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(homologyBiprodEquiv K L (n + 1)).symm a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨homologyBiprodEquiv K L (n + 1) a, ?_⟩
    rwa [LinearEquiv.symm_apply_apply]

/-- The degree-zero second map is surjective. -/
theorem SingularMayerVietoris.biprodSequence_second_zero_surjective
    {A K L B : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) :
    Function.Surjective (biprodSequenceSecondMap g 0) :=
  (homologyLinearMap_second_zero_surjective hS).comp (homologyBiprodEquiv K L 0).symm.surjective
