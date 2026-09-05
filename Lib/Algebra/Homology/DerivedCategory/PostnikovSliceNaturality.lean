/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovSlice

/-!
# Naturality of the normalized single-homology comparison
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The chosen comparison from a single-degree derived object to its homology single is
normalized to induce the identity on degree-`n` homology. -/
@[reassoc]
theorem homologyFunctor_map_isoSingleFunctorHomology_hom (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    (homologyFunctor C n).map (isoSingleFunctorHomology K n).hom ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app
          ((homologyFunctor C n).obj K) =
      𝟙 ((homologyFunctor C n).obj K) := by
  let Y := (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose
  let e : K ≅ (singleFunctor C n).obj Y :=
    (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose_spec.some
  let hY : (homologyFunctor C n).obj K ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app Y
  change (homologyFunctor C n).map
      (e.hom ≫ (singleFunctor C n).map hY.inv) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app _ = 𝟙 _
  rw [Functor.map_comp, Category.assoc,
    ← Functor.comp_map, (singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc]
  change hY.hom ≫ hY.inv = 𝟙 _
  simp

/-- Degree-`n` homology is faithful on the image of the degree-`n` single functor. -/
theorem homologyFunctor_map_injective_singleFunctor (A B : C) (n : ℤ) :
    Function.Injective (fun f : (singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B ↦
      (homologyFunctor C n).map f) := by
  intro f g h
  suffices hp :
      (singleFunctor C n).preimage f = (singleFunctor C n).preimage g by
    rw [← (singleFunctor C n).map_preimage f,
      ← (singleFunctor C n).map_preimage g, hp]
  apply (cancel_epi
    ((singleFunctorCompHomologyFunctorIso C n).hom.app A)).mp
  calc
    (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫
        (singleFunctor C n).preimage f =
      (singleFunctor C n ⋙ homologyFunctor C n).map
          ((singleFunctor C n).preimage f) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
          simpa only [Functor.id_map] using
            ((singleFunctorCompHomologyFunctorIso C n).hom.naturality
              ((singleFunctor C n).preimage f)).symm
    _ = (homologyFunctor C n).map f ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      simp only [Functor.comp_map, (singleFunctor C n).map_preimage]
    _ = (homologyFunctor C n).map g ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      change (homologyFunctor C n).map f = (homologyFunctor C n).map g at h
      rw [h]
    _ = (singleFunctor C n ⋙ homologyFunctor C n).map
          ((singleFunctor C n).preimage g) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      simp only [Functor.comp_map, (singleFunctor C n).map_preimage]
    _ = (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫
        (singleFunctor C n).preimage g := by
      simpa only [Functor.id_map] using
        (singleFunctorCompHomologyFunctorIso C n).hom.naturality
          ((singleFunctor C n).preimage g)

/-- Degree-`n` homology detects morphisms between objects concentrated in degree `n`. -/
theorem homologyFunctor_map_injective_of_isGE_of_isLE
    (K L : DerivedCategory C) (n : ℤ) [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] :
    Function.Injective (fun f : K ⟶ L ↦ (homologyFunctor C n).map f) := by
  intro f g h
  change (homologyFunctor C n).map f = (homologyFunctor C n).map g at h
  apply (cancel_epi (isoSingleFunctorHomology K n).inv).mp
  apply (cancel_mono (isoSingleFunctorHomology L n).hom).mp
  apply homologyFunctor_map_injective_singleFunctor
  simp only [Functor.map_comp, h]

/-- The normalized comparison with the degree-`n` single homology object is natural on
objects concentrated in degree `n`. -/
@[reassoc]
theorem isoSingleFunctorHomology_hom_naturality
    {K L : DerivedCategory C} (n : ℤ) [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n]
    (f : K ⟶ L) :
    (isoSingleFunctorHomology K n).hom ≫
        (singleFunctor C n).map ((homologyFunctor C n).map f) =
      f ≫ (isoSingleFunctorHomology L n).hom := by
  apply homologyFunctor_map_injective_of_isGE_of_isLE K _ n
  apply (cancel_mono
    ((singleFunctorCompHomologyFunctorIso C n).hom.app
      ((homologyFunctor C n).obj L))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map,
    (singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map,
    homologyFunctor_map_isoSingleFunctorHomology_hom_assoc,
    homologyFunctor_map_isoSingleFunctorHomology_hom,
    Category.comp_id]

end DerivedCategory
