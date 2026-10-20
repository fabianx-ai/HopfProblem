/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Additivity of the computed right-derived functors

Each right derived functor `Rⁿ F` of an additive functor into abelian groups is again
additive, and a natural isomorphism `F ≅ G` induces a natural isomorphism `Rⁿ F ≅ Rⁿ G`
compatible with the degree-zero identification `R⁰ F ≅ F` for left exact `F`.

Weibel, *An Introduction to Homological Algebra*, §2.4 (right derived functors of an additive
functor; the section numbers of the individual statements are not reproduced here).
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory
open HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Functor

/-- Every right derived functor `Rⁿ F` of an additive functor `F : A ⥤ AddCommGrpCat` is
again additive: `Rⁿ F (f + g) = Rⁿ F f + Rⁿ F g` (cf. Weibel §2.4).
-/
instance rightDerived_additive {A : Type u} [Category.{v} A] [Abelian A]
    [HasInjectiveResolutions A] (F : A ⥤ AddCommGrpCat.{w}) [F.Additive]
    (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    let s := InjectiveResolution.desc f J I
    let t := InjectiveResolution.desc g J I
    have hs : I.ι ≫ s = (CochainComplex.single₀ A).map f ≫ J.ι :=
      InjectiveResolution.desc_commutes f J I
    have ht : I.ι ≫ t = (CochainComplex.single₀ A).map g ≫ J.ι :=
      InjectiveResolution.desc_commutes g J I
    have hsum : I.ι ≫ (s + t) =
        (CochainComplex.single₀ A).map (f + g) ≫ J.ι := by
      simp [Preadditive.comp_add, Preadditive.add_comp, hs, ht]
    rw [F.rightDerived_map_eq n (f + g) (s + t) hsum,
      F.rightDerived_map_eq n f s hs, F.rightDerived_map_eq n g t ht]
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

end CategoryTheory.Functor

end
end

public section
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.NatIso

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]

/-- A natural isomorphism `α : F ≅ G` of additive functors induces a natural isomorphism
`Rⁿ α : Rⁿ F ≅ Rⁿ G` in every right-derived degree (cf. Weibel §2.4). -/
noncomputable def rightDerived (α : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

/-- The forward map of `Rⁿ α` is the derived natural transformation `Rⁿ (α.hom)`. -/
theorem rightDerived_hom (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).hom = NatTrans.rightDerived α.hom n := by
  unfold rightDerived
  rfl

/-- The inverse map of `Rⁿ α` is the derived natural transformation `Rⁿ (α.inv)`. -/
theorem rightDerived_inv (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).inv = NatTrans.rightDerived α.inv n := by
  unfold rightDerived
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For left exact `F` and `G`, the isomorphism `R⁰ α` commutes with the canonical
identifications `R⁰ F ≅ F` and `R⁰ G ≅ G`: `R⁰ α ≫ (R⁰G ≅ G) = (R⁰F ≅ F) ≫ α`
(cf. Weibel §2.4). -/
theorem rightDerived_zero_hom [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) :
    (rightDerived α 0).hom ≫ G.rightDerivedZeroIsoSelf.hom =
      F.rightDerivedZeroIsoSelf.hom ≫ α.hom := by
  have hcycles {A : C} (I : InjectiveResolution A) :
      α.hom.app A ≫ I.toRightDerivedZero' G =
        I.toRightDerivedZero' F ≫
          cyclesMap ((NatTrans.mapHomologicalComplex α.hom (.up ℕ)).app I.cocomplex) 0 := by
    rw [← cancel_mono (iCycles ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) 0)]
    rw [Category.assoc, Category.assoc, cyclesMap_i,
      I.toRightDerivedZero'_comp_iCycles G, ← Category.assoc,
      I.toRightDerivedZero'_comp_iCycles F]
    exact (α.hom.naturality (I.ι.f 0)).symm
  have hunit : F.toRightDerivedZero ≫ NatTrans.rightDerived α.hom 0 =
      α.hom ≫ G.toRightDerivedZero := by
    apply NatTrans.ext
    funext A
    let I := injectiveResolution A
    rw [NatTrans.comp_app, NatTrans.comp_app,
      I.toRightDerivedZero_eq F, I.toRightDerivedZero_eq G,
      I.rightDerived_app_eq α.hom 0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change I.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
        homologyMap ((NatTrans.mapHomologicalComplex α.hom (.up ℕ)).app I.cocomplex) 0 ≫
        (I.isoRightDerivedObj G 0).inv = _
    rw [← Category.assoc _ (homologyMap _ 0), homologyπ_naturality]
    rw [← Category.assoc, ← Category.assoc, ← hcycles I]
    rfl
  rw [rightDerived_hom, ← cancel_epi F.toRightDerivedZero]
  rw [← Category.assoc, hunit, Category.assoc,
    G.rightDerivedZeroIsoSelf_inv_hom_id, Category.comp_id,
    ← Category.assoc, F.rightDerivedZeroIsoSelf_inv_hom_id, Category.id_comp]

end CategoryTheory.NatIso
