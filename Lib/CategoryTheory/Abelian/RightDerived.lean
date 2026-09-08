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

The usual injective-resolution computation gives additive degree functors.
This module retains the existing derived objects and coefficient maps.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory
open HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Functor

/-- Each right-derived degree of an additive abelian-group-valued functor is additive.

Choose the same source and target injective resolutions for two coefficient maps.
The sum of their comparisons extends the sum of the coefficient maps. Compute all
three derived maps using these comparisons; additivity of complex homology and
bilinearity of composition give the sum law on the existing derived family.
Identity and composition are existing functor laws; zero and negatives follow
from this additive instance. This is the PD-L04 comparison-sum argument.
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

/-- A natural isomorphism of additive functors induces an isomorphism in each
right-derived degree. On a common injective resolution, its forward and inverse
maps are the original natural-isomorphism components applied termwise, followed
by cohomology. Naturality along differentials makes these cochain maps, and
naturality along resolution comparisons makes the resulting maps independent
of the computation and natural in the coefficient object (textbook M09). -/
noncomputable def rightDerived (α : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

/-- The forward derived transport is the original derived natural transformation.
Together with `InjectiveResolution.rightDerived_app_eq`, this computes it on
every original injective resolution as the homology of the forward cochain map,
conjugated by the two resolution-computation isomorphisms. -/
theorem rightDerived_hom (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).hom = NatTrans.rightDerived α.hom n := by
  unfold rightDerived
  rfl

/-- The inverse derived transport is induced by the original inverse natural
transformation, on the same resolution. Its computation therefore uses the
inverse cochain map and the resolution-computation isomorphisms in reverse order,
not a separately chosen equivalence between the derived objects. -/
theorem rightDerived_inv (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).inv = NatTrans.rightDerived α.inv n := by
  unfold rightDerived
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Derived transport commutes with the canonical degree-zero identifications
for left-exact functors. The square is fixed by the original augmentation:
naturality there gives the square on degree-zero cycles; the homology projection
and resolution-computation maps give the square on the canonical zero units.
Cancelling those units gives this normalization. Thus no new choice of a
degree-zero equivalence is made (textbook M09, the same kernel factorization). -/
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
