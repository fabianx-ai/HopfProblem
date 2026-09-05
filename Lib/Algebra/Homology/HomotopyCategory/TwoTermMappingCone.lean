/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# The mapping cone of a single-object morphism

A morphism `f : X ⟶ Y` regarded as a morphism of cochain complexes concentrated in degree zero
has a mapping cone concentrated in degrees `-1` and `0`.  This file constructs that literal
two-term complex with Mathlib's `ConnectData` and gives an exact complex-level isomorphism to the
mapping cone.  The unique nonzero differential is `f`, with no sign.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C} (f : X ⟶ Y)

lemma relNegOneZero : (ComplexShape.up ℤ).Rel (-1) 0 :=
  ComplexShape.up_mk (-1) 0 (by omega)

lemma relZeroOne : (ComplexShape.up ℤ).Rel 0 1 :=
  ComplexShape.up_mk 0 1 (by omega)

/-- A chain complex concentrated in degree zero. -/
abbrev chainSingleZero (X : C) : ChainComplex C ℕ :=
  (HomologicalComplex.single C (ComplexShape.down ℕ) 0).obj X

/-- A natural-number-indexed cochain complex concentrated in degree zero. -/
abbrev cochainSingleZero (X : C) : CochainComplex C ℕ :=
  (HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj X

/-- Connect the degree-zero chain single on `X` to the degree-zero cochain single on `Y` by
`f`. -/
noncomputable def twoTermData : ConnectData (chainSingleZero X) (cochainSingleZero Y) where
  d₀ := f
  comp_d₀ := zero_comp
  d₀_comp := comp_zero

/-- The integer-indexed complex with `X` in degree `-1`, `Y` in degree `0`, and differential
`f`. -/
abbrev twoTerm : CochainComplex C ℤ := (twoTermData f).cochainComplex

lemma twoTerm_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((twoTerm f).X i) := by
  rcases i with (n | n)
  · change IsZero ((cochainSingleZero Y).X n)
    apply HomologicalComplex.isZero_single_obj_X
    intro hn
    subst n
    exact hzero rfl
  · change IsZero ((chainSingleZero X).X n)
    apply HomologicalComplex.isZero_single_obj_X
    intro hn
    subst n
    exact hneg rfl

lemma mappingCone_single_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((mappingCone ((singleFunctor C 0).map f)).X i) := by
  rw [mappingCone.isZero_X_iff]
  constructor
  · apply HomologicalComplex.isZero_single_obj_X
    omega
  · apply HomologicalComplex.isZero_single_obj_X
    exact hzero

noncomputable def twoTermPointIsoNegOne :
    (twoTerm f).X (-1) ≅ (mappingCone ((singleFunctor C 0).map f)).X (-1) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X ≪≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm ≪≫
    isoBiprodZero (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 Y (-1) (by omega)) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((singleFunctor C 0).map f) (-1) 0 relNegOneZero).symm

noncomputable def twoTermPointIsoZero :
    (twoTerm f).X 0 ≅ (mappingCone ((singleFunctor C 0).map f)).X 0 :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Y ≪≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).symm ≪≫
    isoZeroBiprod (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 X 1 (by omega)) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((singleFunctor C 0).map f) 0 1 relZeroOne).symm

noncomputable def twoTermPointIso (i : ℤ) :
    (twoTerm f).X i ≅ (mappingCone ((singleFunctor C 0).map f)).X i := by
  by_cases hneg : i = -1
  · subst i
    exact twoTermPointIsoNegOne f
  by_cases hzero : i = 0
  · subst i
    exact twoTermPointIsoZero f
  exact IsZero.iso (twoTerm_isZero_X f i hneg hzero)
    (mappingCone_single_isZero_X f i hneg hzero)

set_option backward.isDefEq.respectTransparency false

lemma twoTermPointIsoNegOne_hom :
    (twoTermPointIso f (-1)).hom =
      (mappingCone.inl ((singleFunctor C 0).map f)).v 0 (-1) (by omega) := by
  change (twoTermPointIsoNegOne f).hom = _
  dsimp [twoTermPointIsoNegOne, isoBiprodZero, mappingCone.inl,
    HomologicalComplex.homotopyCofiber.inlX,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  change 𝟙 X ≫ 𝟙 X ≫ biprod.inl ≫ _ = _
  simp only [Category.id_comp]
  rfl

lemma twoTermPointIsoZero_hom :
    (twoTermPointIso f 0).hom =
      (mappingCone.inr ((singleFunctor C 0).map f)).f 0 := by
  change (twoTermPointIsoZero f).hom = _
  change (twoTermPointIsoZero f).hom =
    HomologicalComplex.homotopyCofiber.inrX ((singleFunctor C 0).map f) 0
  rw [← cancel_mono (HomologicalComplex.homotopyCofiber.XIsoBiprod
    ((singleFunctor C 0).map f) 0 1 relZeroOne).hom]
  dsimp [twoTermPointIsoZero, isoZeroBiprod,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change 𝟙 Y ≫ 𝟙 Y ≫ biprod.inr = _
  simp only [Category.id_comp]
  exact (HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom
    ((singleFunctor C 0).map f) 1 0 relZeroOne).symm

/-- The literal two-term complex on `f` is isomorphic to the mapping cone of the corresponding
morphism between degree-zero single complexes.  On the unique nonzero differential the
commuting-square obligation reduces to `mappingCone.inl_v_d`, and the resulting map is `f`
rather than `-f`. -/
noncomputable def twoTermIsoMappingCone :
    twoTerm f ≅ mappingCone ((singleFunctor C 0).map f) :=
  Hom.isoOfComponents (twoTermPointIso f) (by
    rintro i _ rfl
    by_cases hi : i = -1
    · subst i
      change (twoTermPointIso f (-1)).hom ≫
        (mappingCone ((singleFunctor C 0).map f)).d (-1) 0 =
        f ≫ (twoTermPointIso f 0).hom
      erw [twoTermPointIsoNegOne_hom, twoTermPointIsoZero_hom]
      rw [mappingCone.inl_v_d _ 0 (-1) 1 (by omega) (by omega)]
      dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single]
      simp
    by_cases hi' : i = -2
    · apply (twoTerm_isZero_X f i (by omega) (by omega)).eq_of_src
    · apply (mappingCone_single_isZero_X f (i + 1) (by omega) (by omega)).eq_of_tgt)

end CochainComplex
