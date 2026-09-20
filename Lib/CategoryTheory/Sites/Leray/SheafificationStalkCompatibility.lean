/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

import Lib.Algebra.Homology.FunctorCoherence
public import Lib.CategoryTheory.Sites.Leray.HigherDirectImageSheafification
public import Lib.Topology.Sheaves.SheafificationLocal

/-!
# Compatibility of sheafification with the resolution stalk model

Sheafification does not change stalks: the unit `P ⟶ P⁺` induces an isomorphism `P_x ≅ (P⁺)_x`
(Hartshorne, *Algebraic Geometry*, II.1.2; Godement, *Topologie algébrique et théorie des
faisceaux*, II.1.2).  Consequently the two descriptions of the stalk of `Rⁿf_*F` — the one coming
from the sheafification statement `Rⁿf_*F = (U ↦ Hⁿ(Γ(f⁻¹U, I)))⁺` of Hartshorne III.8.1, and the
one coming from exactness of the stalk functor applied to the complex `f_*I` — give the same
isomorphism.

These are categorical coherence statements.  They neither assert proper base change nor identify
a higher-direct-image stalk with the cohomology of a geometric fibre.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf.Leray

variable {X Y : TopCat.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map `P_y ⟶ (P⁺)_y` induced by the sheafification unit, natural in the presheaf.
It is an isomorphism (Hartshorne II.1.2). -/
def stalkSheafificationUnitNatTrans (y : Y) :
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ⟶
      TopCat.Sheaf.sheafification Y ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y where
  app P := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    (TopCat.SheafificationLocal.unit P)
  naturality {P Q} η := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map η ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (TopCat.SheafificationLocal.unit Q) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (TopCat.SheafificationLocal.unit P) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map ((TopCat.Sheaf.sheafification Y).map η))
    rw [← (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map_comp,
      ← (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map_comp]
    apply (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).congr_map
    change η ≫ CategoryTheory.toSheafify (Opens.grothendieckTopology Y) Q =
      CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P ≫
        CategoryTheory.sheafifyMap (Opens.grothendieckTopology Y) η
    exact CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology Y) η

/-- Componentwise, `stalkSheafificationUnitNatTrans` is the stalk map induced by the
sheafification unit of the presheaf. -/
@[simp]
theorem stalkSheafificationUnitNatTrans_app (y : Y)
    (P : TopCat.Presheaf AddCommGrpCat.{u} Y) :
    (stalkSheafificationUnitNatTrans y).app P =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (TopCat.SheafificationLocal.unit P) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Applying stalks after sheafification has the expected two-step homology comparison. -/
theorem mapComplexHomologyIso_sheafification_stalk_comp
    (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} Y) ℕ) (n : ℕ) (y : Y) :
    mapComplexHomologyIso P
      (TopCat.Sheaf.sheafification Y ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n =
      mapComplexHomologyIso
          (((TopCat.Sheaf.sheafification Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj P)
          (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n ≪≫
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
            (mapComplexHomologyIso P (TopCat.Sheaf.sheafification Y) n) := by
  dsimp only [mapComplexHomologyIso]
  exact ShortComplex.mapHomologyIso_comp
    (TopCat.Sheaf.sheafification Y)
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) (P.sc n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying complex map from a sheaf complex to the sheafification of its underlying
presheaf complex is the degreewise sheafification unit. -/
theorem sheafificationComplexIso_symm_hom_underlying
    (K : CochainComplex (AbelianSheaf Y) ℕ) :
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (sheafificationComplexIso K).symm.hom =
      (NatTrans.mapHomologicalComplex
        (CategoryTheory.toSheafification
          (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (ComplexShape.up ℕ)).app (underlyingPresheafComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
      ((sheafificationComplexIso K).symm.hom.f n) =
    CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((underlyingPresheafComplex K).X n)
  have h : (sheafificationComplexIso K).symm.hom.f n =
      (CategoryTheory.sheafificationNatIso
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).hom.app (K.X n) := by
    dsimp [sheafificationComplexIso, sheafificationUnderlyingIso]
    rw [Category.id_comp]
  rw [h]
  exact CategoryTheory.sheafificationNatIso_hom_app_hom
    (Opens.grothendieckTopology Y) AddCommGrpCat.{u} (K.X n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical stalk--homology comparison carries the sheafification unit to the
stalk of the canonical homology-sheaf sheafification comparison. -/
theorem stalkHomologyPresheafIso_hom_comp_sheafificationUnit
    (K : CochainComplex (AbelianSheaf Y) ℕ) (n : ℕ) (y : Y) :
    (stalkHomologyPresheafIso y K n).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (TopCat.SheafificationLocal.unit (homologyPresheaf K n)) =
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
          (sheafHomologyIsoSheafification K n)).hom := by
  dsimp [stalkHomologyPresheafIso, sheafHomologyIsoSheafification]
  rw [← cancel_epi (mapComplexHomologyIso K
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hnat :
      ShortComplex.homologyMap
          (((underlyingPresheafComplex K).sc n).mapNatTrans
            (stalkSheafificationUnitNatTrans y)) ≫
        (mapComplexHomologyIso (underlyingPresheafComplex K)
          (TopCat.Sheaf.sheafification Y ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n).hom =
      (mapComplexHomologyIso (underlyingPresheafComplex K)
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (TopCat.SheafificationLocal.unit (homologyPresheaf K n)) := by
    exact ShortComplex.mapHomologyIso_hom_naturality_natTrans
      ((underlyingPresheafComplex K).sc n) (stalkSheafificationUnitNatTrans y)
  rw [← hnat]
  rw [mapComplexHomologyIso_sheafification_stalk_comp]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  have hmap :
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (mapComplexHomologyIso (underlyingPresheafComplex K)
            (TopCat.Sheaf.sheafification Y) n).hom =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
            (mapComplexHomologyIso (underlyingPresheafComplex K)
              (TopCat.Sheaf.sheafification Y) n).hom) := rfl
  rw [hmap]
  simp only [← Category.assoc]
  rw [cancel_mono]
  have hcomplex :
      (NatTrans.mapHomologicalComplex (stalkSheafificationUnitNatTrans y)
          (ComplexShape.up ℕ)).app (underlyingPresheafComplex K) =
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (sheafificationComplexIso K).symm.hom := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (TopCat.SheafificationLocal.unit ((underlyingPresheafComplex K).X i)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
          ((sheafificationComplexIso K).symm.hom.f i))
    apply (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).congr_map
    have hi := congrArg (fun q => q.f i)
      (sheafificationComplexIso_symm_hom_underlying K)
    exact hi.symm
  have hhom :
      ShortComplex.homologyMap
          (((underlyingPresheafComplex K).sc n).mapNatTrans
            (stalkSheafificationUnitNatTrans y)) =
        HomologicalComplex.homologyMap
          (((TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapHomologicalComplex
              (ComplexShape.up ℕ)).map
                (sheafificationComplexIso K).symm.hom) n := by
    change HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (stalkSheafificationUnitNatTrans y)
          (ComplexShape.up ℕ)).app (underlyingPresheafComplex K)) n = _
    rw [hcomplex]
  rw [hhom]
  exact mapComplexHomologyIso_hom_naturality
    (sheafificationComplexIso K).symm.hom
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) n

/-- The stalk comparison obtained by applying stalks to the resolution-sheafification theorem
and then undoing the sheafification unit on the presheaf stalk. -/
def higherDirectImageResolutionSheafificationStalkIso
    (f : X ⟶ Y) (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F n).obj y ≅
      TopCat.Presheaf.stalk (homologyPresheaf (pushedResolution f I) n) y :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
        (higherDirectImageResolutionSheafificationIso f F I n)).trans
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (TopCat.SheafificationLocal.unit
        (homologyPresheaf (pushedResolution f I) n)))).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification-induced stalk comparison is the canonical resolution-stalk comparison. -/
theorem higherDirectImageResolutionSheafificationStalkIso_eq
    (f : X ⟶ Y) (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    higherDirectImageResolutionSheafificationStalkIso f F I n y =
      higherDirectImageResolutionStalkIso f F I n y := by
  apply Iso.ext
  dsimp [higherDirectImageResolutionSheafificationStalkIso,
    higherDirectImageResolutionSheafificationIso,
    higherDirectImageResolutionStalkIso]
  rw [(TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map_comp,
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map_comp]
  change
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (higherDirectImageResolutionIso f F I n).hom ≫
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (sheafHomologyIsoSheafification (pushedResolution f I) n).hom ≫
      inv ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (TopCat.SheafificationLocal.unit
          (homologyPresheaf (pushedResolution f I) n))) =
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (higherDirectImageResolutionIso f F I n).hom ≫
      (stalkHomologyPresheafIso y (pushedResolution f I) n).hom
  rw [cancel_epi]
  have hs :
      (stalkHomologyPresheafIso y (pushedResolution f I) n).hom ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (TopCat.SheafificationLocal.unit
              (homologyPresheaf (pushedResolution f I) n)) =
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (sheafHomologyIsoSheafification (pushedResolution f I) n).hom := by
    exact stalkHomologyPresheafIso_hom_comp_sheafificationUnit
      (pushedResolution f I) n y
  rw [← hs]
  simp

end CategoryTheory.Sheaf.Leray
