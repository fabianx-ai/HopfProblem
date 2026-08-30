/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Stalk

/-!
# Comparing a sheaf with a principal-cover local system

This file packages the textbook descent step from a deck-equivariant, locally constant family of
stalk maps to a morphism into the associated local system.  The induced morphism on each stalk,
followed by evaluation at a chosen lift, is the supplied stalk map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology

namespace PrincipalCoverLocalSystem

universe uG u

variable {G : Type uG} {E X M : Type u}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E] [AddCommGroup M] [DistribMulAction G M]

/-- Data for comparing a sheaf with the local system associated to a principal cover.

The two compatibility fields say precisely that applying the stalk maps to the germs of one
section produces a locally constant, deck-equivariant function on the lifted open set. -/
structure StalkComparisonData (p : E → X) (hp : IsQuotientCoveringMap p G)
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)) where
  /-- The comparison at every chosen lift. -/
  stalkMap : ∀ e : E, F.presheaf.stalk (p e) ⟶ AddCommGrpCat.of M
  /-- Germwise comparison of a section is locally constant on the lifted open set. -/
  section_isLocallyConstant : ∀ (U : Opens X) (s : F.obj.obj (op U)),
    IsLocallyConstant fun e : LiftedOpen p U ↦
      stalkMap e.1 (F.presheaf.germ U (p e.1) e.2 s)
  /-- The germwise comparison obeys the deck-equivariance law. -/
  section_equivariant : ∀ (U : Opens X) (s : F.obj.obj (op U))
      (g : G) (e : LiftedOpen p U),
    stalkMap (g • e.1)
        (F.presheaf.germ U (p (g • e.1))
          (by simpa only [hp.map_smul] using e.2) s) =
      g • stalkMap e.1 (F.presheaf.germ U (p e.1) e.2 s)

namespace StalkComparisonData

variable {p : E → X} {hp : IsQuotientCoveringMap p G}
  {F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)}

/-- The associated equivariant local-system section. -/
def toSection (D : StalkComparisonData (M := M) p hp F) (U : Opens X)
    (s : F.obj.obj (op U)) : equivariantSections (M := M) p hp U :=
  ⟨⟨fun e ↦ D.stalkMap e.1 (F.presheaf.germ U (p e.1) e.2 s),
      D.section_isLocallyConstant U s⟩,
    D.section_equivariant U s⟩

/-- The additive map on sections induced by the stalk comparison. -/
def sectionMap (D : StalkComparisonData (M := M) p hp F) (U : Opens X) :
    F.obj.obj (op U) ⟶ (presheaf (M := M) p hp).obj (op U) :=
  AddCommGrpCat.ofHom
    { toFun := D.toSection U
      map_zero' := by
        apply Subtype.ext
        apply LocallyConstant.ext
        intro e
        change D.stalkMap e.1
            (F.presheaf.germ U (p e.1) e.2 0) = 0
        simp
      map_add' := by
        intro s t
        apply Subtype.ext
        apply LocallyConstant.ext
        intro e
        change D.stalkMap e.1
            (F.presheaf.germ U (p e.1) e.2 (s + t)) =
          D.stalkMap e.1 (F.presheaf.germ U (p e.1) e.2 s) +
            D.stalkMap e.1 (F.presheaf.germ U (p e.1) e.2 t)
        simp }

/-- The presheaf morphism induced by a locally constant equivariant family of stalk maps. -/
def presheafHom (D : StalkComparisonData (M := M) p hp F) :
    F.presheaf ⟶ presheaf (M := M) p hp where
  app U := D.sectionMap (unop U)
  naturality := by
    intro U V i
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro e
    simp only [sectionMap]
    change D.stalkMap e.1
        (F.presheaf.germ (unop V) (p e.1) e.2 (F.presheaf.map i s)) =
      D.stalkMap e.1
        (F.presheaf.germ (unop U) (p e.1) (i.unop.le e.2) s)
    rw [F.presheaf.germ_res_apply' i]

/-- The sheaf morphism induced by a locally constant equivariant family of stalk maps. -/
def hom (D : StalkComparisonData (M := M) p hp F) :
    F ⟶ sheaf (M := M) p hp :=
  ObjectProperty.homMk D.presheafHom

set_option backward.isDefEq.respectTransparency false in
/-- On a chosen lift, the induced stalk map followed by evaluation is the supplied comparison. -/
theorem stalkFunctorMap_comp_stalkEvaluation
    (D : StalkComparisonData (M := M) p hp F) (e : E) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (p e)).map D.presheafHom ≫
        stalkEvaluation (M := M) p hp e =
      D.stalkMap e := by
  apply F.presheaf.stalk_hom_ext
  intro U heU
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  ext s
  exact stalkEvaluation_germ p hp e U heU (D.toSection U s)

set_option backward.isDefEq.respectTransparency false in
/-- If the supplied comparison at a chosen lift is an isomorphism, then so is the induced map on
the stalk at its image. -/
theorem stalkFunctorMap_isIso
    (D : StalkComparisonData (M := M) p hp F) (e : E)
    [IsIso (D.stalkMap e)] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (p e)).map D.presheafHom) := by
  let f := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (p e)).map D.presheafHom
  let q := stalkEvaluation (M := M) p hp e
  have : IsIso (f ≫ q) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (p e)).map D.presheafHom ≫
        stalkEvaluation (M := M) p hp e)
    rw [D.stalkFunctorMap_comp_stalkEvaluation e]
    infer_instance
  exact IsIso.of_isIso_comp_right f q

set_option backward.isDefEq.respectTransparency false in
/-- If every supplied stalk comparison is an isomorphism, then the descended morphism of sheaves
is an isomorphism. -/
theorem hom_isIso
    (D : StalkComparisonData (M := M) p hp F)
    [∀ e : E, IsIso (D.stalkMap e)] : IsIso D.hom := by
  let (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map D.hom.hom) := by
    obtain ⟨e, rfl⟩ := hp.surjective x
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (p e)).map D.presheafHom)
    exact D.stalkFunctorMap_isIso e
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso D.hom

end StalkComparisonData

end PrincipalCoverLocalSystem
