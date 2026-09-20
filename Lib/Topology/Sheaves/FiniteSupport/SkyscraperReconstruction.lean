/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.FiniteSupport.SkyscraperGlobalSections

/-!
# Reconstructing a sheaf from stalk maps to skyscrapers

Maps `F_p ⟶ A` from a stalk correspond to maps `F ⟶ skyscraper p A` of sheaves (the skyscraper
adjunction, Mathlib `StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf`; Hartshorne,
*Algebraic Geometry*, II Ex. 1.17).  Two such maps assemble into a comparison
`F ⟶ skyscraper p A ⊞ skyscraper q B`, and a morphism of sheaves is an isomorphism as soon as it
is one on every stalk (Hartshorne II Prop. 1.1; Mathlib
`TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`), so a stalkwise invertible comparison is an
isomorphism of sheaves.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf.FiniteSupport

universe u

variable {X : TopCat.{u}}

/-- The morphism `F ⟶ skyscraper p A` adjoint to a map `F_p ⟶ A` from the stalk at `p`. -/
def toSkyscraperAt {F : TopCat.Sheaf AddCommGrpCat.{u} X} (p : X) (A : AddCommGrpCat.{u})
    (f : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A) :
    F ⟶ skyscraperAt p A := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  exact ObjectProperty.homMk
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf p f)

/-- On the top open, the canonical skyscraper-section isomorphism is the transport associated
to the fact that the support point belongs to the top open. -/
theorem skyscraperAtTopIso_hom_eqToHom (p : X) (A : AddCommGrpCat.{u})
    (hp : p ∈ (⊤ : Opens X)) :
    (skyscraperAtTopIso p A).hom =
      (eqToHom (if_pos hp) :
        (skyscraperAt p A).obj.obj (op (⊤ : Opens X)) ⟶ A) := by
  unfold skyscraperAtTopIso
  rfl

/-- On global sections, the morphism adjoint to a stalk map `F_p ⟶ A` is the germ at `p`
followed by that stalk map. -/
theorem toSkyscraperAt_top {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p : X) (A : AddCommGrpCat.{u})
    (f : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A) :
    (toSkyscraperAt p A f).hom.app (op (⊤ : Opens X)) ≫
        (skyscraperAtTopIso p A).hom =
      F.presheaf.germ (⊤ : Opens X) p (by simp) ≫ f := by
  let _ : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  let g : F.obj ⟶ skyscraperPresheaf p A := (toSkyscraperAt p A f).hom
  have hfrom : StalkSkyscraperPresheafAdjunctionAuxs.fromStalk p g = f := by
    dsimp [g, toSkyscraperAt]
    change StalkSkyscraperPresheafAdjunctionAuxs.fromStalk p
      (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf p f) = f
    exact StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper p f
  change g.app (op (⊤ : Opens X)) ≫ (skyscraperAtTopIso p A).hom = _
  rw [skyscraperAtTopIso_hom_eqToHom p A (by simp)]
  calc
    _ = F.presheaf.germ (⊤ : Opens X) p (by simp) ≫
        StalkSkyscraperPresheafAdjunctionAuxs.fromStalk p g :=
      (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk p g
        (⊤ : Opens X) (by simp)).symm
    _ = F.presheaf.germ (⊤ : Opens X) p (by simp) ≫ f := by rw [hfrom]

/-- Two stalk maps `F_p ⟶ A` and `F_q ⟶ B` assemble into a morphism into the skyscraper
biproduct. -/
def toSkyscraperBiprod {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B) :
    F ⟶ skyscraperAt p A ⊞ skyscraperAt q B :=
  biprod.lift (toSkyscraperAt p A fp) (toSkyscraperAt q B fq)

/-- A comparison `F ⟶ skyscraper p A ⊞ skyscraper q B` that is invertible on every stalk is an
isomorphism of sheaves. -/
def skyscraperBiprodIsoOfStalkwiseIso {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom)) :
    F ≅ skyscraperAt p A ⊞ skyscraperAt q B := by
  letI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom) := h
  letI : IsIso (toSkyscraperBiprod p q A B fp fq) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (toSkyscraperBiprod p q A B fp fq)
  exact asIso (toSkyscraperBiprod p q A B fp fq)

private theorem biprodIsoProd_hom_comp_fst (A B : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst A B) =
      (biprod.fst : A ⊞ B ⟶ A) := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).1
  simp

private theorem biprodIsoProd_hom_comp_snd (A B : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd A B) =
      (biprod.snd : A ⊞ B ⟶ B) := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).1
  simp

@[reassoc]
private theorem sectionsBiprodIso_hom_comp_fst
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sectionsBiprodIso F G (op (⊤ : Opens X))).hom ≫ biprod.fst =
      (TopCat.Sheaf.globalSectionsFunctor X).map (biprod.fst : F ⊞ G ⟶ F) := by
  unfold sectionsBiprodIso TopCat.Sheaf.globalSectionsFunctor
  rw [Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

@[reassoc]
private theorem sectionsBiprodIso_hom_comp_snd
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sectionsBiprodIso F G (op (⊤ : Opens X))).hom ≫ biprod.snd =
      (TopCat.Sheaf.globalSectionsFunctor X).map (biprod.snd : F ⊞ G ⟶ G) := by
  unfold sectionsBiprodIso TopCat.Sheaf.globalSectionsFunctor
  rw [Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The first coordinate of the reconstructed global section is the germ at `p`, followed by the
given stalk map `F_p ⟶ A`. -/
theorem globalSectionsIsoOfStalkwiseSkyscraperBiprod_hom_comp_fst
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom)) :
    (globalSectionsIsoOfSkyscraperBiprodIso p q A B
        (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h)).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst A B) =
      F.presheaf.germ (⊤ : Opens X) p (by simp) ≫ fp := by
  unfold globalSectionsIsoOfSkyscraperBiprodIso
  change (((((TopCat.Sheaf.globalSectionsFunctor X).map
      (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h).hom) ≫
        (sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤)).hom) ≫
      (biprod.mapIso (skyscraperAtTopIso p A) (skyscraperAtTopIso q B)).hom) ≫
        (AddCommGrpCat.biprodIsoProd A B).hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.fst A B) = _
  simp only [Category.assoc]
  rw [biprodIsoProd_hom_comp_fst]
  rw [biprod.mapIso_hom]
  rw [biprod.map_fst]
  let e := skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h
  have hs := sectionsBiprodIso_hom_comp_fst_assoc
    (skyscraperAt p A) (skyscraperAt q B) (skyscraperAtTopIso p A).hom
  have he : e.hom ≫ (biprod.fst :
      skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt p A) =
      toSkyscraperAt p A fp := by
    dsimp [e]
    simp [skyscraperBiprodIsoOfStalkwiseIso, toSkyscraperBiprod]
  change (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫
    (sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤)).hom ≫
      (biprod.fst :
        (skyscraperAt p A).obj.obj (op ⊤) ⊞
          (skyscraperAt q B).obj.obj (op ⊤) ⟶
            (skyscraperAt p A).obj.obj (op ⊤)) ≫
        (skyscraperAtTopIso p A).hom = _
  calc
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫
        (TopCat.Sheaf.globalSectionsFunctor X).map (biprod.fst :
          skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt p A) ≫
            (skyscraperAtTopIso p A).hom := by
      exact congrArg (fun k ↦ (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫ k) hs
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map (e.hom ≫ (biprod.fst :
          skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt p A)) ≫
            (skyscraperAtTopIso p A).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map (toSkyscraperAt p A fp) ≫
          (skyscraperAtTopIso p A).hom := by rw [he]
    _ = F.presheaf.germ (⊤ : Opens X) p (by simp) ≫ fp :=
      toSkyscraperAt_top p A fp

set_option backward.isDefEq.respectTransparency.types false in
/-- The second coordinate of the reconstructed global section is the germ at `q`, followed by the
given stalk map `F_q ⟶ B`. -/
theorem globalSectionsIsoOfStalkwiseSkyscraperBiprod_hom_comp_snd
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom)) :
    (globalSectionsIsoOfSkyscraperBiprodIso p q A B
        (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h)).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd A B) =
      F.presheaf.germ (⊤ : Opens X) q (by simp) ≫ fq := by
  unfold globalSectionsIsoOfSkyscraperBiprodIso
  change (((((TopCat.Sheaf.globalSectionsFunctor X).map
      (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h).hom) ≫
        (sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤)).hom) ≫
      (biprod.mapIso (skyscraperAtTopIso p A) (skyscraperAtTopIso q B)).hom) ≫
        (AddCommGrpCat.biprodIsoProd A B).hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.snd A B) = _
  simp only [Category.assoc]
  rw [biprodIsoProd_hom_comp_snd]
  rw [biprod.mapIso_hom]
  rw [biprod.map_snd]
  let e := skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h
  have hs := sectionsBiprodIso_hom_comp_snd_assoc
    (skyscraperAt p A) (skyscraperAt q B) (skyscraperAtTopIso q B).hom
  have he : e.hom ≫ (biprod.snd :
      skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt q B) =
      toSkyscraperAt q B fq := by
    dsimp [e]
    simp [skyscraperBiprodIsoOfStalkwiseIso, toSkyscraperBiprod]
  change (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫
    (sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤)).hom ≫
      (biprod.snd :
        (skyscraperAt p A).obj.obj (op ⊤) ⊞
          (skyscraperAt q B).obj.obj (op ⊤) ⟶
            (skyscraperAt q B).obj.obj (op ⊤)) ≫
        (skyscraperAtTopIso q B).hom = _
  calc
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫
        (TopCat.Sheaf.globalSectionsFunctor X).map (biprod.snd :
          skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt q B) ≫
            (skyscraperAtTopIso q B).hom := by
      exact congrArg (fun k ↦ (TopCat.Sheaf.globalSectionsFunctor X).map e.hom ≫ k) hs
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map (e.hom ≫ (biprod.snd :
          skyscraperAt p A ⊞ skyscraperAt q B ⟶ skyscraperAt q B)) ≫
            (skyscraperAtTopIso q B).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (TopCat.Sheaf.globalSectionsFunctor X).map (toSkyscraperAt q B fq) ≫
          (skyscraperAtTopIso q B).hom := by rw [he]
    _ = F.presheaf.germ (⊤ : Opens X) q (by simp) ≫ fq :=
      toSkyscraperAt_top q B fq

set_option backward.isDefEq.respectTransparency.types false in
/-- Under the reconstruction `Γ(X, F) ≃+ A × B`, a global section is sent to the pair of its
germs at `p` and `q` composed with the two stalk maps. -/
theorem globalSectionsEquivOfStalkwiseSkyscraperBiprod_apply
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom))
    (s : F.obj.obj (op (⊤ : Opens X))) :
    globalSectionsEquivOfSkyscraperBiprodIso p q A B
        (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h) s =
      ((F.presheaf.germ (⊤ : Opens X) p (by simp) ≫ fp) s,
        (F.presheaf.germ (⊤ : Opens X) q (by simp) ≫ fq) s) := by
  unfold globalSectionsEquivOfSkyscraperBiprodIso
  change (AddCommGrpCat.Hom.hom
    (globalSectionsIsoOfSkyscraperBiprodIso p q A B
      (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h)).hom) s = _
  apply Prod.ext
  · change (AddCommGrpCat.Hom.hom
      ((globalSectionsIsoOfSkyscraperBiprodIso p q A B
        (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h)).hom ≫
          AddCommGrpCat.ofHom (AddMonoidHom.fst A B))) s = _
    rw [globalSectionsIsoOfStalkwiseSkyscraperBiprod_hom_comp_fst]
    rfl
  · change (AddCommGrpCat.Hom.hom
      ((globalSectionsIsoOfSkyscraperBiprodIso p q A B
        (skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq h)).hom ≫
          AddCommGrpCat.ofHom (AddMonoidHom.snd A B))) s = _
    rw [globalSectionsIsoOfStalkwiseSkyscraperBiprod_hom_comp_snd]
    rfl

end TopCat.Sheaf.FiniteSupport

end
