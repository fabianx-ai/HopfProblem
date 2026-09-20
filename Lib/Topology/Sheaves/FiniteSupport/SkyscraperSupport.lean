module

public import Lib.Topology.Sheaves.FiniteSupport.SkyscraperReconstruction

/-!
# Stalks and support of skyscraper sheaves

The stalk of `skyscraper p A` is `A` at `p` and zero at every other point of a `T₁` space
(Hartshorne, *Algebraic Geometry*, II Ex. 1.17; Mathlib
`skyscraperPresheafStalkOfSpecializes`, `skyscraperPresheafStalkOfNotSpecializesIsTerminal`).
Consequently, a sheaf whose stalks vanish outside two points `p ≠ q` and whose chosen stalk maps
at `p` and `q` are invertible is isomorphic to `skyscraper p A ⊞ skyscraper q B`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf.FiniteSupport

universe u

variable {X : TopCat.{u}}

/-- The stalk of `skyscraper p A` at `p` is `A` (Hartshorne II Ex. 1.17). -/
def stalkSkyscraperAtIso (p : X) (A : AddCommGrpCat.{u}) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj (skyscraperAt p A).obj ≅ A := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  exact skyscraperPresheafStalkOfSpecializes p A specializes_rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `F ⟶ skyscraper p A` adjoint to a stalk map `f : F_p ⟶ A` induces `f` again on
the stalk at `p`, after the identification of the skyscraper stalk with `A`. -/
lemma stalkMap_toSkyscraperAt_comp_counit
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (p : X) (A : AddCommGrpCat.{u})
    (f : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).map
        (toSkyscraperAt p A f).hom ≫
      (stalkSkyscraperAtIso p A).hom = f := by
  let _ : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  apply F.presheaf.stalk_hom_ext
  intro U hpU
  rw [← Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  dsimp [toSkyscraperAt, stalkSkyscraperAtIso, skyscraperAt, skyscraperSheaf]
  rw [Category.assoc]
  rw [germ_skyscraperPresheafStalkOfSpecializes_hom
    p A specializes_rfl U hpU]
  simp [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, hpU]

/-- Stalks commute with biproducts: `(G ⊞ H)_x ≅ G_x ⊞ H_x`. -/
def sheafStalkBiprodIso (x : X)
    (G H : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (G ⊞ H) ≅
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj G ⊞
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj H := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let _ : PreservesBinaryBiproducts S :=
    preservesBinaryBiproducts_of_preservesBiproducts S
  exact S.mapBiprod G H

/-- The stalk map of the comparison into a biproduct of two skyscrapers has the two individual
skyscraper comparisons as its coordinates. -/
@[reassoc]
lemma stalkMap_toSkyscraperBiprod_comp_mapBiprod
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (x p q : X) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B) :
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSkyscraperBiprod p q A B fp fq)) ≫
      (sheafStalkBiprodIso x (skyscraperAt p A) (skyscraperAt q B)).hom =
      biprod.lift
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (toSkyscraperAt p A fp))
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (toSkyscraperAt q B fq)) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let _ : PreservesBinaryBiproducts S :=
    preservesBinaryBiproducts_of_preservesBiproducts S
  change S.map (toSkyscraperBiprod p q A B fp fq) ≫
      (S.mapBiprod (skyscraperAt p A) (skyscraperAt q B)).hom = _
  apply biprod.map_lift_mapBiprod

/-- On a `T₁` space the stalk of `skyscraper p A` at any point other than `p` is zero
(Hartshorne II Ex. 1.17). -/
lemma skyscraperAt_stalk_isZero_of_ne [T1Space X]
    (p x : X) (A : AddCommGrpCat.{u}) (h : p ≠ x) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (skyscraperAt p A).obj) := by
  let _ : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal p A
    (fun hp ↦ h (specializes_iff_eq.mp hp))).isZero

set_option backward.isDefEq.respectTransparency.types false in
/-- If the chosen stalk map at `p` is invertible, the comparison into the biproduct of the two
skyscrapers is an isomorphism on the stalk at `p`. -/
lemma isIso_stalkFunctor_map_toSkyscraperBiprod_at_left
    [T1Space X] {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (hpq : p ≠ q) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    [hfp : IsIso fp] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).map
      (toSkyscraperBiprod p q A B fp fq).hom) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p
  change IsIso (S.map (toSkyscraperBiprod p q A B fp fq))
  have hq : IsZero (S.obj (skyscraperAt q B)) :=
    skyscraperAt_stalk_isZero_of_ne q p B hpq.symm
  let e := sheafStalkBiprodIso p (skyscraperAt p A) (skyscraperAt q B)
  let ep := stalkSkyscraperAtIso p A
  let _ : IsIso (e.hom ≫ biprod.fst ≫ ep.hom) := by
    exact IsIso.comp_isIso' e.isIso_hom
      (IsIso.comp_isIso' (isoBiprodZero hq).isIso_inv ep.isIso_hom)
  have hcomp :
      S.map (toSkyscraperBiprod p q A B fp fq) ≫
          (e.hom ≫ biprod.fst ≫ ep.hom) = fp := by
    dsimp only [S, e]
    simp only [Functor.comp_map]
    rw [stalkMap_toSkyscraperBiprod_comp_mapBiprod_assoc]
    rw [← Category.assoc]
    erw [biprod.lift_fst]
    exact stalkMap_toSkyscraperAt_comp_counit p A fp
  let _ : IsIso (S.map (toSkyscraperBiprod p q A B fp fq) ≫
      (e.hom ≫ biprod.fst ≫ ep.hom)) := by
    rw [hcomp]
    exact hfp
  exact IsIso.of_isIso_comp_right
    (S.map (toSkyscraperBiprod p q A B fp fq))
    (e.hom ≫ biprod.fst ≫ ep.hom)

set_option backward.isDefEq.respectTransparency.types false in
/-- If the chosen stalk map at `q` is invertible, the comparison into the biproduct of the two
skyscrapers is an isomorphism on the stalk at `q`. -/
lemma isIso_stalkFunctor_map_toSkyscraperBiprod_at_right
    [T1Space X] {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (hpq : p ≠ q) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    [hfq : IsIso fq] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).map
      (toSkyscraperBiprod p q A B fp fq).hom) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q
  change IsIso (S.map (toSkyscraperBiprod p q A B fp fq))
  have hp : IsZero (S.obj (skyscraperAt p A)) :=
    skyscraperAt_stalk_isZero_of_ne p q A hpq
  let e := sheafStalkBiprodIso q (skyscraperAt p A) (skyscraperAt q B)
  let eq := stalkSkyscraperAtIso q B
  let _ : IsIso (e.hom ≫ biprod.snd ≫ eq.hom) := by
    exact IsIso.comp_isIso' e.isIso_hom
      (IsIso.comp_isIso' (isoZeroBiprod hp).isIso_inv eq.isIso_hom)
  have hcomp :
      S.map (toSkyscraperBiprod p q A B fp fq) ≫
          (e.hom ≫ biprod.snd ≫ eq.hom) = fq := by
    dsimp only [S, e]
    simp only [Functor.comp_map]
    rw [stalkMap_toSkyscraperBiprod_comp_mapBiprod_assoc]
    rw [← Category.assoc]
    erw [biprod.lift_snd]
    exact stalkMap_toSkyscraperAt_comp_counit q B fq
  let _ : IsIso (S.map (toSkyscraperBiprod p q A B fp fq) ≫
      (e.hom ≫ biprod.snd ≫ eq.hom)) := by
    rw [hcomp]
    exact hfq
  exact IsIso.of_isIso_comp_right
    (S.map (toSkyscraperBiprod p q A B fp fq))
    (e.hom ≫ biprod.snd ≫ eq.hom)

set_option backward.isDefEq.respectTransparency.types false in
/-- For a sheaf whose stalks vanish away from `p ≠ q` and whose chosen stalk maps at `p` and `q`
are invertible, the comparison into the biproduct of the two skyscrapers is an isomorphism on
every stalk. -/
theorem isIso_stalkFunctor_map_toSkyscraperBiprod
    [T1Space X] {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (hpq : p ≠ q) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    [IsIso fp] [IsIso fq]
    (hF : ∀ x : X, x ≠ p → x ≠ q →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj))
    (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSkyscraperBiprod p q A B fp fq).hom) := by
  by_cases hxp : x = p
  · subst x
    exact isIso_stalkFunctor_map_toSkyscraperBiprod_at_left
      p q hpq A B fp fq
  by_cases hxq : x = q
  · subst x
    exact isIso_stalkFunctor_map_toSkyscraperBiprod_at_right
      p q hpq A B fp fq
  · let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    change IsIso (S.map (toSkyscraperBiprod p q A B fp fq))
    have hsource : IsZero (S.obj F) := hF x hxp hxq
    have hp : IsZero (S.obj (skyscraperAt p A)) :=
      skyscraperAt_stalk_isZero_of_ne p x A (Ne.symm hxp)
    have hq : IsZero (S.obj (skyscraperAt q B)) :=
      skyscraperAt_stalk_isZero_of_ne q x B (Ne.symm hxq)
    let _ : PreservesBinaryBiproducts S :=
      preservesBinaryBiproducts_of_preservesBiproducts S
    let e := S.mapBiprod (skyscraperAt p A) (skyscraperAt q B)
    have hsum : IsZero (S.obj (skyscraperAt p A) ⊞
        S.obj (skyscraperAt q B)) :=
      (biprod_isZero_iff _ _).2 ⟨hp, hq⟩
    have htarget : IsZero (S.obj
        (skyscraperAt p A ⊞ skyscraperAt q B)) :=
      hsum.of_iso e
    exact hsource.isIso htarget _

/-- A sheaf whose stalks vanish outside two points `p ≠ q`, with invertible chosen stalk maps
there, is isomorphic to `skyscraper p A ⊞ skyscraper q B` (Hartshorne II Ex. 1.17). -/
def skyscraperBiprodIsoOfTwoPointSupport
    [T1Space X] {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (p q : X) (hpq : p ≠ q) (A B : AddCommGrpCat.{u})
    (fp : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).obj F.obj ⟶ A)
    (fq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q).obj F.obj ⟶ B)
    [IsIso fp] [IsIso fq]
    (hF : ∀ x : X, x ≠ p → x ≠ q →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj)) :
    F ≅ skyscraperAt p A ⊞ skyscraperAt q B :=
  skyscraperBiprodIsoOfStalkwiseIso p q A B fp fq fun x ↦
    isIso_stalkFunctor_map_toSkyscraperBiprod p q hpq A B fp fq hF x

end TopCat.Sheaf.FiniteSupport

end
