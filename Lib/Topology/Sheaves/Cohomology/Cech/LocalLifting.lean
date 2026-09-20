/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.LocallyZeroCochain
public import Lib.Topology.Sheaves.Cohomology.Cech.Coefficients
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local lifting of normalized Cech cochains

This is the lifting step in the construction of the long exact Čech sequence on a paracompact
space.  For a morphism of sheaves of abelian groups, its section quotient is the presheaf whose
value on an open set is the quotient of target sections by the image of source sections.  If the
sheaf morphism is an epimorphism, this presheaf is locally zero.  Independently, its value on the
empty open is zero by the empty-cover sheaf axiom.

The locally-zero cochain theorem then makes the quotient of any normalized cochain literally zero
on one refinement.  Choosing a preimage in every ordered-simplex component produces a single
source-valued cochain whose coefficient image is the refined pullback of the original cochain.
The refinement may depend on the cochain and its degree; no surjectivity statement is made for
sections on the original cover.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.10
* G. E. Bredon, *Sheaf Theory*, III.4
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace TopCat.Sheaf

variable {X : TopCat.{w}}
variable {B C : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- The section quotient presheaf of a morphism of sheaves of abelian groups.  On an open `U`,
its sections are `C(U)` modulo the image of `B(U) ⟶ C(U)`. -/
noncomputable def sectionQuotientPresheaf (f : B ⟶ C) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of
    (C.obj.obj U ⧸ AddMonoidHom.range (f.hom.app U).hom)
  map {U V} i := AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (C.obj.map i).hom (by
      rintro _ ⟨b, rfl⟩
      exact ⟨B.obj.map i b, f.hom.naturality_apply i b⟩)
  map_id U := by
    ext c
    simp
  map_comp i j := by
    ext c
    simp

/-- The componentwise quotient projection from the target sheaf's underlying presheaf to its
section quotient presheaf. -/
noncomputable def sectionQuotientPresheafProjection (f : B ⟶ C) :
    C.obj ⟶ sectionQuotientPresheaf f where
  app U := AddCommGrpCat.ofHom <|
    QuotientAddGroup.mk' (AddMonoidHom.range (f.hom.app U).hom)
  naturality {U V} i := by
    ext c
    rfl

/-- The section quotient of an epimorphism of sheaves is locally zero.  This uses only local
surjectivity of the sheaf epimorphism, not surjectivity on sections of the given open set. -/
theorem sectionQuotientPresheaf_isLocallyZero
    {X : TopCat.{u}} {B C : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : B ⟶ C) [Epi f] :
    (sectionQuotientPresheaf f).IsLocallyZero := by
  intro U q x hx
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  have hloc : TopCat.Presheaf.IsLocallySurjective f.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi f).2
      (show Epi f from inferInstance)
  obtain ⟨V, hVU, ⟨b, hb⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff f.hom).1 hloc U c x hx
  refine ⟨V, hVU, hxV, ?_⟩
  change QuotientAddGroup.mk' (AddMonoidHom.range (f.hom.app (op V)).hom)
      (C.obj.map (homOfLE hVU).op c) = 0
  change f.hom.app (op V) b = C.obj.map (homOfLE hVU).op c at hb
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨b, hb⟩

/-- The section quotient presheaf is zero on the empty open.  The empty-cover sheaf axiom makes
the empty-open section groups of both source and target zero; in particular the target, and hence
its quotient, is subsingleton. -/
theorem sectionQuotientPresheaf_empty_isZero (f : B ⟶ C) :
    IsZero ((sectionQuotientPresheaf f).obj (op (⊥ : Opens X))) := by
  have hempty : IsZero (B.obj.obj (op (⊥ : Opens X))) ∧
      IsZero (C.obj.obj (op (⊥ : Opens X))) :=
    ⟨B.isTerminalOfEmpty.isZero, C.isTerminalOfEmpty.isZero⟩
  let _ : Subsingleton (C.obj.obj (op (⊥ : Opens X))) :=
    AddCommGrpCat.subsingleton_of_isZero hempty.2
  let hQ : Subsingleton ((sectionQuotientPresheaf f).obj (op (⊥ : Opens X))) :=
    ⟨by
      intro q r
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
      obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ r
      congr
      exact Subsingleton.elim _ _⟩
  exact @AddCommGrpCat.isZero_of_subsingleton _ hQ

end TopCat.Sheaf

namespace TopologicalSpace.OpenCover

private theorem coefficientMapDegree_refinementMapDegree_apply
    {X : TopCat.{u}} {I J : Type u} [LinearOrder I] [LinearOrder J]
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) {U : I → Opens X} {V : J → Opens X}
    (r : Refinement V U) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X) P U q) :
    OrderedCech.coefficientMapDegree f V q
        (OrderedCech.refinementMapDegree P r q a) =
      OrderedCech.refinementMapDegree Q r q
        (OrderedCech.coefficientMapDegree f U q a) := by
  have h := congrArg (fun k ↦ k.f q)
    (OrderedCech.coefficientMap_comp_refinementMap f r)
  simpa only [OrderedCech.coefficientMap_f, OrderedCech.refinementMap_f,
    HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom h a).symm

namespace SetOpenCover

private theorem exists_preimage_of_sectionQuotientProjection_eq_zero
    {X : TopCat.{u}} {B C : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : B ⟶ C) (U : Opens X) (c : C.obj.obj (op U))
    (h : (TopCat.Sheaf.sectionQuotientPresheafProjection f).app (op U) c = 0) :
    ∃ b : B.obj.obj (op U), f.hom.app (op U) b = c := by
  change QuotientAddGroup.mk' (AddMonoidHom.range (f.hom.app (op U)).hom) c = 0 at h
  exact (QuotientAddGroup.eq_zero_iff c).1 h

/-- The quotient of a normalized target-valued cochain becomes literally zero after one
refinement.  This is the direct application of the locally-zero cochain theorem to the section
quotient presheaf, with local zeroness and empty-open reducedness supplied separately. -/
theorem exists_refinement_sectionQuotient_cochain_eq_zero
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    {B C : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : B ⟶ C) [Epi f] (U : SetOpenCover X) (q : ℕ)
    (c : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
      C.obj U.family q) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family),
      OrderedCech.refinementMapDegree
        (TopCat.Sheaf.sectionQuotientPresheaf
          (X := X) (B := B) (C := C) f) r q
        (OrderedCech.coefficientMapDegree (X := X) (A := AddCommGrpCat.{u})
          (TopCat.Sheaf.sectionQuotientPresheafProjection
            (X := X) (B := B) (C := C) f)
          U.family q c) = 0 :=
  exists_refinement_pullback_eq_zero_of_isLocallyZero_of_isZero_empty
    (TopCat.Sheaf.sectionQuotientPresheaf (X := X) (B := B) (C := C) f)
    (TopCat.Sheaf.sectionQuotientPresheaf_isLocallyZero
      (X := X) (B := B) (C := C) f)
    (TopCat.Sheaf.sectionQuotientPresheaf_empty_isZero
      (X := X) (B := B) (C := C) f) U q
    (OrderedCech.coefficientMapDegree (X := X) (A := AddCommGrpCat.{u})
      (TopCat.Sheaf.sectionQuotientPresheafProjection
        (X := X) (B := B) (C := C) f) U.family q c)

/-- A normalized cochain valued in the target of an epimorphism of abelian sheaves has a
source-valued lift after passage to one set-valued open refinement.  The coefficient image of the
chosen lift is literally the refined pullback of the original cochain. -/
theorem exists_refinement_cochain_lift
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    {B C : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : B ⟶ C) [Epi f] (U : SetOpenCover X) (q : ℕ)
    (c : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
      C.obj U.family q) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family)
      (b : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
        B.obj V.family q),
      OrderedCech.coefficientMapDegree f.hom V.family q b =
        OrderedCech.refinementMapDegree C.obj r q c := by
  let Q := TopCat.Sheaf.sectionQuotientPresheaf f
  let p : C.obj ⟶ Q := TopCat.Sheaf.sectionQuotientPresheafProjection f
  obtain ⟨V, r, hzero⟩ :=
    exists_refinement_sectionQuotient_cochain_eq_zero f U q c
  have hquotient : OrderedCech.coefficientMapDegree p V.family q
      (OrderedCech.refinementMapDegree C.obj r q c) = 0 := by
    rw [coefficientMapDegree_refinementMapDegree_apply]
    exact hzero
  have hcomponent : ∀ σ : OrderedSimplex V.Index q,
      (TopCat.Sheaf.sectionQuotientPresheafProjection f).app
          (op (σ.intersection V.family))
        (OrderedCech.π C.obj V.family q σ
          (OrderedCech.refinementMapDegree C.obj r q c)) = 0 := by
    intro σ
    have hσ := congrArg
      (fun z ↦ OrderedCech.π Q V.family q σ z) hquotient
    calc
      p.app (op (σ.intersection V.family))
          (OrderedCech.π C.obj V.family q σ
            (OrderedCech.refinementMapDegree C.obj r q c)) =
        OrderedCech.π Q V.family q σ
          (OrderedCech.coefficientMapDegree p V.family q
            (OrderedCech.refinementMapDegree C.obj r q c)) := by
              exact (ConcreteCategory.congr_hom
                (OrderedCech.coefficientMapDegree_π p V.family q σ)
                (OrderedCech.refinementMapDegree C.obj r q c)).symm
      _ = 0 := by simpa only [map_zero] using hσ
  choose b hb using fun σ : OrderedSimplex V.Index q ↦
    exists_preimage_of_sectionQuotientProjection_eq_zero f
      (σ.intersection V.family)
      (OrderedCech.π C.obj V.family q σ
        (OrderedCech.refinementMapDegree C.obj r q c)) (hcomponent σ)
  let lift : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
      B.obj V.family q :=
    (Limits.Concrete.productEquiv
      (fun σ : OrderedSimplex V.Index q ↦
        B.obj.obj (op (σ.intersection V.family)))).symm b
  refine ⟨V, r, lift, ?_⟩
  apply (Limits.Concrete.productEquiv
    (fun σ : OrderedSimplex V.Index q ↦
      C.obj.obj (op (σ.intersection V.family)))).injective
  funext σ
  simp only [Limits.Concrete.productEquiv_apply_apply]
  calc
    OrderedCech.π C.obj V.family q σ
        (OrderedCech.coefficientMapDegree f.hom V.family q lift) =
      f.hom.app (op (σ.intersection V.family))
        (OrderedCech.π B.obj V.family q σ lift) := by
          exact ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_π f.hom V.family q σ) lift
    _ = OrderedCech.π C.obj V.family q σ
        (OrderedCech.refinementMapDegree C.obj r q c) := by
      rw [show OrderedCech.π B.obj V.family q σ lift = b σ by
        simpa only [OrderedCech.π, lift] using
          (Limits.Concrete.productEquiv_symm_apply_π
            (fun τ : OrderedSimplex V.Index q ↦
              B.obj.obj (op (τ.intersection V.family))) b σ)]
      exact hb σ

end SetOpenCover

end TopologicalSpace.OpenCover
