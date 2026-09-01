/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestriction.Cohomology
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Sheaf
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalSections
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Open restriction of native singular cochains

This file identifies the native singular-cochain presheaf restricted to an open subspace
with the intrinsic singular-cochain presheaf of that subspace.  Combined with the general
compatibility of sheafification and continuous/cocontinuous open restriction, this is the
textbook bridge needed to reduce extension of sheaf sections on an ambient open to the already
proved global representative theorem on the corresponding open subspace.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X) (A : AddCommGrpCat.{0}) (n : ℕ)

open AlgebraicTopology.SingularCochains

/-- Extend a native cochain on an open subspace to the ambient space, assigning zero to every
singular simplex whose image is not contained in that open. -/
def extendByZero (t : Cochains U A n) : Cochains X A n := by
  classical
  exact cochainFromValues A n fun sigma =>
    if hsigma : Set.range sigma ⊆ U then
      t (TopCat.SingularSmallChains.simplexChain U n
        (simplexInOpen n sigma U hsigma))
    else 0

/-- Restricting an extension-by-zero native cochain recovers the original cochain. -/
theorem restrict_extendByZero (t : Cochains U A n) :
    restrictGlobalCochain A n (extendByZero U A n t) U = t := by
  classical
  apply cochain_ext A n
  intro sigma
  let tau : TopCat.SingularSmallChains.SingularSimplex X n :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp sigma
  have htau : Set.range tau ⊆ U := by
    rintro _ ⟨z, rfl⟩
    exact (sigma z).property
  rw [restrictGlobalCochain_simplex]
  change extendByZero U A n t
      (TopCat.SingularSmallChains.simplexChain X n tau) = _
  rw [extendByZero, cochainFromValues_simplex, dif_pos htau]
  congr 2

/-- Extend a cochain by zero along an arbitrary inclusion of ambient opens. -/
def extendByZeroAlong {U V : (Opens X)ᵒᵖ} (_i : U ⟶ V)
    (t : Cochains V.unop A n) : Cochains U.unop A n := by
  classical
  exact cochainFromValues A n fun sigma =>
    let tau : TopCat.SingularSmallChains.SingularSimplex X n :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U.unop, X)).comp sigma
    if htau : Set.range tau ⊆ V.unop then
      t (TopCat.SingularSmallChains.simplexChain V.unop n
        (simplexInOpen n tau V.unop htau))
    else 0

set_option backward.isDefEq.respectTransparency false in
/-- Restriction after extension by zero along an inclusion of opens is the identity. -/
theorem map_extendByZeroAlong {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (t : Cochains V.unop A n) :
    (AlgebraicTopology.SingularCochains.pullback A
      (((Opens.toTopCat X).map i.unop).hom)).f n
        (extendByZeroAlong A n i t) = t := by
  classical
  apply cochain_ext A n
  intro sigma
  let f : C(V.unop, U.unop) := ((Opens.toTopCat X).map i.unop).hom
  let tau : TopCat.SingularSmallChains.SingularSimplex X n :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U.unop, X)).comp (f.comp sigma)
  have htau : Set.range tau ⊆ V.unop := by
    rintro _ ⟨z, rfl⟩
    exact (sigma z).property
  rw [pullback_simplex]
  change extendByZeroAlong A n i t
      (TopCat.SingularSmallChains.simplexChain U.unop n (f.comp sigma)) = _
  rw [extendByZeroAlong, cochainFromValues_simplex, dif_pos htau]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- Every native singular-cochain restriction along an inclusion of opens is surjective. -/
theorem presheaf_map_surjective {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    Function.Surjective ((presheaf X A n).map i) := by
  change Function.Surjective
    ((AlgebraicTopology.SingularCochains.pullback A
      (((Opens.toTopCat X).map i.unop).hom)).f n)
  intro t
  exact ⟨extendByZeroAlong A n i t, map_extendByZeroAlong A n i t⟩

/-- An open of the open subspace is homeomorphic to its ambient open image. -/
def openImageHomeomorph (V : Opens U) :
    V ≃ₜ (TopCat.Sheaf.OpenRestriction.openImage U).obj V :=
  U.isOpenEmbedding.toIsEmbedding.homeomorphImage (V : Set U)

/-- Forward map underlying the canonical open-image homeomorphism. -/
def openImageMap (V : Opens U) :
    C(V, (TopCat.Sheaf.OpenRestriction.openImage U).obj V) :=
  ⟨openImageHomeomorph U V, (openImageHomeomorph U V).continuous⟩

/-- Inverse map underlying the canonical open-image homeomorphism. -/
def openImageMapInv (V : Opens U) :
    C((TopCat.Sheaf.OpenRestriction.openImage U).obj V, V) :=
  ⟨(openImageHomeomorph U V).symm, (openImageHomeomorph U V).symm.continuous⟩

/-- Degreewise cochain pullback along the canonical open-image homeomorphism. -/
def openImageCochainIso (V : Opens U) :
    (presheaf X A n).obj
        (op ((TopCat.Sheaf.OpenRestriction.openImage U).obj V)) ≅
      (presheaf (TopCat.of U) A n).obj (op V) where
  hom := (AlgebraicTopology.SingularCochains.pullback A
    (openImageMap U V)).f n
  inv := (AlgebraicTopology.SingularCochains.pullback A
    (openImageMapInv U V)).f n
  hom_inv_id := by
    change
      (AlgebraicTopology.SingularCochains.pullback A
          (openImageMap U V)).f n ≫
        (AlgebraicTopology.SingularCochains.pullback A
          (openImageMapInv U V)).f n = 𝟙 _
    have h := congrArg (fun f => f.f n)
      (AlgebraicTopology.SingularCochains.pullback_comp A
        (openImageMapInv U V)
        (openImageMap U V))
    rw [show (openImageMap U V).comp
          (openImageMapInv U V) = ContinuousMap.id _ by
        ext x
        exact congrArg Subtype.val
          ((openImageHomeomorph U V).apply_symm_apply x),
      AlgebraicTopology.SingularCochains.pullback_id] at h
    exact h.symm
  inv_hom_id := by
    change
      (AlgebraicTopology.SingularCochains.pullback A
          (openImageMapInv U V)).f n ≫
        (AlgebraicTopology.SingularCochains.pullback A
          (openImageMap U V)).f n = 𝟙 _
    have h := congrArg (fun f => f.f n)
      (AlgebraicTopology.SingularCochains.pullback_comp A
        (openImageMap U V)
        (openImageMapInv U V))
    rw [show (openImageMapInv U V).comp
          (openImageMap U V) = ContinuousMap.id _ by
        ext x
        exact congrArg (fun y : V => (y.1 : X))
          ((openImageHomeomorph U V).symm_apply_apply x),
      AlgebraicTopology.SingularCochains.pullback_id] at h
    exact h.symm

/-- The ambient singular-cochain presheaf restricted to the open subspace. -/
abbrev restrictedPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of U) :=
  (TopCat.Sheaf.OpenRestriction.openImage U).op ⋙ presheaf X A n

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the ambient native singular-cochain presheaf to an open subspace is canonically
isomorphic to the intrinsic singular-cochain presheaf of that subspace. -/
def presheafIso : restrictedPresheaf U A n ≅ presheaf (TopCat.of U) A n :=
  NatIso.ofComponents
    (fun V => openImageCochainIso U A n V.unop)
    (fun {V W} r => by
      change
        (AlgebraicTopology.SingularCochains.pullback A
            (((Opens.toTopCat X).map
              ((TopCat.Sheaf.OpenRestriction.openImage U).map r.unop)).hom)).f n ≫
          (AlgebraicTopology.SingularCochains.pullback A
            (openImageMap U W.unop)).f n =
        (AlgebraicTopology.SingularCochains.pullback A
            (openImageMap U V.unop)).f n ≫
          (AlgebraicTopology.SingularCochains.pullback A
            (((Opens.toTopCat (TopCat.of U)).map r.unop).hom)).f n
      have hmap :
          (((Opens.toTopCat X).map
              ((TopCat.Sheaf.OpenRestriction.openImage U).map r.unop)).hom).comp
              (openImageMap U W.unop) =
            (openImageMap U V.unop).comp
              (((Opens.toTopCat (TopCat.of U)).map r.unop).hom) := by
        ext x
        rfl
      have hcomplex :
          AlgebraicTopology.SingularCochains.pullback A
              (((Opens.toTopCat X).map
                ((TopCat.Sheaf.OpenRestriction.openImage U).map r.unop)).hom) ≫
            AlgebraicTopology.SingularCochains.pullback A
              (openImageMap U W.unop) =
          AlgebraicTopology.SingularCochains.pullback A
              (openImageMap U V.unop) ≫
            AlgebraicTopology.SingularCochains.pullback A
              (((Opens.toTopCat (TopCat.of U)).map r.unop).hom) := by
        rw [← AlgebraicTopology.SingularCochains.pullback_comp,
          ← AlgebraicTopology.SingularCochains.pullback_comp, hmap]
      exact congrArg (fun f => f.f n) hcomplex)

/-- Sheafification of native singular cochains commutes with restriction to an open subspace. -/
def sheafIso :
    (TopCat.Sheaf.OpenRestriction.restriction U).obj (sheaf X A n) ≅
      sheaf (TopCat.of U) A n :=
  ((CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility
        (TopCat.Sheaf.OpenRestriction.openImage U) AddCommGrpCat.{0}
        (Opens.grothendieckTopology (TopCat.of U))
        (Opens.grothendieckTopology X)).app (presheaf X A n)).symm ≪≫
    (sheafification (TopCat.of U)).mapIso (presheafIso U A n)

set_option backward.isDefEq.respectTransparency false in
/-- The open-restriction comparison carries the ambient sheafification unit to the intrinsic
sheafification unit. -/
theorem unit_sheafIso_hom :
    (TopCat.Sheaf.OpenRestriction.openImage U).op.whiskerLeft (unit X A n) ≫
        (sheafIso U A n).hom.hom =
      (presheafIso U A n).hom ≫ unit (TopCat.of U) A n := by
  let G := TopCat.Sheaf.OpenRestriction.openImage U
  let J := Opens.grothendieckTopology (TopCat.of U)
  let K := Opens.grothendieckTopology X
  let C := CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility
    G AddCommGrpCat.{0} J K
  have hc := CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility
    G AddCommGrpCat.{0} J K (presheaf X A n)
  change G.op.whiskerLeft (unit X A n) ≫
      (C.inv.app (presheaf X A n)).hom ≫
        ((sheafification (TopCat.of U)).map (presheafIso U A n).hom).hom =
    (presheafIso U A n).hom ≫ unit (TopCat.of U) A n
  dsimp [unit] at hc ⊢
  have hcancel :
      G.op.whiskerLeft (toSheafify K (presheaf X A n)) ≫
          (C.inv.app (presheaf X A n)).hom =
        toSheafify J (G.op ⋙ presheaf X A n) := by
    have h := congrArg
      (fun q => q ≫ (C.inv.app (presheaf X A n)).hom) hc
    have hi := congrArg (fun q => q.hom)
      (C.hom_inv_id_app (presheaf X A n))
    change (C.hom.app (presheaf X A n)).hom ≫
        (C.inv.app (presheaf X A n)).hom = 𝟙 _ at hi
    rw [Category.assoc, hi] at h
    exact h.symm.trans (Category.comp_id _)
  rw [← Category.assoc, hcancel]
  exact (CategoryTheory.toSheafify_naturality J (presheafIso U A n).hom).symm

/-- Componentwise form of compatibility of the open-restriction comparison with the
sheafification unit. -/
theorem unit_sheafIso_hom_app (V : Opens U)
    (t : (presheaf X A n).obj
      (op ((TopCat.Sheaf.OpenRestriction.openImage U).obj V))) :
    (sheafIso U A n).hom.hom.app (op V)
        ((unit X A n).app
          (op ((TopCat.Sheaf.OpenRestriction.openImage U).obj V)) t) =
      (unit (TopCat.of U) A n).app (op V)
        ((presheafIso U A n).hom.app (op V) t) := by
  exact congrArg (fun q => q.app (op V) t) (unit_sheafIso_hom U A n)

/-- On a normal paracompact open subspace, every section of the ambient singular-cochain
sheaf over that open has a native-cochain representative. -/
theorem unit_app_surjective [NormalSpace U] [ParacompactSpace U] :
    Function.Surjective ((unit X A n).app (op U)) := by
  intro s
  let eP := (presheafIso U A n).app (op (⊤ : Opens U))
  let eS := (sheafIso U A n).hom.hom.app (op (⊤ : Opens U))
  let rS := TopCat.Sheaf.OpenRestriction.restrictionGlobalEquiv U (sheaf X A n)
  let sR := rS.symm s
  obtain ⟨phi, hphi⟩ :=
    globalCochainUnit_surjective (TopCat.of U) A n (eS sR)
  let phiTop := restrictGlobalCochain A n phi (⊤ : Opens U)
  let tR := eP.inv phiTop
  let htop := TopCat.Sheaf.OpenRestriction.openImage_top U
  let hOp : op ((TopCat.Sheaf.OpenRestriction.openImage U).obj ⊤) = op U :=
    congrArg op htop
  let t := (presheaf X A n).map (eqToHom hOp) tR
  refine ⟨t, ?_⟩
  have hsq := unit_sheafIso_hom_app U A n (⊤ : Opens U) tR
  have htR : eP.hom tR = phiTop := by
    exact eP.inv_hom_id_apply phiTop
  change (presheafIso U A n).hom.app (op ⊤) tR = phiTop at htR
  rw [htR] at hsq
  have hphi' : (unit (TopCat.of U) A n).app (op ⊤) phiTop = eS sR := by
    exact (globalCochainUnit_apply (TopCat.of U) A n phi).symm.trans hphi
  rw [hphi'] at hsq
  have hnat :
      (unit X A n).app (op U) t =
        (sheaf X A n).obj.map (eqToHom hOp)
          ((unit X A n).app
            (op ((TopCat.Sheaf.OpenRestriction.openImage U).obj ⊤)) tR) := by
    exact congrArg (fun q => q tR)
      ((unit X A n).naturality (eqToHom hOp))
  rw [hnat]
  have hu :
      (unit X A n).app
          (op ((TopCat.Sheaf.OpenRestriction.openImage U).obj ⊤)) tR = sR := by
    let eApp := ((TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of U)).mapIso
      (sheafIso U A n)).app (op (⊤ : Opens U))
    change eApp.hom _ = eApp.hom _ at hsq
    exact eApp.addCommGroupIsoToAddEquiv.injective hsq
  exact (congrArg rS hu).trans (rS.apply_symm_apply s)

/-- On a space whose open subspaces are normal and paracompact, every sheafified native
singular-cochain sheaf is flasque. -/
theorem isFlasque_of_open_normal_paracompact
    [∀ V : Opens X, NormalSpace V]
    [∀ V : Opens X, ParacompactSpace V] :
    (sheaf X A n).IsFlasque := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨tV, htV⟩ := unit_app_surjective V.unop A n s
  obtain ⟨tU, htU⟩ := presheaf_map_surjective A n i tV
  refine ⟨(unit X A n).app U tU, ?_⟩
  have hnat := congrArg (fun q => q tU) ((unit X A n).naturality i)
  change (unit X A n).app V ((presheaf X A n).map i tU) =
    (sheaf X A n).obj.map i ((unit X A n).app U tU) at hnat
  rw [htU, htV] at hnat
  exact hnat.symm

/-- In particular, every sheafified native singular-cochain sheaf on a metrizable space is
flasque. -/
theorem isFlasque_of_metrizable [MetrizableSpace X] :
    (sheaf X A n).IsFlasque := by
  let _ : ∀ V : Opens X, NormalSpace V := fun V => by
    let _ : MetrizableSpace V := Topology.IsEmbedding.subtypeVal.metrizableSpace
    infer_instance
  let _ : ∀ V : Opens X, ParacompactSpace V := fun V => by
    let _ : MetrizableSpace V := Topology.IsEmbedding.subtypeVal.metrizableSpace
    let _ : MetricSpace V := metrizableSpaceMetric V
    infer_instance
  exact isFlasque_of_open_normal_paracompact A n

end TopCat.SingularCochainSheaf.OpenRestriction
