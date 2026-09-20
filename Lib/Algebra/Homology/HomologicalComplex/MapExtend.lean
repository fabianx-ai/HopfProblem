/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Additive functors commute with extension by zero

Given an embedding of complex shapes, extension inserts zero objects outside the image of the
embedding.  An additive functor preserves zero objects up to canonical isomorphism, so applying
the functor before or after extension gives isomorphic homological complexes.

This file supplies the objectwise component isomorphism and packages its compatibility with the
differentials.  No exactness or homology-preservation hypothesis is required.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe uC vC uD vD uι uι'

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
variable {F : Functor C D} [F.Additive]
variable {ι : Type uι} {ι' : Type uι'} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- Degreewise comparison between mapping an extended complex and extending a mapped complex. -/
def mapExtendXIso (K : HomologicalComplex C c) (e : c.Embedding c') (i' : ι') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).X i' ≅
      (((F.mapHomologicalComplex c).obj K).extend e).X i' :=
  match h : e.r i' with
  | none => IsZero.iso
      ((F.map_isZero (K.isZero_extend_X' e i' h)).of_iso
        (eqToIso (F.mapHomologicalComplex_obj_X c' (K.extend e) i')))
      (((F.mapHomologicalComplex c).obj K).isZero_extend_X' e i' h)
  | some i =>
      eqToIso (F.mapHomologicalComplex_obj_X c' (K.extend e) i') ≪≫
        F.mapIso (K.extendXIso e (e.f_eq_of_r_eq_some h)) ≪≫
          eqToIso (F.mapHomologicalComplex_obj_X c K i).symm ≪≫
            (((F.mapHomologicalComplex c).obj K).extendXIso e
              (e.f_eq_of_r_eq_some h)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An additive functor commutes with extension by zero, up to isomorphism of homological
complexes. -/
def mapExtendIso (K : HomologicalComplex C c) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso (F := F) K e)
    (fun i' j' hij => by
      generalize hi : e.r i' = oi
      generalize hj : e.r j' = oj
      cases oi with
      | none =>
          exact IsZero.eq_of_src
            (F.map_isZero (K.isZero_extend_X' e i' hi)) _ _
      | some i =>
        cases oj with
        | none =>
            exact IsZero.eq_of_tgt
              (((F.mapHomologicalComplex c).obj K).isZero_extend_X' e j' hj) _ _
        | some j =>
          have hfi : e.f i = i' := e.f_eq_of_r_eq_some hi
          have hfj : e.f j = j' := e.f_eq_of_r_eq_some hj
          simp only [mapExtendXIso]
          split
          · rename_i h
            rw [hi] at h
            simp at h
          · rename_i i₀ h
            have hi₀ : i₀ = i := by
              rw [hi] at h
              exact (Option.some.inj h).symm
            subst i₀
            split
            · rename_i h
              rw [hj] at h
              simp at h
            · rename_i j₀ h
              have hj₀ : j₀ = j := by
                rw [hj] at h
                exact (Option.some.inj h).symm
              subst j₀
              rw [F.mapHomologicalComplex_obj_d]
              rw [K.extend_d_eq e hfi hfj,
                ((F.mapHomologicalComplex c).obj K).extend_d_eq e hfi hfj]
              simp [Functor.map_comp])

end HomologicalComplex
