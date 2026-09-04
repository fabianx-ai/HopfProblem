/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovSlice

/-!
# Naturality of the normalized single-homology comparison
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The chosen comparison from a single-degree derived object to its homology single is
normalized to induce the identity on degree-`n` homology. -/
@[reassoc]
theorem homologyFunctor_map_isoSingleFunctorHomology_hom (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    (homologyFunctor C n).map (isoSingleFunctorHomology K n).hom ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app
          ((homologyFunctor C n).obj K) =
      𝟙 ((homologyFunctor C n).obj K) := by
  let Y := (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose
  let e : K ≅ (singleFunctor C n).obj Y :=
    (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose_spec.some
  let hY : (homologyFunctor C n).obj K ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app Y
  change (homologyFunctor C n).map
      (e.hom ≫ (singleFunctor C n).map hY.inv) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app _ = 𝟙 _
  rw [Functor.map_comp, Category.assoc,
    ← Functor.comp_map, (singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc]
  change hY.hom ≫ hY.inv = 𝟙 _
  simp

end DerivedCategory
