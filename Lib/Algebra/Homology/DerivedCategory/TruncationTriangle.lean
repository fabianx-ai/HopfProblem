/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Concrete models for canonical derived truncation triangles

For a cochain complex `K`, this file compares the abstract truncation triangle selected by the
canonical t-structure on the derived category with the distinguished triangle of the concrete
short exact truncation sequence of `K`.  The comparison is normalized to be the identity on the
middle object.  Its third triangle square therefore records the exact compatibility between the
abstract truncation connecting morphism and the concrete short-exact-sequence connecting
morphism.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

/-- The abstract canonical truncation triangle is isomorphic to the distinguished triangle of
the concrete short exact truncation sequence.  The middle component is chosen to be the identity
on `Q.obj K`. -/
def truncationTriangleIso (K : CochainComplex C ℤ) (n : ℤ) :
    (TStructure.t.triangleLTGE n).obj (Q.obj K) ≅
      triangleOfSES (K.shortComplexTruncLE_shortExact (n - 1)) := by
  let S := K.shortComplexTruncLE (n - 1)
  let hS := K.shortComplexTruncLE_shortExact (n - 1)
  let e : Q.obj S.X₃ ≅ Q.obj (K.truncGE n) :=
    asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)))
  have hright : TStructure.t.IsGE (Q.obj S.X₃) n := by
    exact TStructure.t.isGE_of_iso e.symm n
  exact (TStructure.t.triangle_iso_exists
    (TStructure.t.triangleLTGE_distinguished n (Q.obj K))
    (triangleOfSES_distinguished hS) (Iso.refl _) (n - 1) n
    (by infer_instance) (by infer_instance)
    (by
      change TStructure.t.IsLE (Q.obj (K.truncLE (n - 1))) (n - 1)
      constructor
      exact ⟨K.truncLE (n - 1), Iso.refl _, inferInstance⟩) hright (by omega)).choose

@[simp]
theorem truncationTriangleIso_hom_hom₂ (K : CochainComplex C ℤ) (n : ℤ) :
    (truncationTriangleIso K n).hom.hom₂ = 𝟙 (Q.obj K) := by
  exact (TStructure.t.triangle_iso_exists
    (TStructure.t.triangleLTGE_distinguished n (Q.obj K))
    (triangleOfSES_distinguished (K.shortComplexTruncLE_shortExact (n - 1)))
    (Iso.refl _) (n - 1) n
    (by infer_instance) (by infer_instance)
    (by
      change TStructure.t.IsLE (Q.obj (K.truncLE (n - 1))) (n - 1)
      constructor
      exact ⟨K.truncLE (n - 1), Iso.refl _, inferInstance⟩)
    (by
      let S := K.shortComplexTruncLE (n - 1)
      let e : Q.obj S.X₃ ≅ Q.obj (K.truncGE n) :=
        asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)))
      exact TStructure.t.isGE_of_iso e.symm n)
    (by omega)).choose_spec

/-- The third square of `truncationTriangleIso`: the abstract truncation connecting morphism is
the concrete short-exact-sequence connecting morphism after transport along the two endpoint
components. -/
@[reassoc]
theorem truncationTriangleIso_hom_comm₃ (K : CochainComplex C ℤ) (n : ℤ) :
    ((TStructure.t.triangleLTGE n).obj (Q.obj K)).mor₃ ≫
        ((truncationTriangleIso K n).hom.hom₁)⟦(1 : ℤ)⟧' =
      (truncationTriangleIso K n).hom.hom₃ ≫
        (triangleOfSES (K.shortComplexTruncLE_shortExact (n - 1))).mor₃ := by
  exact (truncationTriangleIso K n).hom.comm₃

end DerivedCategory
