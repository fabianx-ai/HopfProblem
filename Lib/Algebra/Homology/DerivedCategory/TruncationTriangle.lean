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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Below the cutoff, the canonical inclusion from the good truncation is an isomorphism on
components.  The boundary component itself is deliberately excluded: there the source is the
cycles object. -/
lemma isIso_ιTruncLE_f_of_lt (K : CochainComplex C ℤ) (n i : ℤ) (h : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  dsimp [CochainComplex.ιTruncLE, HomologicalComplex.ιTruncLE]
  change IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i).unop
  have hi : ∃ j, (ComplexShape.embeddingUpIntLE n).op.f j = i := by
    use Int.natAbs (n - i)
    change n - (Int.natAbs (n - i) : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  obtain ⟨j, hj⟩ := hi
  have hnb : ¬ (ComplexShape.embeddingUpIntLE n).op.BoundaryGE j := by
    rw [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hj0
    subst j
    simp at hj
    omega
  have hz := K.op.isIso_restrictionToTruncGE'
    (ComplexShape.embeddingUpIntLE n).op j hnb
  have hzi : IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i) := by
    subst i
    apply ((ComplexShape.embeddingUpIntLE n).op.isIso_liftExtend_f_iff
      (K.op.restrictionToTruncGE' (ComplexShape.embeddingUpIntLE n).op)
      (K.op.restrictionToTruncGE'_hasLift (ComplexShape.embeddingUpIntLE n).op) rfl).2
    exact hz
  infer_instance

/-- Above the cutoff, the canonical projection to the good truncation is an isomorphism on
components.  The boundary component itself is deliberately excluded: there the target is the
opcycles object. -/
lemma isIso_πTruncGE_f_of_lt (K : CochainComplex C ℤ) (n i : ℤ) (h : n < i) :
    IsIso ((K.πTruncGE n).f i) := by
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  have hi : ∃ j, (ComplexShape.embeddingUpIntGE n).f j = i := by
    use Int.natAbs (i - n)
    change n + (Int.natAbs (i - n) : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  obtain ⟨j, hj⟩ := hi
  have hnb : ¬ (ComplexShape.embeddingUpIntGE n).BoundaryGE j := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hj0
    subst j
    simp at hj
    omega
  apply ((ComplexShape.embeddingUpIntGE n).isIso_liftExtend_f_iff
    (K.restrictionToTruncGE' (ComplexShape.embeddingUpIntGE n))
    (K.restrictionToTruncGE'_hasLift (ComplexShape.embeddingUpIntGE n)) hj).2
  exact K.isIso_restrictionToTruncGE'
    (ComplexShape.embeddingUpIntGE n) j hnb

end CochainComplex

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

/-- The lower endpoint of the abstract truncation triangle is the derived image of the concrete
lower truncation. -/
def truncLTIsoQTruncLE (K : CochainComplex C ℤ) (n : ℤ) :
    (TStructure.t.truncLT n).obj (Q.obj K) ≅ Q.obj (K.truncLE (n - 1)) :=
  Triangle.π₁.mapIso (truncationTriangleIso K n)

/-- The upper endpoint of the abstract truncation triangle is the derived image of the concrete
upper truncation. -/
def truncGEIsoQTruncGE (K : CochainComplex C ℤ) (n : ℤ) :
    (TStructure.t.truncGE n).obj (Q.obj K) ≅ Q.obj (K.truncGE n) :=
  let e := truncationTriangleIso K n
  let e₃ : (TStructure.t.truncGE n).obj (Q.obj K) ≅
      Q.obj (K.shortComplexTruncLE (n - 1)).X₃ :=
    Triangle.π₃.mapIso e
  let eq : Q.obj (K.shortComplexTruncLE (n - 1)).X₃ ≅ Q.obj (K.truncGE n) :=
    asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)))
  e₃ ≪≫ eq

/-- The concrete connecting morphism from upper to shifted lower truncation. -/
def concreteTruncationδ (K : CochainComplex C ℤ) (n : ℤ) :
    Q.obj (K.truncGE n) ⟶ (Q.obj (K.truncLE (n - 1)))⟦(1 : ℤ)⟧ :=
  inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega))) ≫
    (triangleOfSES (K.shortComplexTruncLE_shortExact (n - 1))).mor₃

set_option backward.isDefEq.respectTransparency false

/-- The lower endpoint comparison commutes with the canonical inclusions into `Q.obj K`. -/
@[reassoc]
lemma truncLTIsoQTruncLE_hom_comp_ι (K : CochainComplex C ℤ) (n : ℤ) :
    (truncLTIsoQTruncLE K n).hom ≫ Q.map (K.ιTruncLE (n - 1)) =
      (TStructure.t.truncLTι n).app (Q.obj K) := by
  change (truncationTriangleIso K n).hom.hom₁ ≫
      Q.map (K.shortComplexTruncLE (n - 1)).f =
    (TStructure.t.truncLTι n).app (Q.obj K)
  have h := (truncationTriangleIso K n).hom.comm₁.symm
  rw [truncationTriangleIso_hom_hom₂] at h
  change (truncationTriangleIso K n).hom.hom₁ ≫
      Q.map (K.shortComplexTruncLE (n - 1)).f =
    (TStructure.t.truncLTι n).app (Q.obj K) ≫ 𝟙 (Q.obj K) at h
  exact h.trans (Category.comp_id _)

/-- The upper endpoint comparison commutes with the canonical projections from `Q.obj K`. -/
@[reassoc]
lemma truncGEπ_comp_truncGEIsoQTruncGE_hom (K : CochainComplex C ℤ) (n : ℤ) :
    (TStructure.t.truncGEπ n).app (Q.obj K) ≫ (truncGEIsoQTruncGE K n).hom =
      Q.map (K.πTruncGE n) := by
  change (TStructure.t.truncGEπ n).app (Q.obj K) ≫
      (truncationTriangleIso K n).hom.hom₃ ≫
        Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)) =
    Q.map (K.πTruncGE n)
  have h := (truncationTriangleIso K n).hom.comm₂_assoc
    (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)))
  rw [truncationTriangleIso_hom_hom₂] at h
  rw [TStructure.triangleLTGE_obj_mor₂, triangleOfSES_mor₂,
    ← Q.map_comp,
    K.g_shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)] at h
  change (TStructure.t.truncGEπ n).app (Q.obj K) ≫
      (truncationTriangleIso K n).hom.hom₃ ≫
        Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)) =
    𝟙 (Q.obj K) ≫ Q.map (K.πTruncGE n) at h
  exact h.trans (Category.id_comp _)

/-- Transporting the abstract t-structure connecting morphism through the endpoint comparisons
gives the connecting morphism of the concrete short exact truncation sequence, with no sign. -/
lemma concreteTruncationδ_eq (K : CochainComplex C ℤ) (n : ℤ) :
    (truncGEIsoQTruncGE K n).inv ≫
        (TStructure.t.truncGEδLT n).app (Q.obj K) ≫
          (truncLTIsoQTruncLE K n).hom⟦(1 : ℤ)⟧' =
      concreteTruncationδ K n := by
  let e := truncationTriangleIso K n
  dsimp only [truncGEIsoQTruncGE, truncLTIsoQTruncLE, concreteTruncationδ]
  simp only [Iso.trans_inv, asIso_inv, ← TStructure.triangleLTGE_obj_mor₃]
  have h := e.hom.comm₃
  change ((TStructure.t.triangleLTGE n).obj (Q.obj K)).mor₃ ≫
      (Triangle.π₁.map e.hom)⟦(1 : ℤ)⟧' =
    Triangle.π₃.map e.hom ≫
      (triangleOfSES (K.shortComplexTruncLE_shortExact (n - 1))).mor₃ at h
  dsimp only [e] at h
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [h]
  exact congrArg
    (fun k ↦ inv (Q.map
      (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega))) ≫ k)
    ((Triangle.π₃.mapIso (truncationTriangleIso K n)).inv_hom_id_assoc
      (triangleOfSES (K.shortComplexTruncLE_shortExact (n - 1))).mor₃)

end DerivedCategory
