/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.TruncationTriangle
public import Lib.Algebra.Homology.HomotopyCategory.TwoTermMappingCone

/-!
# The concrete adjacent two-slice complex

For an integer-indexed cochain complex `K`, the good truncation
`(K.truncLE (q + 1)).truncGE q` is concentrated in the adjacent degrees `q` and `q + 1`.
After shifting by `q + 1`, this file identifies it with the literal two-term complex on
`K.opcyclesToCycles q (q + 1)`, and hence with the corresponding mapping cone.

The shift convention contributes `(q + 1).negOnePow` on the degree `-1` component.  With that
normalization the unique nonzero differential is the positive map `opcyclesToCycles`; no extra
negation is introduced.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

section GenericEndpoints

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (L : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]

set_option backward.isDefEq.respectTransparency false in
/-- At the boundary of a good lower truncation, its canonical projection followed by the
canonical opcycles identification is the opcycles quotient. -/
lemma πTruncGE_f_boundary_generic {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : e.BoundaryGE i) :
    (L.πTruncGE e).f i' ≫ (L.truncGEXIsoOpcycles e hi' hi).hom =
      L.pOpcycles i' := by
  dsimp [HomologicalComplex.πTruncGE]
  rw [e.liftExtend_f _ _ hi']
  rw [L.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hi' hi]
  simp [HomologicalComplex.truncGEXIsoOpcycles]

set_option backward.isDefEq.respectTransparency false in
/-- In the interior of a good lower truncation, its canonical projection followed by the
canonical component identification is the identity. -/
lemma πTruncGE_f_interior_generic {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : ¬ e.BoundaryGE i) :
    (L.πTruncGE e).f i' ≫ (L.truncGEXIso e hi' hi).hom = 𝟙 _ := by
  dsimp [HomologicalComplex.πTruncGE]
  rw [e.liftExtend_f _ _ hi']
  rw [L.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hi' hi]
  simp [HomologicalComplex.truncGEXIso]

end GenericEndpoints

set_option backward.isDefEq.respectTransparency false in
/-- The boundary component of the integer-indexed good lower-truncation projection. -/
lemma πTruncGE_f_boundary (K : CochainComplex C ℤ) (n : ℤ) :
    (K.πTruncGE n).f n ≫ (K.truncGEXIsoOpcycles n).hom =
      K.pOpcycles n := by
  simpa [CochainComplex.πTruncGE, CochainComplex.truncGEXIsoOpcycles] using
    (πTruncGE_f_boundary_generic K (ComplexShape.embeddingUpIntGE n)
      (i := 0) (i' := n) (by simp) (by
        rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]))

set_option backward.isDefEq.respectTransparency false in
/-- An interior component of the integer-indexed good lower-truncation projection. -/
lemma πTruncGE_f_interior (K : CochainComplex C ℤ) (n i : ℤ)
    (h : n < i) :
    (K.πTruncGE n).f i ≫ (K.truncGEXIso n i h).hom = 𝟙 _ := by
  let j : ℕ := (i - n).natAbs
  have hj : n + (j : ℤ) = i := by
    dsimp [j]
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  simpa [CochainComplex.πTruncGE, CochainComplex.truncGEXIso] using
    (πTruncGE_f_interior_generic K (ComplexShape.embeddingUpIntGE n)
      (i := j) (i' := i) hj (by
        rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
        intro hz
        subst j
        simp at hj
        omega))

set_option backward.isDefEq.respectTransparency false in
/-- The boundary-to-interior differential of a good lower truncation, transported through its
canonical component identifications. -/
lemma truncGE_d_fromOpcycles (K : CochainComplex C ℤ) (n : ℤ) :
    (K.truncGEXIsoOpcycles n).hom ≫ K.fromOpcycles n (n + 1) =
      (K.truncGE n).d n (n + 1) ≫
        (K.truncGEXIso n (n + 1) (by omega)).hom := by
  have : Epi ((K.πTruncGE n).f n) := by
    dsimp [CochainComplex.πTruncGE]
    infer_instance
  rw [← cancel_epi ((K.πTruncGE n).f n)]
  rw [← Category.assoc, πTruncGE_f_boundary]
  rw [← Category.assoc, (K.πTruncGE n).comm]
  rw [Category.assoc, πTruncGE_f_interior]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The boundary component of the integer-indexed good upper-truncation inclusion is the cycles
inclusion after the canonical component identification. -/
lemma ιTruncLE_f_boundary (K : CochainComplex C ℤ) (n : ℤ) :
    (K.ιTruncLE n).f n =
      (K.truncLEXIsoCycles n).hom ≫ K.iCycles n := by
  apply Quiver.Hom.op_inj
  dsimp [CochainComplex.ιTruncLE, CochainComplex.truncLEXIsoCycles,
    HomologicalComplex.ιTruncLE, HomologicalComplex.truncLEXIsoCycles]
  change
    (K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f n =
      (K.iCycles n).op ≫ (K.opcyclesOpIso n).inv ≫
        (K.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE n).op
          (i := 0) (i' := n) (by simp) (by
            simpa using (show (ComplexShape.embeddingUpIntLE n).BoundaryLE 0 by
              rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]))).inv
  rw [← cancel_mono
    (K.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE n).op
      (i := 0) (i' := n) (by simp) (by
        simpa using (show (ComplexShape.embeddingUpIntLE n).BoundaryLE 0 by
          rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]))).hom]
  rw [πTruncGE_f_boundary_generic]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_mono (K.opcyclesOpIso n).hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (K.sc n).op.pOpcycles ≫ (K.sc n).opcyclesOpIso.hom =
    (K.sc n).iCycles.op
  exact (K.sc n).op_pOpcycles_opcyclesOpIso_hom

/-- The part of `K` lying in the adjacent good-truncation degrees `q` and `q + 1`. -/
abbrev adjacentTwoSlice (K : CochainComplex C ℤ) (q : ℤ) :
    CochainComplex C ℤ :=
  (K.truncLE (q + 1)).truncGE q

set_option backward.isDefEq.respectTransparency false in
/-- The unique potentially nonzero differential of the adjacent two-slice complex, transported
to the opcycles and cycles objects, is the natural map `opcyclesToCycles`. -/
lemma adjacentTwoSlice_d_eq (K : CochainComplex C ℤ) (q : ℤ) :
    ((K.truncLE (q + 1)).truncGEXIsoOpcycles q).hom ≫
        opcyclesMap (K.ιTruncLE (q + 1)) q ≫
          K.opcyclesToCycles q (q + 1) =
      (adjacentTwoSlice K q).d q (q + 1) ≫
        ((K.truncLE (q + 1)).truncGEXIso q (q + 1) (by omega)).hom ≫
          (K.truncLEXIsoCycles (q + 1)).hom := by
  rw [← cancel_mono (K.iCycles (q + 1))]
  simp only [opcyclesToCycles_naturality, Category.assoc, cyclesMap_i,
    opcyclesToCycles_iCycles_assoc]
  rw [← ιTruncLE_f_boundary]
  rw [← Category.assoc, truncGE_d_fromOpcycles]
  simp [adjacentTwoSlice, Category.assoc]

/-- The good upper-truncation inclusion induces an isomorphism on opcycles strictly below its
cutoff. -/
lemma isIso_opcyclesMap_ιTruncLE (K : CochainComplex C ℤ) (q : ℤ) :
    IsIso (opcyclesMap (K.ιTruncLE (q + 1)) q) := by
  apply ShortComplex.isIso_opcyclesMap_of_isIso_of_epi'
    ((shortComplexFunctor C (ComplexShape.up ℤ) q).map
      (K.ιTruncLE (q + 1)))
  · exact K.isIso_ιTruncLE_f_of_lt (q + 1) q (by omega)
  · dsimp [shortComplexFunctor]
    rw [CochainComplex.prev]
    have := K.isIso_ιTruncLE_f_of_lt (q + 1) (q - 1) (by omega)
    simpa using
      (inferInstanceAs (Epi ((K.ιTruncLE (q + 1)).f (q - 1))))

/-- The adjacent two-slice shifted so that its two possibly nonzero terms lie in degrees `-1`
and `0`. -/
abbrev shiftedAdjacentTwoSlice (K : CochainComplex C ℤ) (q : ℤ) :
    CochainComplex C ℤ :=
  (adjacentTwoSlice K q)⟦q + 1⟧

lemma shiftedAdjacentTwoSlice_isZero_X
    (K : CochainComplex C ℤ) (q i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((shiftedAdjacentTwoSlice K q).X i) := by
  let S := adjacentTwoSlice K q
  have hS : IsZero (S.X (i + (q + 1))) := by
    obtain hi | hi := lt_or_gt_of_ne hneg
    · exact S.isZero_of_isStrictlyGE q _ (by omega)
    · exact S.isZero_of_isStrictlyLE (q + 1) _ (by omega)
  exact IsZero.of_iso hS
    (S.shiftFunctorObjXIso (q + 1) i (i + (q + 1)) rfl).symm

noncomputable def shiftedTwoSlicePointIsoNegOne
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedAdjacentTwoSlice K q).X (-1) ≅
      (twoTerm (K.opcyclesToCycles q (q + 1))).X (-1) := by
  letI := isIso_opcyclesMap_ιTruncLE K q
  exact (q + 1).negOnePow •
    (adjacentTwoSlice K q).shiftFunctorObjXIso
        (q + 1) (-1) q (by omega) ≪≫
      (K.truncLE (q + 1)).truncGEXIsoOpcycles q ≪≫
        asIso (opcyclesMap (K.ιTruncLE (q + 1)) q) ≪≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (K.opcycles q)).symm

noncomputable def shiftedTwoSlicePointIsoZero
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedAdjacentTwoSlice K q).X 0 ≅
      (twoTerm (K.opcyclesToCycles q (q + 1))).X 0 :=
  (adjacentTwoSlice K q).shiftFunctorObjXIso
      (q + 1) 0 (q + 1) (by omega) ≪≫
    (K.truncLE (q + 1)).truncGEXIso q (q + 1) (by omega) ≪≫
      K.truncLEXIsoCycles (q + 1) ≪≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℕ) 0 (K.cycles (q + 1))).symm

noncomputable def shiftedTwoSlicePointIso
    (K : CochainComplex C ℤ) (q i : ℤ) :
    (shiftedAdjacentTwoSlice K q).X i ≅
      (twoTerm (K.opcyclesToCycles q (q + 1))).X i := by
  by_cases hneg : i = -1
  · subst i
    exact shiftedTwoSlicePointIsoNegOne K q
  by_cases hzero : i = 0
  · subst i
    exact shiftedTwoSlicePointIsoZero K q
  exact IsZero.iso
    (shiftedAdjacentTwoSlice_isZero_X K q i hneg hzero)
    (twoTerm_isZero_X _ i hneg hzero)

set_option backward.isDefEq.respectTransparency false

/-- The shifted adjacent two-slice is the literal two-term complex on the canonical
`opcyclesToCycles` morphism.  The parity scalar on the degree `-1` component exactly cancels the
sign in the cochain shift differential. -/
noncomputable def shiftedAdjacentTwoSliceIsoTwoTerm
    (K : CochainComplex C ℤ) (q : ℤ) :
    shiftedAdjacentTwoSlice K q ≅
      twoTerm (K.opcyclesToCycles q (q + 1)) :=
  Hom.isoOfComponents (shiftedTwoSlicePointIso K q) (by
    rintro i _ rfl
    by_cases hi : i = -1
    · subst i
      change (shiftedTwoSlicePointIsoNegOne K q).hom ≫
          K.opcyclesToCycles q (q + 1) =
        (shiftedAdjacentTwoSlice K q).d (-1) 0 ≫
          (shiftedTwoSlicePointIsoZero K q).hom
      rw [CochainComplex.shiftFunctor_obj_d']
      dsimp [shiftedTwoSlicePointIsoNegOne,
        shiftedTwoSlicePointIsoZero]
      simp only [Category.comp_id, Units.smul_def,
        Preadditive.zsmul_comp, Category.assoc]
      rw [adjacentTwoSlice_d_eq]
      simp only [HomologicalComplex.XIsoOfEq_hom_comp_d_assoc,
        HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
    by_cases hi' : i = -2
    · apply (shiftedAdjacentTwoSlice_isZero_X K q i (by omega) (by omega)).eq_of_src
    · apply (twoTerm_isZero_X (K.opcyclesToCycles q (q + 1))
        (i + 1) (by omega) (by omega)).eq_of_tgt)

/-- The shifted adjacent two-slice as the standard mapping cone of the canonical morphism between
degree-zero single complexes. -/
noncomputable def shiftedAdjacentTwoSliceIsoMappingCone
    (K : CochainComplex C ℤ) (q : ℤ) :
    shiftedAdjacentTwoSlice K q ≅
      mappingCone ((singleFunctor C 0).map
        (K.opcyclesToCycles q (q + 1))) :=
  shiftedAdjacentTwoSliceIsoTwoTerm K q ≪≫
    twoTermIsoMappingCone (K.opcyclesToCycles q (q + 1))

end CochainComplex
