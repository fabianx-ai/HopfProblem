/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.ColimitCoefficients
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Degree-zero Cech cohomology and global sections

This file formalizes textbook section CD-05A, equations (C7)--(C8). For every topological space,
abelian sheaf, and set-valued open cover, the normalized degree-zero Cech cocycles are exactly the
compatible families of local sections. The sheaf gluing and uniqueness axioms therefore identify
fixed-cover degree-zero Cech cohomology with global sections. The identification commutes with
every refinement transition and with morphisms of coefficient sheaves, so it descends to a
coefficient-natural isomorphism from refinement-directed degree-zero Cech cohomology to global
sections.

No separation or paracompactness hypothesis is used, and no positive-degree comparison with
derived sheaf cohomology is made here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace TopologicalSpace.OpenCover

private def OrderedSimplex.vertex {ι : Type u} [LinearOrder ι] (i : ι) :
    OrderedSimplex ι 0 :=
  OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (by
    intro a b h
    omega)

@[simp]
private theorem OrderedSimplex.vertex_apply {ι : Type u} [LinearOrder ι] (i : ι)
    (j : Fin 1) :
    OrderedSimplex.vertex i j = i := rfl

@[simp]
private theorem OrderedSimplex.intersection_vertex {X : Type u} [TopologicalSpace X]
    {ι : Type v} [LinearOrder ι] (U : ι → TopologicalSpace.Opens X) (i : ι) :
    (OrderedSimplex.vertex i).intersection U = U i := by
  simp [OrderedSimplex.intersection]

private theorem OrderedSimplex.eq_vertex {ι : Type u} [LinearOrder ι]
    (σ : OrderedSimplex ι 0) : σ = OrderedSimplex.vertex (σ 0) := by
  ext j
  fin_cases j
  rfl

private def OrderedSimplex.edge {ι : Type u} [o : LinearOrder ι] {i j : ι}
    (h : o.lt i j) :
    OrderedSimplex ι 1 :=
  OrderEmbedding.ofStrictMono (fun k : Fin 2 => if k = 0 then i else j) (by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals simp_all)

@[simp]
private theorem OrderedSimplex.edge_zero {ι : Type u} [o : LinearOrder ι] {i j : ι}
    (h : o.lt i j) :
    OrderedSimplex.edge h 0 = i := rfl

@[simp]
private theorem OrderedSimplex.edge_one {ι : Type u} [o : LinearOrder ι] {i j : ι}
    (h : o.lt i j) :
    OrderedSimplex.edge h 1 = j := rfl

@[simp]
private theorem OrderedSimplex.edge_face_zero {ι : Type u} [o : LinearOrder ι] {i j : ι}
    (h : o.lt i j) :
    (OrderedSimplex.edge h).face 0 = OrderedSimplex.vertex j := by
  ext k
  fin_cases k
  rfl

@[simp]
private theorem OrderedSimplex.edge_face_one {ι : Type u} [o : LinearOrder ι] {i j : ι}
    (h : o.lt i j) :
    (OrderedSimplex.edge h).face 1 = OrderedSimplex.vertex i := by
  ext k
  fin_cases k
  rfl

@[simp]
private theorem OrderedSimplex.intersection_edge {X : Type u} [TopologicalSpace X]
    {ι : Type v} [o : LinearOrder ι] (U : ι → TopologicalSpace.Opens X)
    {i j : ι} (h : o.lt i j) :
    (OrderedSimplex.edge h).intersection U = U i ⊓ U j := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf
    intro k
    fin_cases k <;> simp

end TopologicalSpace.OpenCover

namespace TopologicalSpace.OpenCover.SetOpenCover

open TopologicalSpace

variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{max u v} X) (U : SetOpenCover X)

/-- Restriction of a global section to every normalized degree-zero component. -/
noncomputable def globalToZeroCochain :
    F.presheaf.obj (op (⊤ : Opens X)) ⟶
      OrderedCech.object F.presheaf U.family 0 :=
  Limits.Pi.lift fun _σ => F.presheaf.map (homOfLE le_top).op

@[reassoc (attr := simp)]
theorem globalToZeroCochain_π (σ : OrderedSimplex U.Index 0) :
    globalToZeroCochain F U ≫ OrderedCech.π F.presheaf U.family 0 σ =
      F.presheaf.map (homOfLE le_top : σ.intersection U.family ⟶ ⊤).op := by
  exact Limits.Pi.lift_π _ _

theorem globalToZeroCochain_comp_differential :
    globalToZeroCochain F U ≫ OrderedCech.differential F.presheaf U.family 0 = 0 := by
  apply Limits.Pi.hom_ext
  intro σ
  rw [zero_comp]
  change globalToZeroCochain F U ≫
    (OrderedCech.differential F.presheaf U.family 0 ≫
      OrderedCech.π F.presheaf U.family 1 σ) = 0
  rw [OrderedCech.differential_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    globalToZeroCochain_π_assoc]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  have hmap :
      F.presheaf.map ((homOfLE le_top).op ≫
          (OrderedSimplex.faceHom U.family σ 0).op) =
        F.presheaf.map ((homOfLE le_top).op ≫
          (OrderedSimplex.faceHom U.family σ 1).op) := by
    congr 1
  rw [hmap, add_neg_cancel]

/-- Global restriction viewed as a normalized degree-zero cocycle. -/
noncomputable def globalToZeroCycles :
    F.presheaf.obj (op (⊤ : Opens X)) ⟶
      (normalizedCechComplex F.presheaf U).cycles 0 :=
  (normalizedCechComplex F.presheaf U).liftCycles
    (globalToZeroCochain F U) 1 (by simp) (by
      simpa only [normalizedCechComplex, OrderedCech.complex_d] using
        globalToZeroCochain_comp_differential F U)

@[reassoc (attr := simp)]
theorem globalToZeroCycles_iCycles :
    globalToZeroCycles F U ≫
        (normalizedCechComplex F.presheaf U).iCycles 0 =
      globalToZeroCochain F U := by
  dsimp only [globalToZeroCycles]
  apply HomologicalComplex.liftCycles_i

/-- Transport from the singleton ordered intersection to its cover member. -/
private noncomputable def zeroVertexTransport (i : U.Index) :
    F.presheaf.obj (op ((OrderedSimplex.vertex i).intersection U.family)) ⟶
      F.presheaf.obj (op (U.family i)) :=
  F.presheaf.map
    (eqToHom (congrArg op (OrderedSimplex.intersection_vertex U.family i)))

/-- Restriction of a normalized zero-cocycle to one cover member. -/
private noncomputable def zeroCycleRestrictionAt (i : U.Index) :
    (normalizedCechComplex F.presheaf U).cycles 0 ⟶
      F.presheaf.obj (op (U.family i)) :=
  (normalizedCechComplex F.presheaf U).iCycles 0 ≫
    OrderedCech.π F.presheaf U.family 0 (OrderedSimplex.vertex i) ≫
      zeroVertexTransport F U i

/-- The indexed family represented by a normalized degree-zero cocycle. -/
private noncomputable def zeroCycleFamily
    (z : ToType ((normalizedCechComplex F.presheaf U).cycles 0))
    (i : U.Index) : ToType (F.presheaf.obj (op (U.family i))) :=
  zeroCycleRestrictionAt F U i z

/-- Transport from an ordered edge intersection to the corresponding binary intersection. -/
private noncomputable def zeroEdgeTransport {i j : U.Index}
    (h : (indexLinearOrder U).lt i j) :
    F.presheaf.obj (op ((OrderedSimplex.edge h).intersection U.family)) ⟶
      F.presheaf.obj (op (U.family i ⊓ U.family j)) :=
  F.presheaf.map
    (eqToHom (congrArg op (OrderedSimplex.intersection_edge U.family h)))

private noncomputable def zeroEdgeTerm {i j : U.Index}
    (h : (indexLinearOrder U).lt i j) (k : Fin 2) :
    (normalizedCechComplex F.presheaf U).cycles 0 ⟶
      F.presheaf.obj (op (U.family i ⊓ U.family j)) :=
  (normalizedCechComplex F.presheaf U).iCycles 0 ≫
    OrderedCech.π F.presheaf U.family 0 ((OrderedSimplex.edge h).face k) ≫
      F.presheaf.map ((OrderedSimplex.edge h).faceHom U.family k).op ≫
        zeroEdgeTransport F U h

private theorem zeroEdgeTerm_zero {i j : U.Index}
    (h : (indexLinearOrder U).lt i j) :
    zeroEdgeTerm F U h 0 =
      zeroCycleRestrictionAt F U j ≫
        F.presheaf.map (Opens.infLERight (U.family i) (U.family j)).op := by
  simp only [zeroEdgeTerm, zeroCycleRestrictionAt, zeroVertexTransport,
    zeroEdgeTransport, Category.assoc,
    ← F.presheaf.map_comp]
  congr 1

private theorem zeroEdgeTerm_one {i j : U.Index}
    (h : (indexLinearOrder U).lt i j) :
    zeroEdgeTerm F U h 1 =
      zeroCycleRestrictionAt F U i ≫
        F.presheaf.map (Opens.infLELeft (U.family i) (U.family j)).op := by
  simp only [zeroEdgeTerm, zeroCycleRestrictionAt, zeroVertexTransport,
    zeroEdgeTransport, Category.assoc,
    ← F.presheaf.map_comp]
  let p : op (((OrderedSimplex.edge h).face 1).intersection U.family) =
      op ((OrderedSimplex.vertex i).intersection U.family) :=
    congrArg (fun σ => op (σ.intersection U.family))
      (OrderedSimplex.edge_face_one h)
  have hπ :
      OrderedCech.π F.presheaf U.family 0 ((OrderedSimplex.edge h).face 1) ≫
          F.presheaf.map (eqToHom p) =
        OrderedCech.π F.presheaf U.family 0 (OrderedSimplex.vertex i) := by
    rw [eqToHom_map]
    exact Limits.Pi.π_comp_eqToHom
      (fun σ : OrderedSimplex U.Index 0 =>
        F.presheaf.obj (op (σ.intersection U.family)))
      (OrderedSimplex.edge_face_one h)
  rw [← hπ]
  simp only [← F.presheaf.map_comp, Category.assoc]
  congr 1

private theorem zeroCycleFamily_isCompatible
    (z : ToType ((normalizedCechComplex F.presheaf U).cycles 0)) :
    TopCat.Presheaf.IsCompatible F.presheaf U.family
      (zeroCycleFamily F U z) := by
  intro i j
  rcases @lt_trichotomy U.Index (indexLinearOrder U) i j with hij | hij | hij
  · let σ : OrderedSimplex U.Index 1 := OrderedSimplex.edge hij
    have hz : zeroEdgeTerm F U hij 0 - zeroEdgeTerm F U hij 1 = 0 := by
      have hraw := (normalizedCechComplex F.presheaf U).iCycles_d 0 1 =≫
        OrderedCech.π F.presheaf U.family 1 σ
      rw [zero_comp, Category.assoc] at hraw
      dsimp only [normalizedCechComplex] at hraw
      rw [OrderedCech.complex_d, OrderedCech.differential_π] at hraw
      rw [Fin.sum_univ_two] at hraw
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
        neg_smul, Preadditive.comp_add, Preadditive.comp_neg] at hraw
      have hraw' := hraw =≫ zeroEdgeTransport F U hij
      simpa only [zeroEdgeTerm, σ, normalizedCechComplex, sub_eq_add_neg,
        Category.assoc, Preadditive.add_comp, Preadditive.neg_comp, zero_comp] using hraw'
    have hterms := sub_eq_zero.mp hz
    rw [zeroEdgeTerm_zero, zeroEdgeTerm_one] at hterms
    simpa only [zeroCycleFamily, ← ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom hterms z).symm
  · subst j
    rfl
  · let σ : OrderedSimplex U.Index 1 := OrderedSimplex.edge hij
    have hz : zeroEdgeTerm F U hij 0 - zeroEdgeTerm F U hij 1 = 0 := by
      have hraw := (normalizedCechComplex F.presheaf U).iCycles_d 0 1 =≫
        OrderedCech.π F.presheaf U.family 1 σ
      rw [zero_comp, Category.assoc] at hraw
      dsimp only [normalizedCechComplex] at hraw
      rw [OrderedCech.complex_d, OrderedCech.differential_π] at hraw
      rw [Fin.sum_univ_two] at hraw
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
        neg_smul, Preadditive.comp_add, Preadditive.comp_neg] at hraw
      have hraw' := hraw =≫ zeroEdgeTransport F U hij
      simpa only [zeroEdgeTerm, σ, normalizedCechComplex, sub_eq_add_neg,
        Category.assoc, Preadditive.add_comp, Preadditive.neg_comp, zero_comp] using hraw'
    have hterms := sub_eq_zero.mp hz
    rw [zeroEdgeTerm_zero, zeroEdgeTerm_one] at hterms
    let p : op (U.family j ⊓ U.family i) = op (U.family i ⊓ U.family j) :=
      congrArg op (inf_comm (U.family j) (U.family i))
    have hc := congrArg (F.presheaf.map (eqToHom p))
      (ConcreteCategory.congr_hom hterms z)
    simp only [← ConcreteCategory.comp_apply, Category.assoc,
      ← F.presheaf.map_comp] at hc
    have hi :
        F.presheaf.map
            ((Opens.infLERight (U.family j) (U.family i)).op ≫ eqToHom p) =
          F.presheaf.map (Opens.infLELeft (U.family i) (U.family j)).op := by
      congr 1
    have hj :
        F.presheaf.map
            ((Opens.infLELeft (U.family j) (U.family i)).op ≫ eqToHom p) =
          F.presheaf.map (Opens.infLERight (U.family i) (U.family j)).op := by
      congr 1
    rw [hi, hj] at hc
    simpa only [zeroCycleFamily, ← ConcreteCategory.comp_apply] using hc

@[reassoc (attr := simp)]
private theorem globalToZeroCycles_zeroCycleRestrictionAt (i : U.Index) :
    globalToZeroCycles F U ≫ zeroCycleRestrictionAt F U i =
      F.presheaf.map (homOfLE le_top : U.family i ⟶ ⊤).op := by
  simp only [zeroCycleRestrictionAt,
    globalToZeroCycles_iCycles_assoc, globalToZeroCochain_π_assoc,
    zeroVertexTransport, ← F.presheaf.map_comp]
  congr 1

private theorem globalToZeroCochain_comp_alternatingEvaluation
    (f : Fin 1 → U.Index) :
    globalToZeroCochain F U ≫
        OrderedCech.alternatingEvaluation F.presheaf U.family 0 f =
      F.presheaf.map
        (homOfLE le_top : IndexTuple.intersection U.family f ⟶ ⊤).op := by
  have hf : Function.Injective f := fun a b _ => Subsingleton.elim a b
  rw [OrderedCech.alternatingEvaluation_of_injective F.presheaf U.family 0 f hf]
  have hsign : (Equiv.Perm.sign (Tuple.sort f) : ℤ) = 1 := by
    rw [Subsingleton.elim (Tuple.sort f) (Equiv.refl _)]
    simp
  rw [hsign]
  simp only [one_smul, globalToZeroCochain_π_assoc,
    ← F.presheaf.map_comp]
  congr 1

private theorem globalToZeroCochain_comp_refinementMapDegree
    {V : SetOpenCover X} (r : Refinement V.family U.family) :
    globalToZeroCochain F U ≫
        OrderedCech.refinementMapDegree F.presheaf r 0 =
      globalToZeroCochain F V := by
  apply Limits.Pi.hom_ext
  intro σ
  change globalToZeroCochain F U ≫
      (OrderedCech.refinementMapDegree F.presheaf r 0 ≫
        OrderedCech.π F.presheaf V.family 0 σ) =
    globalToZeroCochain F V ≫ OrderedCech.π F.presheaf V.family 0 σ
  rw [OrderedCech.refinementMapDegree_π,
    globalToZeroCochain_π]
  rw [← Category.assoc, globalToZeroCochain_comp_alternatingEvaluation]
  simp only [← F.presheaf.map_comp]
  congr 1

private theorem globalToZeroCycles_comp_cyclesMap
    {V : SetOpenCover X} (r : Refinement V.family U.family) :
    globalToZeroCycles F U ≫
        HomologicalComplex.cyclesMap (OrderedCech.refinementMap F.presheaf r) 0 =
      globalToZeroCycles F V := by
  rw [← cancel_mono ((normalizedCechComplex F.presheaf V).iCycles 0)]
  calc
    (globalToZeroCycles F U ≫
          HomologicalComplex.cyclesMap (OrderedCech.refinementMap F.presheaf r) 0) ≫
        (normalizedCechComplex F.presheaf V).iCycles 0 =
      globalToZeroCycles F U ≫
        ((normalizedCechComplex F.presheaf U).iCycles 0 ≫
          (OrderedCech.refinementMap F.presheaf r).f 0) := by
            dsimp only [normalizedCechComplex]
            rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    _ = (globalToZeroCycles F U ≫
          (normalizedCechComplex F.presheaf U).iCycles 0) ≫
        (OrderedCech.refinementMap F.presheaf r).f 0 :=
      (Category.assoc _ _ _).symm
    _ = globalToZeroCochain F U ≫
        OrderedCech.refinementMapDegree F.presheaf r 0 := by
      rw [globalToZeroCycles_iCycles]
      rfl
    _ = globalToZeroCochain F V :=
      globalToZeroCochain_comp_refinementMapDegree F U r
    _ = globalToZeroCycles F V ≫
        (normalizedCechComplex F.presheaf V).iCycles 0 :=
      (globalToZeroCycles_iCycles F V).symm

private theorem globalToZeroCycles_injective :
    Function.Injective (globalToZeroCycles F U) := by
  intro s t hst
  apply F.eq_of_locally_eq' U.family ⊤ (fun _ => homOfLE le_top)
    (by rw [U.isOpenCover.iSup_eq_top])
  intro i
  have hi := congrArg (zeroCycleRestrictionAt F U i) hst
  simpa only [← ConcreteCategory.comp_apply,
    globalToZeroCycles_zeroCycleRestrictionAt] using hi

private theorem zeroCycles_ext
    {z w : ToType ((normalizedCechComplex F.presheaf U).cycles 0)}
    (h : ∀ i, zeroCycleRestrictionAt F U i z = zeroCycleRestrictionAt F U i w) :
    z = w := by
  apply (AddCommGrpCat.mono_iff_injective
    ((normalizedCechComplex F.presheaf U).iCycles 0)).mp (by infer_instance)
  apply (Limits.Concrete.productEquiv
    (fun σ : OrderedSimplex U.Index 0 =>
      F.presheaf.obj (op (σ.intersection U.family)))).injective
  funext σ
  simp only [Limits.Concrete.productEquiv_apply_apply]
  have hπ :
      OrderedCech.π F.presheaf U.family 0 (OrderedSimplex.vertex (σ 0))
          ((normalizedCechComplex F.presheaf U).iCycles 0 z) =
        OrderedCech.π F.presheaf U.family 0 (OrderedSimplex.vertex (σ 0))
          ((normalizedCechComplex F.presheaf U).iCycles 0 w) := by
    let _ : IsIso (zeroVertexTransport F U (σ 0)) := by
      dsimp only [zeroVertexTransport]
      infer_instance
    apply ((ConcreteCategory.isIso_iff_bijective
      (zeroVertexTransport F U (σ 0))).mp (by infer_instance)).injective
    simpa only [zeroCycleRestrictionAt, ConcreteCategory.comp_apply] using h (σ 0)
  rw [← σ.eq_vertex] at hπ
  exact hπ

private theorem globalToZeroCycles_surjective :
    Function.Surjective (globalToZeroCycles F U) := by
  intro z
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' U.family ⊤
    (fun _ => homOfLE le_top) (by rw [U.isOpenCover.iSup_eq_top])
    (zeroCycleFamily F U z) (zeroCycleFamily_isCompatible F U z)
  refine ⟨s, zeroCycles_ext F U fun i => ?_⟩
  simpa only [zeroCycleFamily, ← ConcreteCategory.comp_apply,
    globalToZeroCycles_zeroCycleRestrictionAt] using hs i

private theorem globalToZeroCycles_bijective :
    Function.Bijective (globalToZeroCycles F U) :=
  ⟨globalToZeroCycles_injective F U, globalToZeroCycles_surjective F U⟩

theorem globalToZeroCycles_isIso :
    IsIso (globalToZeroCycles F U) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (globalToZeroCycles_bijective F U)

/-- Fixed-cover normalized degree-zero Cech cohomology is global sections. The inverse is
restriction of a global section to the cover, while the forward map is sheaf gluing. -/
noncomputable def normalizedCechCohomologyZeroIsoGlobalSections :
    normalizedCechCohomology F.presheaf U 0 ≅
      F.presheaf.obj (op (⊤ : Opens X)) := by
  let _ : IsIso (globalToZeroCycles F U) := globalToZeroCycles_isIso F U
  exact ((asIso (globalToZeroCycles F U)) ≪≫
    (normalizedCechComplex F.presheaf U).isoHomologyπ₀).symm

@[simp]
private theorem normalizedCechCohomologyZeroIsoGlobalSections_inv :
    (normalizedCechCohomologyZeroIsoGlobalSections F U).inv =
      globalToZeroCycles F U ≫
        (normalizedCechComplex F.presheaf U).isoHomologyπ₀.hom :=
  rfl

private theorem normalizedCechCohomologyZeroIsoGlobalSections_inv_comp_homologyMap
    {V : SetOpenCover X} (r : Refinement V.family U.family) :
    (normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
        HomologicalComplex.homologyMap
          (OrderedCech.refinementMap F.presheaf r) 0 =
      (normalizedCechCohomologyZeroIsoGlobalSections F V).inv := by
  change (globalToZeroCycles F U ≫
      (normalizedCechComplex F.presheaf U).homologyπ 0) ≫
        HomologicalComplex.homologyMap
          (OrderedCech.refinementMap F.presheaf r) 0 =
    globalToZeroCycles F V ≫
      (normalizedCechComplex F.presheaf V).homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, globalToZeroCycles_comp_cyclesMap]
  rfl

@[reassoc (attr := simp)]
private theorem normalizedCechCohomologyZeroIsoGlobalSections_inv_comp_refinement
    {V : SetOpenCover X} (h : U ≤ V) :
    (normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
        normalizedCechCohomologyMap F.presheaf h 0 =
      (normalizedCechCohomologyZeroIsoGlobalSections F V).inv := by
  rw [normalizedCechCohomologyMap_eq F.presheaf h (refinementOfLE h) 0]
  exact normalizedCechCohomologyZeroIsoGlobalSections_inv_comp_homologyMap
    F U (refinementOfLE h)

/-- Under the fixed-cover degree-zero identification, every refinement transition is the
identity on global sections. -/
@[reassoc (attr := simp)]
theorem normalizedCechCohomologyMap_comp_zeroIsoGlobalSections
    {V : SetOpenCover X} (h : U ≤ V) :
    normalizedCechCohomologyMap F.presheaf h 0 ≫
        (normalizedCechCohomologyZeroIsoGlobalSections F V).hom =
      (normalizedCechCohomologyZeroIsoGlobalSections F U).hom := by
  rw [← cancel_epi (normalizedCechCohomologyZeroIsoGlobalSections F U).inv]
  rw [← Category.assoc,
    normalizedCechCohomologyZeroIsoGlobalSections_inv_comp_refinement,
    Iso.inv_hom_id, Iso.inv_hom_id]

private theorem coefficientMap_comp_globalToZeroCochain
    {G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (f : F ⟶ G) :
    f.hom.app (op (⊤ : Opens X)) ≫ globalToZeroCochain G U =
      globalToZeroCochain F U ≫
        OrderedCech.coefficientMapDegree f.hom U.family 0 := by
  apply Limits.Pi.hom_ext
  intro σ
  change f.hom.app (op (⊤ : Opens X)) ≫
      (globalToZeroCochain G U ≫
        OrderedCech.π G.presheaf U.family 0 σ) =
    globalToZeroCochain F U ≫
      (OrderedCech.coefficientMapDegree f.hom U.family 0 ≫
        OrderedCech.π G.presheaf U.family 0 σ)
  rw [globalToZeroCochain_π, OrderedCech.coefficientMapDegree_π]
  rw [← Category.assoc, globalToZeroCochain_π]
  exact (f.hom.naturality
    (homOfLE le_top : σ.intersection U.family ⟶ ⊤).op).symm

private theorem coefficientMap_comp_globalToZeroCycles
    {G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (f : F ⟶ G) :
    f.hom.app (op (⊤ : Opens X)) ≫ globalToZeroCycles G U =
      globalToZeroCycles F U ≫
        HomologicalComplex.cyclesMap
          (OrderedCech.coefficientMap f.hom U.family) 0 := by
  rw [← cancel_mono ((normalizedCechComplex G.presheaf U).iCycles 0)]
  calc
    (f.hom.app (op (⊤ : Opens X)) ≫ globalToZeroCycles G U) ≫
        (normalizedCechComplex G.presheaf U).iCycles 0 =
      f.hom.app (op (⊤ : Opens X)) ≫
        (globalToZeroCycles G U ≫
          (normalizedCechComplex G.presheaf U).iCycles 0) :=
      Category.assoc _ _ _
    _ = f.hom.app (op (⊤ : Opens X)) ≫ globalToZeroCochain G U := by
      rw [globalToZeroCycles_iCycles]
    _ = globalToZeroCochain F U ≫
        OrderedCech.coefficientMapDegree f.hom U.family 0 :=
      coefficientMap_comp_globalToZeroCochain F U f
    _ = (globalToZeroCycles F U ≫
          (normalizedCechComplex F.presheaf U).iCycles 0) ≫
        (OrderedCech.coefficientMap f.hom U.family).f 0 := by
      rw [globalToZeroCycles_iCycles]
      rfl
    _ = globalToZeroCycles F U ≫
        ((normalizedCechComplex F.presheaf U).iCycles 0 ≫
          (OrderedCech.coefficientMap f.hom U.family).f 0) :=
      Category.assoc _ _ _
    _ = globalToZeroCycles F U ≫
        (HomologicalComplex.cyclesMap
            (OrderedCech.coefficientMap f.hom U.family) 0 ≫
          (normalizedCechComplex G.presheaf U).iCycles 0) := by
      dsimp only [normalizedCechComplex]
      rw [HomologicalComplex.cyclesMap_i]
    _ = (globalToZeroCycles F U ≫
          HomologicalComplex.cyclesMap
            (OrderedCech.coefficientMap f.hom U.family) 0) ≫
        (normalizedCechComplex G.presheaf U).iCycles 0 :=
      (Category.assoc _ _ _).symm

@[reassoc (attr := simp)]
private theorem globalSectionsMap_comp_zeroIsoGlobalSections_inv
    {G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (f : F ⟶ G) :
    f.hom.app (op (⊤ : Opens X)) ≫
        (normalizedCechCohomologyZeroIsoGlobalSections G U).inv =
      (normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
        normalizedCechCohomologyCoefficientMap f.hom U 0 := by
  change f.hom.app (op (⊤ : Opens X)) ≫
      (globalToZeroCycles G U ≫
        (normalizedCechComplex G.presheaf U).homologyπ 0) =
    (globalToZeroCycles F U ≫
      (normalizedCechComplex F.presheaf U).homologyπ 0) ≫
        HomologicalComplex.homologyMap
          (OrderedCech.coefficientMap f.hom U.family) 0
  calc
    f.hom.app (op (⊤ : Opens X)) ≫
        (globalToZeroCycles G U ≫
          (normalizedCechComplex G.presheaf U).homologyπ 0) =
      (f.hom.app (op (⊤ : Opens X)) ≫ globalToZeroCycles G U) ≫
        (normalizedCechComplex G.presheaf U).homologyπ 0 :=
      (Category.assoc _ _ _).symm

    _ = (globalToZeroCycles F U ≫
          HomologicalComplex.cyclesMap
            (OrderedCech.coefficientMap f.hom U.family) 0) ≫
        (normalizedCechComplex G.presheaf U).homologyπ 0 := by
      rw [coefficientMap_comp_globalToZeroCycles]
    _ = globalToZeroCycles F U ≫
        (HomologicalComplex.cyclesMap
            (OrderedCech.coefficientMap f.hom U.family) 0 ≫
          (normalizedCechComplex G.presheaf U).homologyπ 0) :=
      Category.assoc _ _ _
    _ = globalToZeroCycles F U ≫
        ((normalizedCechComplex F.presheaf U).homologyπ 0 ≫
          HomologicalComplex.homologyMap
            (OrderedCech.coefficientMap f.hom U.family) 0) := by
      dsimp only [normalizedCechComplex]
      rw [HomologicalComplex.homologyπ_naturality]
    _ = (globalToZeroCycles F U ≫
          (normalizedCechComplex F.presheaf U).homologyπ 0) ≫
        HomologicalComplex.homologyMap
          (OrderedCech.coefficientMap f.hom U.family) 0 :=
      (Category.assoc _ _ _).symm

/-- The fixed-cover degree-zero identification is natural in the abelian-sheaf coefficient. -/
@[reassoc (attr := simp)]
theorem normalizedCechCohomologyCoefficientMap_comp_zeroIsoGlobalSections
    {G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (f : F ⟶ G) :
    normalizedCechCohomologyCoefficientMap f.hom U 0 ≫
        (normalizedCechCohomologyZeroIsoGlobalSections G U).hom =
      (normalizedCechCohomologyZeroIsoGlobalSections F U).hom ≫
        f.hom.app (op (⊤ : Opens X)) := by
  rw [← cancel_epi (normalizedCechCohomologyZeroIsoGlobalSections F U).inv]
  calc
    (normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
        (normalizedCechCohomologyCoefficientMap f.hom U 0 ≫
          (normalizedCechCohomologyZeroIsoGlobalSections G U).hom) =
      ((normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
          normalizedCechCohomologyCoefficientMap f.hom U 0) ≫
        (normalizedCechCohomologyZeroIsoGlobalSections G U).hom :=
      (Category.assoc _ _ _).symm
    _ = (f.hom.app (op (⊤ : Opens X)) ≫
          (normalizedCechCohomologyZeroIsoGlobalSections G U).inv) ≫
        (normalizedCechCohomologyZeroIsoGlobalSections G U).hom := by
      rw [globalSectionsMap_comp_zeroIsoGlobalSections_inv]
    _ = f.hom.app (op (⊤ : Opens X)) ≫
        ((normalizedCechCohomologyZeroIsoGlobalSections G U).inv ≫
          (normalizedCechCohomologyZeroIsoGlobalSections G U).hom) :=
      Category.assoc _ _ _
    _ = f.hom.app (op (⊤ : Opens X)) := by
      rw [Iso.inv_hom_id, Category.comp_id]
    _ = ((normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
          (normalizedCechCohomologyZeroIsoGlobalSections F U).hom) ≫
        f.hom.app (op (⊤ : Opens X)) := by
      rw [Iso.inv_hom_id, Category.id_comp]
    _ = (normalizedCechCohomologyZeroIsoGlobalSections F U).inv ≫
        ((normalizedCechCohomologyZeroIsoGlobalSections F U).hom ≫
          f.hom.app (op (⊤ : Opens X))) :=
      Category.assoc _ _ _

private theorem singletonTop_le (V : SetOpenCover X) : singletonTop ≤ V := by
  refine ⟨{
    index := fun _ => ⟨⊤, ?_⟩
    le := fun _ => le_top }⟩
  simp [singletonTop]

/-- The map from refinement-colimit degree-zero Cech cohomology to global sections induced by
the compatible fixed-cover identifications. -/
noncomputable def cechCohomologyZeroToGlobalSections :
    cechCohomology F.presheaf 0 ⟶ F.presheaf.obj (op (⊤ : Opens X)) :=
  cechCohomologyDesc F.presheaf 0 (F.presheaf.obj (op (⊤ : Opens X)))
    (fun V => (normalizedCechCohomologyZeroIsoGlobalSections F V).hom)
    (fun {_ _} h => normalizedCechCohomologyMap_comp_zeroIsoGlobalSections F _ h)

@[reassoc (attr := simp)]
private theorem toCechCohomology_comp_zeroToGlobalSections (V : SetOpenCover X) :
    toCechCohomology F.presheaf 0 V ≫ cechCohomologyZeroToGlobalSections F =
      (normalizedCechCohomologyZeroIsoGlobalSections F V).hom := by
  apply toCechCohomology_comp_cechCohomologyDesc

/-- Global restriction into degree zero on the singleton cover, followed by the colimit
structure map. -/
private noncomputable def globalSectionsToCechCohomologyZero :
    F.presheaf.obj (op (⊤ : Opens X)) ⟶ cechCohomology F.presheaf 0 :=
  (normalizedCechCohomologyZeroIsoGlobalSections F singletonTop).inv ≫
    toCechCohomology F.presheaf 0 singletonTop

@[reassoc (attr := simp)]
private theorem globalSectionsToCechCohomologyZero_comp_zeroToGlobalSections :
    globalSectionsToCechCohomologyZero F ≫
        cechCohomologyZeroToGlobalSections F =
      𝟙 (F.presheaf.obj (op (⊤ : Opens X))) := by
  simp only [globalSectionsToCechCohomologyZero, Category.assoc,
    toCechCohomology_comp_zeroToGlobalSections, Iso.inv_hom_id]

private theorem cechCohomologyZeroToGlobalSections_comp_globalSectionsTo :
    cechCohomologyZeroToGlobalSections F ≫
        globalSectionsToCechCohomologyZero F =
      𝟙 (cechCohomology F.presheaf 0) := by
  apply cechCohomology_hom_ext F.presheaf 0
  intro V
  let h : singletonTop ≤ V := singletonTop_le V
  have hto :
      toCechCohomology F.presheaf 0 singletonTop =
        normalizedCechCohomologyMap F.presheaf h 0 ≫
          toCechCohomology F.presheaf 0 V :=
    (normalizedCechCohomologyMap_comp_toCechCohomology F.presheaf 0 h).symm
  have hinv :
      (normalizedCechCohomologyZeroIsoGlobalSections F singletonTop).inv ≫
          normalizedCechCohomologyMap F.presheaf h 0 =
        (normalizedCechCohomologyZeroIsoGlobalSections F V).inv :=
    normalizedCechCohomologyZeroIsoGlobalSections_inv_comp_refinement F singletonTop h
  simp only [Category.comp_id]
  rw [← Category.assoc, toCechCohomology_comp_zeroToGlobalSections]
  dsimp only [globalSectionsToCechCohomologyZero]
  rw [hto, ← Category.assoc
    (normalizedCechCohomologyZeroIsoGlobalSections F singletonTop).inv,
    hinv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The canonical map from refinement-colimit degree-zero Cech cohomology to global sections is
an isomorphism. -/
theorem cechCohomologyZeroToGlobalSections_isIso :
    IsIso (cechCohomologyZeroToGlobalSections F) where
  out := ⟨globalSectionsToCechCohomologyZero F,
    cechCohomologyZeroToGlobalSections_comp_globalSectionsTo F,
    globalSectionsToCechCohomologyZero_comp_zeroToGlobalSections F⟩

/-- Refinement-colimit degree-zero Cech cohomology is canonically isomorphic to global
sections. This is equation (C8), valid without separation or paracompactness hypotheses. -/
noncomputable def cechCohomologyZeroIsoGlobalSections :
    cechCohomology F.presheaf 0 ≅ F.presheaf.obj (op (⊤ : Opens X)) := by
  let _ : IsIso (cechCohomologyZeroToGlobalSections F) :=
    cechCohomologyZeroToGlobalSections_isIso F
  exact asIso (cechCohomologyZeroToGlobalSections F)

@[simp]
private theorem cechCohomologyZeroIsoGlobalSections_hom :
    (cechCohomologyZeroIsoGlobalSections F).hom =
      cechCohomologyZeroToGlobalSections F :=
  rfl

/-- The colimit structure map followed by the degree-zero identification is the corresponding
fixed-cover identification. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_comp_zeroIsoGlobalSections (V : SetOpenCover X) :
    toCechCohomology F.presheaf 0 V ≫
        (cechCohomologyZeroIsoGlobalSections F).hom =
      (normalizedCechCohomologyZeroIsoGlobalSections F V).hom := by
  change toCechCohomology F.presheaf 0 V ≫
      cechCohomologyZeroToGlobalSections F =
    (normalizedCechCohomologyZeroIsoGlobalSections F V).hom
  exact toCechCohomology_comp_zeroToGlobalSections F V

/-- The refinement-colimit degree-zero identification is natural in the abelian-sheaf
coefficient. -/
@[reassoc (attr := simp)]
theorem cechCohomologyCoefficientMap_comp_zeroIsoGlobalSections
    {G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (f : F ⟶ G) :
    cechCohomologyCoefficientMap f.hom 0 ≫
        (cechCohomologyZeroIsoGlobalSections G).hom =
      (cechCohomologyZeroIsoGlobalSections F).hom ≫
        f.hom.app (op (⊤ : Opens X)) := by
  apply cechCohomology_hom_ext F.presheaf 0
  intro V
  simp

end TopologicalSpace.OpenCover.SetOpenCover
