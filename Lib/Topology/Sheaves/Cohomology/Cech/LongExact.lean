/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.ConnectingHom
public import Lib.Topology.Sheaves.Cohomology.Cech.DegreeZero
public import Mathlib.Algebra.Homology.ExactSequence

/-!
# The long exact sequence in refinement-directed Cech cohomology

This file translates reviewed textbook section CD-05I, equation (C24). It proves exactness of
the refinement-directed Cech sequence attached to a short exact sequence of abelian sheaves by
the representative calculations in the textbook proof, including its separate degree-zero
branches, and packages the resulting consecutive exact pairs and finite six-object windows.

Naturality of the connecting morphism and the cohomological-delta-functor structure belong to
CD-05J and are deliberately not asserted here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}

/-! ## Initial injection -/

/-- The degree-zero Cech coefficient map induced by the left map of a short exact sequence is
injective. This is the initial injection in equation (C24), transported through the canonical
degree-zero identification with global sections. -/
theorem initialCoefficientMap_injective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) :
    Function.Injective (cechCohomologyCoefficientMap S.f.hom 0) := by
  let _ : Mono S.f.hom :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology X) AddCommGrpCat S.f).mp hS.mono_f
  have hf : Function.Injective (S.f.hom.app (op (⊤ : Opens X))) :=
    (AddCommGrpCat.mono_iff_injective _).1 (by infer_instance)
  have hzero :
      cechCohomologyCoefficientMap S.f.hom 0 ≫
          (cechCohomologyZeroIsoGlobalSections S.X₂).hom =
        (cechCohomologyZeroIsoGlobalSections S.X₁).hom ≫
          S.f.hom.app (op (⊤ : Opens X)) :=
    cechCohomologyCoefficientMap_comp_zeroIsoGlobalSections S.X₁ S.f
  intro x y hxy
  apply (AddCommGrpCat.mono_iff_injective
    (cechCohomologyZeroIsoGlobalSections S.X₁).hom).1 (by infer_instance)
  apply hf
  calc
    S.f.hom.app (op (⊤ : Opens X))
        ((cechCohomologyZeroIsoGlobalSections S.X₁).hom x) =
      (cechCohomologyZeroIsoGlobalSections S.X₂).hom
        (cechCohomologyCoefficientMap S.f.hom 0 x) := by
          exact (ConcreteCategory.congr_hom hzero x).symm
    _ = (cechCohomologyZeroIsoGlobalSections S.X₂).hom
        (cechCohomologyCoefficientMap S.f.hom 0 y) := by rw [hxy]
    _ = S.f.hom.app (op (⊤ : Opens X))
        ((cechCohomologyZeroIsoGlobalSections S.X₁).hom y) := by
          exact ConcreteCategory.congr_hom hzero y

/-- The initial categorical pair `0 ⟶ H⁰(A) ⟶ H⁰(B)` in the Cech long sequence. -/
noncomputable def initialCechShortComplex
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (0 : AddCommGrpCat.of PUnit.{u + 1} ⟶ cechCohomology S.X₁.presheaf 0)
    (cechCohomologyCoefficientMap S.f.hom 0) zero_comp

/-- Exactness of the initial categorical pair `0 ⟶ H⁰(A) ⟶ H⁰(B)`. -/
theorem initialCechShortComplex_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) : (initialCechShortComplex S).Exact := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    (0 : AddCommGrpCat.of PUnit.{u + 1} ⟶ cechCohomology S.X₁.presheaf 0)
    (cechCohomologyCoefficientMap S.f.hom 0)
  intro x
  constructor
  · intro hx
    have hx0 : x = 0 := initialCoefficientMap_injective hS (by
      simpa only [map_zero] using hx)
    subst x
    refine ⟨PUnit.unit, ?_⟩
    rfl
  · rintro ⟨z, rfl⟩
    change cechCohomologyCoefficientMap S.f.hom 0 0 = 0
    exact map_zero _

/-! ## Common representative and death witnesses -/

/-- A coefficient morphism sends a concrete normalized Cech cocycle to its componentwise
coefficient image. -/
def coefficientCocycle
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X) (q : ℕ) :
    CechCocycle P U q →+ CechCocycle Q U q where
  toFun c := ⟨OrderedCech.coefficientMapDegree f U.family q c.1, by
    calc
      OrderedCech.differential Q U.family q
          (OrderedCech.coefficientMapDegree f U.family q c.1) =
        OrderedCech.coefficientMapDegree f U.family (q + 1)
          (OrderedCech.differential P U.family q c.1) := by
            simpa only [ConcreteCategory.comp_apply] using
              (ConcreteCategory.congr_hom
                (OrderedCech.coefficientMapDegree_comp_differential f U.family q) c.1)
      _ = 0 := by rw [c.2]; exact map_zero _⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' c c' := by
    apply Subtype.ext
    exact map_add _ _ _

/-- The underlying cochain of `coefficientCocycle` is the landed degreewise coefficient map. -/
theorem coefficientCocycle_apply_coe
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle P U q) :
    (coefficientCocycle f U q c).1 =
      OrderedCech.coefficientMapDegree f U.family q c.1 :=
  rfl

/-- Coefficient images of concrete cocycles commute literally with chosen refinement. -/
theorem coefficientCocycle_refine
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) {U V : SetOpenCover X}
    (r : Refinement V.family U.family) (q : ℕ)
    (c : CechCocycle P U q) :
    coefficientCocycle f V q (refineCocycle P r q c) =
      refineCocycle Q r q (coefficientCocycle f U q c) := by
  apply Subtype.ext
  have h := congrArg (fun k => k.f q)
    (OrderedCech.coefficientMap_comp_refinementMap f r)
  exact (ConcreteCategory.congr_hom h c.1).symm

/-- The fixed-cover coefficient map sends a concrete cocycle class to the class of its literal
coefficient image. -/
theorem normalizedCechCohomologyCoefficientMap_cocycleClass
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle P U q) :
    normalizedCechCohomologyCoefficientMap f U q
        (cocycleClass P U q c) =
      cocycleClass Q U q (coefficientCocycle f U q c) := by
  let K := normalizedCechComplex (A := AddCommGrpCat.{u}) P U
  let L := normalizedCechComplex (A := AddCommGrpCat.{u}) Q U
  let φ : K ⟶ L := normalizedCechComplexMap f U
  let ψ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) q).map φ
  let z := cocycleKernelEquiv P U q c
  let w := cocycleKernelEquiv Q U q (coefficientCocycle f U q c)
  have hcycles : ShortComplex.cyclesMap ψ ((K.sc q).abCyclesIso.inv z) =
      (L.sc q).abCyclesIso.inv w := by
    apply (AddCommGrpCat.mono_iff_injective (L.sc q).iCycles).1 inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, (K.sc q).abCyclesIso_inv_apply_iCycles,
      (L.sc q).abCyclesIso_inv_apply_iCycles]
    rfl
  change ShortComplex.homologyMap ψ
      ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv z)) =
    (L.sc q).homologyπ ((L.sc q).abCyclesIso.inv w)
  rw [← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hcycles]

/-- The refinement-colimit coefficient map has the same concrete-cocycle formula. -/
theorem cechCohomologyCoefficientMap_cocycleClass
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle P U q) :
    cechCohomologyCoefficientMap f q
        (toCechCohomology P q U (cocycleClass P U q c)) =
      toCechCohomology Q q U
        (cocycleClass Q U q (coefficientCocycle f U q c)) := by
  calc
    cechCohomologyCoefficientMap f q
        (toCechCohomology P q U (cocycleClass P U q c)) =
      (toCechCohomology P q U ≫ cechCohomologyCoefficientMap f q)
        (cocycleClass P U q c) := by rw [ConcreteCategory.comp_apply]
    _ = (normalizedCechCohomologyCoefficientMap f U q ≫
          toCechCohomology Q q U) (cocycleClass P U q c) := by
            rw [toCechCohomology_comp_cechCohomologyCoefficientMap]
    _ = toCechCohomology Q q U
        (normalizedCechCohomologyCoefficientMap f U q
          (cocycleClass P U q c)) := by rw [ConcreteCategory.comp_apply]
    _ = toCechCohomology Q q U
        (cocycleClass Q U q (coefficientCocycle f U q c)) := by
          rw [normalizedCechCohomologyCoefficientMap_cocycleClass]

/-- A positive-degree concrete cocycle whose class dies in the refinement colimit becomes the
literal differential of a cochain after refinement. -/
theorem exists_refinement_cocycle_eq_differential
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle F U (q + 1))
    (hc : toCechCohomology F (q + 1) U
      (cocycleClass F U (q + 1) c) = 0) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family)
      (z : OrderedCech.object (A := AddCommGrpCat.{u}) F V.family q),
      (refineCocycle F r (q + 1) c).1 =
        OrderedCech.differential F V.family q z := by
  obtain ⟨V, h, hcV⟩ :=
    (toCechCohomology_apply_eq_zero_iff F (q + 1)
      (cocycleClass F U (q + 1) c)).1 hc
  let r : Refinement V.family U.family := refinementOfLE h
  have hclass : cocycleClass F V (q + 1) (refineCocycle F r (q + 1) c) = 0 := by
    rw [← normalizedCechCohomologyMap_cocycleClass F h r (q + 1) c]
    exact hcV
  obtain ⟨z, hz⟩ :=
    (cocycleClass_eq_zero_iff F V (q + 1)
      (refineCocycle F r (q + 1) c)).1 hclass
  let K := normalizedCechComplex (A := AddCommGrpCat.{u}) F V
  let z' : OrderedCech.object (A := AddCommGrpCat.{u}) F V.family q :=
    (K.XIsoOfEq (CochainComplex.prev_nat_succ q)).hom z
  refine ⟨V, r, z', ?_⟩
  calc
    (refineCocycle F r (q + 1) c).1 =
        K.d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1) z := hz.symm
    _ = K.d q (q + 1) z' := by
      exact (ConcreteCategory.congr_hom
        (K.XIsoOfEq_hom_comp_d (CochainComplex.prev_nat_succ q) (q + 1)) z).symm
    _ = OrderedCech.differential F V.family q z' := by
      simp only [K, normalizedCechComplex, OrderedCech.complex_d]

/-- In degree zero, a concrete cocycle with zero fixed-cover class is literally zero; no
negative-degree primitive is introduced. -/
theorem cocycle_eq_zero_of_cocycleClass_eq_zero_degree_zero
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (c : CechCocycle F U 0)
    (hc : cocycleClass F U 0 c = 0) : c = 0 := by
  obtain ⟨b, hb⟩ := (cocycleClass_eq_zero_iff F U 0 c).1 hc
  have hnot : ¬(ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by
    simp only [CochainComplex.prev_nat_zero, ComplexShape.up_Rel]
    omega
  have hfzero : ((normalizedCechComplex F U).sc 0).f b = 0 := by
    change (normalizedCechComplex F U).d ((ComplexShape.up ℕ).prev 0) 0 b = 0
    rw [(normalizedCechComplex F U).shape _ _ hnot]
    rfl
  apply Subtype.ext
  exact hb.symm.trans hfzero

/-- A degree-zero concrete cocycle whose class dies in the refinement colimit becomes literally
zero after refinement. -/
theorem exists_refinement_cocycle_eq_zero_degree_zero
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (c : CechCocycle F U 0)
    (hc : toCechCohomology F 0 U (cocycleClass F U 0 c) = 0) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family),
      refineCocycle F r 0 c = 0 := by
  obtain ⟨V, h, hcV⟩ :=
    (toCechCohomology_apply_eq_zero_iff F 0 (cocycleClass F U 0 c)).1 hc
  let r : Refinement V.family U.family := refinementOfLE h
  have hclass : cocycleClass F V 0 (refineCocycle F r 0 c) = 0 := by
    rw [← normalizedCechCohomologyMap_cocycleClass F h r 0 c]
    exact hcV
  exact ⟨V, r, cocycle_eq_zero_of_cocycleClass_eq_zero_degree_zero
    F V (refineCocycle F r 0 c) hclass⟩

/-- If a positive-degree coefficient image dies in the colimit, then after refinement that
literal coefficient image is a differential. -/
theorem exists_refinement_coefficientCocycle_eq_differential
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle P U (q + 1))
    (hc : cechCohomologyCoefficientMap f (q + 1)
      (toCechCohomology P (q + 1) U
        (cocycleClass P U (q + 1) c)) = 0) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family)
      (z : OrderedCech.object (A := AddCommGrpCat.{u}) Q V.family q),
      OrderedCech.coefficientMapDegree f V.family (q + 1)
          (refineCocycle P r (q + 1) c).1 =
        OrderedCech.differential Q V.family q z := by
  have hc' : toCechCohomology Q (q + 1) U
      (cocycleClass Q U (q + 1) (coefficientCocycle f U (q + 1) c)) = 0 := by
    rw [← cechCohomologyCoefficientMap_cocycleClass f U (q + 1) c]
    exact hc
  obtain ⟨V, r, z, hz⟩ := exists_refinement_cocycle_eq_differential
    Q U q (coefficientCocycle f U (q + 1) c) hc'
  refine ⟨V, r, z, ?_⟩
  rw [← coefficientCocycle_apply_coe f V (q + 1)
    (refineCocycle P r (q + 1) c), coefficientCocycle_refine]
  exact hz

/-- If a degree-zero coefficient image dies in the colimit, then after refinement that literal
coefficient image is zero. -/
theorem exists_refinement_coefficientCocycle_eq_zero_degree_zero
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (U : SetOpenCover X)
    (c : CechCocycle P U 0)
    (hc : cechCohomologyCoefficientMap f 0
      (toCechCohomology P 0 U (cocycleClass P U 0 c)) = 0) :
    ∃ (V : SetOpenCover X) (r : Refinement V.family U.family),
      OrderedCech.coefficientMapDegree f V.family 0
        (refineCocycle P r 0 c).1 = 0 := by
  have hc' : toCechCohomology Q 0 U
      (cocycleClass Q U 0 (coefficientCocycle f U 0 c)) = 0 := by
    rw [← cechCohomologyCoefficientMap_cocycleClass f U 0 c]
    exact hc
  obtain ⟨V, r, hz⟩ := exists_refinement_cocycle_eq_zero_degree_zero
    Q U (coefficientCocycle f U 0 c) hc'
  refine ⟨V, r, ?_⟩
  rw [← coefficientCocycle_apply_coe f V 0 (refineCocycle P r 0 c),
    coefficientCocycle_refine, hz]
  rfl

end TopologicalSpace.OpenCover.SetOpenCover
