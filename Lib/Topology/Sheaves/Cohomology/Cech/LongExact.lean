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

/-! ## Exactness at the middle term -/

/-- A middle-sheaf cocycle in the componentwise kernel factors uniquely through a left-sheaf
cocycle. -/
theorem existsUnique_leftCocycle_of_middleKernel
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (b : CechCocycle S.X₂.presheaf U q)
    (hb : OrderedCech.coefficientMapDegree S.g.hom U.family q b.1 = 0) :
    ∃! a : CechCocycle S.X₁.presheaf U q,
      OrderedCech.coefficientMapDegree S.f.hom U.family q a.1 = b.1 := by
  obtain ⟨a, ha⟩ := ((cochainShortComplex S U q).ab_exact_iff.1
    (cochainShortComplex_exact hS U q) b.1 hb)
  change OrderedCech.coefficientMapDegree S.f.hom U.family q a = b.1 at ha
  have hac : OrderedCech.differential S.X₁.presheaf U.family q a = 0 := by
    apply cochain_f_injective hS U (q + 1)
    rw [map_zero]
    calc
      OrderedCech.coefficientMapDegree S.f.hom U.family (q + 1)
          (OrderedCech.differential S.X₁.presheaf U.family q a) =
        OrderedCech.differential S.X₂.presheaf U.family q
          (OrderedCech.coefficientMapDegree S.f.hom U.family q a) := by
            simpa only [ConcreteCategory.comp_apply] using
              (ConcreteCategory.congr_hom
                (OrderedCech.coefficientMapDegree_comp_differential
                  S.f.hom U.family q) a).symm
      _ = OrderedCech.differential S.X₂.presheaf U.family q b.1 := by rw [ha]
      _ = 0 := b.2
  refine ⟨⟨a, hac⟩, ha, ?_⟩
  intro a' ha'
  apply Subtype.ext
  apply cochain_f_injective hS U q
  exact ha'.trans ha.symm

/-- The positive-degree correction obtained by refining a middle cocycle and subtracting the
differential of a lifted primitive. -/
def middleKernelCorrection
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V W : SetOpenCover X}
    (r : Refinement V.family U.family)
    (s : Refinement W.family V.family) (q : ℕ)
    (c : CechCocycle S.X₂.presheaf U (q + 1))
    (t : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf W.family q) :
    CechCocycle S.X₂.presheaf W (q + 1) :=
  ⟨OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 -
      OrderedCech.differential S.X₂.presheaf W.family q t, by
    change OrderedCech.differential S.X₂.presheaf W.family (q + 1)
      (OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 -
        OrderedCech.differential S.X₂.presheaf W.family q t) = 0
    rw [map_sub]
    have hrefine := ConcreteCategory.congr_hom
      (OrderedCech.refinementMapDegree_comp_differential
        S.X₂.presheaf (r.comp s) (q + 1)) c.1
    have hdd := ConcreteCategory.congr_hom
      (OrderedCech.differential_comp_differential S.X₂.presheaf W.family q) t
    simp only [ConcreteCategory.comp_apply] at hrefine hdd
    rw [hrefine, c.2, map_zero, hdd]
    exact sub_self 0⟩

/-- The underlying cochain of `middleKernelCorrection` is exactly the reviewed subtraction
`(r ∘ s)*c - dt`. -/
theorem middleKernelCorrection_coe
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V W : SetOpenCover X}
    (r : Refinement V.family U.family)
    (s : Refinement W.family V.family) (q : ℕ)
    (c : CechCocycle S.X₂.presheaf U (q + 1))
    (t : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf W.family q) :
    (middleKernelCorrection r s q c t).1 =
      OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 -
        OrderedCech.differential S.X₂.presheaf W.family q t :=
  rfl

/-- Under the reviewed equations `v(r*c) = dz` and `v(t) = s*z`, the corrected middle cocycle
lies in the componentwise kernel of the right coefficient map. -/
theorem middleKernelCorrection_map_eq_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V W : SetOpenCover X}
    (r : Refinement V.family U.family)
    (s : Refinement W.family V.family) (q : ℕ)
    (c : CechCocycle S.X₂.presheaf U (q + 1))
    (z : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₃.presheaf V.family q)
    (t : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf W.family q)
    (hz : OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1)
        (refineCocycle S.X₂.presheaf r (q + 1) c).1 =
      OrderedCech.differential S.X₃.presheaf V.family q z)
    (ht : OrderedCech.coefficientMapDegree S.g.hom W.family q t =
      OrderedCech.refinementMapDegree S.X₃.presheaf s q z) :
    OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
      (middleKernelCorrection r s q c t).1 = 0 := by
  have hcomp :
      OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 =
        OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
          (refineCocycle S.X₂.presheaf r (q + 1) c).1 := by
    change OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 =
      OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
        (OrderedCech.refinementMapDegree S.X₂.presheaf r (q + 1) c.1)
    have h := congrArg (fun k => k.f (q + 1))
      (OrderedCech.refinementMap_comp S.X₂.presheaf r s)
    simpa only [OrderedCech.refinementMap_f, HomologicalComplex.comp_f,
      ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h c.1
  have hcoefficient :
      OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
          (OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
            (refineCocycle S.X₂.presheaf r (q + 1) c).1) =
        OrderedCech.refinementMapDegree S.X₃.presheaf s (q + 1)
          (OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1)
            (refineCocycle S.X₂.presheaf r (q + 1) c).1) := by
    have h := congrArg (fun k => k.f (q + 1))
      (OrderedCech.coefficientMap_comp_refinementMap S.g.hom s)
    simpa only [OrderedCech.coefficientMap_f, OrderedCech.refinementMap_f,
      HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom h
          (refineCocycle S.X₂.presheaf r (q + 1) c).1).symm
  have hcoefficientDifferential :
      OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf W.family q t) =
        OrderedCech.differential S.X₃.presheaf W.family q
          (OrderedCech.coefficientMapDegree S.g.hom W.family q t) := by
    simpa only [ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom
        (OrderedCech.coefficientMapDegree_comp_differential
          S.g.hom W.family q) t).symm
  have hrefinementDifferential :
      OrderedCech.refinementMapDegree S.X₃.presheaf s (q + 1)
          (OrderedCech.differential S.X₃.presheaf V.family q z) =
        OrderedCech.differential S.X₃.presheaf W.family q
          (OrderedCech.refinementMapDegree S.X₃.presheaf s q z) := by
    simpa only [ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom
        (OrderedCech.refinementMapDegree_comp_differential
          S.X₃.presheaf s q) z).symm
  calc
    OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
        (middleKernelCorrection r s q c t).1 =
      OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
          (OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1) -
        OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf W.family q t) := by
            rw [middleKernelCorrection_coe, map_sub]
    _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (q + 1)
          (OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1)
            (refineCocycle S.X₂.presheaf r (q + 1) c).1) -
        OrderedCech.differential S.X₃.presheaf W.family q
          (OrderedCech.coefficientMapDegree S.g.hom W.family q t) := by
            rw [hcomp, hcoefficient, hcoefficientDifferential]
    _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (q + 1)
          (OrderedCech.differential S.X₃.presheaf V.family q z) -
        OrderedCech.differential S.X₃.presheaf W.family q
          (OrderedCech.refinementMapDegree S.X₃.presheaf s q z) := by
            rw [hz, ht]
    _ = 0 := by rw [hrefinementDifferential, sub_self]

/-- The left cocycle factoring the correction represents the original middle cohomology class. -/
theorem middleKernelCorrection_class
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V W : SetOpenCover X}
    (r : Refinement V.family U.family)
    (s : Refinement W.family V.family) (q : ℕ)
    (c : CechCocycle S.X₂.presheaf U (q + 1))
    (t : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf W.family q)
    (a : CechCocycle S.X₁.presheaf W (q + 1))
    (ha : OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1) a.1 =
      (middleKernelCorrection r s q c t).1) :
    cechCohomologyCoefficientMap S.f.hom (q + 1)
        (toCechCohomology S.X₁.presheaf (q + 1) W
          (cocycleClass S.X₁.presheaf W (q + 1) a)) =
      toCechCohomology S.X₂.presheaf (q + 1) U
        (cocycleClass S.X₂.presheaf U (q + 1) c) := by
  have hcoefficient : coefficientCocycle S.f.hom W (q + 1) a =
      middleKernelCorrection r s q c t := by
    apply Subtype.ext
    exact ha
  have hsub :
      (middleKernelCorrection r s q c t).1 -
          (refineCocycle S.X₂.presheaf (r.comp s) (q + 1) c).1 =
        OrderedCech.differential S.X₂.presheaf W.family q (-t) := by
    change (OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 -
        OrderedCech.differential S.X₂.presheaf W.family q t) -
      OrderedCech.refinementMapDegree S.X₂.presheaf (r.comp s) (q + 1) c.1 =
        OrderedCech.differential S.X₂.presheaf W.family q (-t)
    rw [map_neg]
    abel
  have hclass := cocycleClass_eq_of_sub_eq_differential S.X₂.presheaf W q
    (middleKernelCorrection r s q c t)
    (refineCocycle S.X₂.presheaf (r.comp s) (q + 1) c) (-t) hsub
  let h : U ≤ W := ⟨r.comp s⟩
  calc
    cechCohomologyCoefficientMap S.f.hom (q + 1)
        (toCechCohomology S.X₁.presheaf (q + 1) W
          (cocycleClass S.X₁.presheaf W (q + 1) a)) =
      toCechCohomology S.X₂.presheaf (q + 1) W
        (cocycleClass S.X₂.presheaf W (q + 1)
          (coefficientCocycle S.f.hom W (q + 1) a)) :=
            cechCohomologyCoefficientMap_cocycleClass S.f.hom W (q + 1) a
    _ = toCechCohomology S.X₂.presheaf (q + 1) W
        (cocycleClass S.X₂.presheaf W (q + 1)
          (middleKernelCorrection r s q c t)) := by rw [hcoefficient]
    _ = toCechCohomology S.X₂.presheaf (q + 1) W
        (cocycleClass S.X₂.presheaf W (q + 1)
          (refineCocycle S.X₂.presheaf (r.comp s) (q + 1) c)) := by rw [hclass]
    _ = toCechCohomology S.X₂.presheaf (q + 1) U
        (cocycleClass S.X₂.presheaf U (q + 1) c) := by
          rw [← normalizedCechCohomologyMap_cocycleClass
            S.X₂.presheaf h (r.comp s) (q + 1) c]
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom
              (normalizedCechCohomologyMap_comp_toCechCohomology
                S.X₂.presheaf (q + 1) h)
              (cocycleClass S.X₂.presheaf U (q + 1) c)

/-- A positive-degree middle class killed by the right coefficient map has a left-class
preimage, constructed by the reviewed refine--lift--subtract--factor calculation. -/
theorem exists_left_preimage_succ
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₂.presheaf U (q + 1))
    (hc : cechCohomologyCoefficientMap S.g.hom (q + 1)
      (toCechCohomology S.X₂.presheaf (q + 1) U
        (cocycleClass S.X₂.presheaf U (q + 1) c)) = 0) :
    ∃ (W : SetOpenCover X) (a : CechCocycle S.X₁.presheaf W (q + 1)),
      cechCohomologyCoefficientMap S.f.hom (q + 1)
          (toCechCohomology S.X₁.presheaf (q + 1) W
            (cocycleClass S.X₁.presheaf W (q + 1) a)) =
        toCechCohomology S.X₂.presheaf (q + 1) U
          (cocycleClass S.X₂.presheaf U (q + 1) c) := by
  obtain ⟨V, r, z, hz⟩ :=
    exists_refinement_coefficientCocycle_eq_differential S.g.hom U q c hc
  let _ : Epi S.g := hS.epi_g
  obtain ⟨W, s, t, ht⟩ := exists_refinement_cochain_lift S.g V q z
  let d := middleKernelCorrection r s q c t
  have hd : OrderedCech.coefficientMapDegree S.g.hom W.family (q + 1) d.1 = 0 :=
    middleKernelCorrection_map_eq_zero r s q c z t hz ht
  obtain ⟨a, ha, _⟩ := existsUnique_leftCocycle_of_middleKernel hS W (q + 1) d hd
  exact ⟨W, a, middleKernelCorrection_class r s q c t a ha⟩

/-- At degree zero, a killed middle class becomes a literal kernel element after refinement and
therefore factors through the left cocycle, without a negative-degree primitive. -/
theorem exists_left_preimage_degree_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : SetOpenCover X)
    (c : CechCocycle S.X₂.presheaf U 0)
    (hc : cechCohomologyCoefficientMap S.g.hom 0
      (toCechCohomology S.X₂.presheaf 0 U
        (cocycleClass S.X₂.presheaf U 0 c)) = 0) :
    ∃ (V : SetOpenCover X) (a : CechCocycle S.X₁.presheaf V 0),
      cechCohomologyCoefficientMap S.f.hom 0
          (toCechCohomology S.X₁.presheaf 0 V
            (cocycleClass S.X₁.presheaf V 0 a)) =
        toCechCohomology S.X₂.presheaf 0 U
          (cocycleClass S.X₂.presheaf U 0 c) := by
  obtain ⟨V, r, hr⟩ :=
    exists_refinement_coefficientCocycle_eq_zero_degree_zero S.g.hom U c hc
  let b := refineCocycle S.X₂.presheaf r 0 c
  obtain ⟨a, ha, _⟩ := existsUnique_leftCocycle_of_middleKernel hS V 0 b hr
  have hcoefficient : coefficientCocycle S.f.hom V 0 a = b := by
    apply Subtype.ext
    exact ha
  let h : U ≤ V := ⟨r⟩
  refine ⟨V, a, ?_⟩
  calc
    cechCohomologyCoefficientMap S.f.hom 0
        (toCechCohomology S.X₁.presheaf 0 V
          (cocycleClass S.X₁.presheaf V 0 a)) =
      toCechCohomology S.X₂.presheaf 0 V
        (cocycleClass S.X₂.presheaf V 0 (coefficientCocycle S.f.hom V 0 a)) :=
          cechCohomologyCoefficientMap_cocycleClass S.f.hom V 0 a
    _ = toCechCohomology S.X₂.presheaf 0 V
        (cocycleClass S.X₂.presheaf V 0 b) := by rw [hcoefficient]
    _ = toCechCohomology S.X₂.presheaf 0 U
        (cocycleClass S.X₂.presheaf U 0 c) := by
          rw [← normalizedCechCohomologyMap_cocycleClass
            S.X₂.presheaf h r 0 c]
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom
              (normalizedCechCohomologyMap_comp_toCechCohomology
                S.X₂.presheaf 0 h)
              (cocycleClass S.X₂.presheaf U 0 c)

/-- The two ordinary coefficient maps in each degree compose to zero on refinement-directed
Cech cohomology. -/
theorem coefficientMaps_comp_zero
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (q : ℕ) :
    cechCohomologyCoefficientMap S.f.hom q ≫
      cechCohomologyCoefficientMap S.g.hom q = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change cechCohomologyCoefficientMap S.g.hom q
      (cechCohomologyCoefficientMap S.f.hom q x) = 0
  obtain ⟨U, c, hc⟩ := cechCohomology_exists_cocycle_rep S.X₁.presheaf q x
  rw [← hc, cechCohomologyCoefficientMap_cocycleClass,
    cechCohomologyCoefficientMap_cocycleClass]
  have hsheaf : S.f.hom ≫ S.g.hom = 0 :=
    congrArg (fun k : S.X₁ ⟶ S.X₃ => k.hom) S.zero
  have hmaps := congrArg (fun k => k.f q)
    (OrderedCech.coefficientMap_comp S.f.hom S.g.hom U.family)
  have hzero :
      OrderedCech.coefficientMapDegree S.g.hom U.family q
          (OrderedCech.coefficientMapDegree S.f.hom U.family q c.1) = 0 := by
    calc
      OrderedCech.coefficientMapDegree S.g.hom U.family q
          (OrderedCech.coefficientMapDegree S.f.hom U.family q c.1) =
        (OrderedCech.coefficientMap S.f.hom U.family ≫
          OrderedCech.coefficientMap S.g.hom U.family).f q c.1 := by
            rw [HomologicalComplex.comp_f, OrderedCech.coefficientMap_f,
              OrderedCech.coefficientMap_f, ConcreteCategory.comp_apply]
      _ = (OrderedCech.coefficientMap (S.f.hom ≫ S.g.hom) U.family).f q c.1 := by
            exact (ConcreteCategory.congr_hom hmaps c.1).symm
      _ = (OrderedCech.coefficientMap (0 : S.X₁.presheaf ⟶ S.X₃.presheaf)
          U.family).f q c.1 := by rw [hsheaf]
      _ = 0 := by
        change OrderedCech.coefficientMapDegree
          (0 : S.X₁.presheaf ⟶ S.X₃.presheaf) U.family q c.1 = 0
        apply (Limits.Concrete.productEquiv
          (fun σ : OrderedSimplex U.Index q =>
            S.X₃.presheaf.obj (op (σ.intersection U.family)))).injective
        funext σ
        simp only [Limits.Concrete.productEquiv_apply_apply]
        calc
          OrderedCech.π S.X₃.presheaf U.family q σ
              (OrderedCech.coefficientMapDegree
                (0 : S.X₁.presheaf ⟶ S.X₃.presheaf) U.family q c.1) =
            ConcreteCategory.hom
              ((0 : S.X₁.presheaf ⟶ S.X₃.presheaf).app
                (op (σ.intersection U.family)))
                (OrderedCech.π S.X₁.presheaf U.family q σ c.1) := by
                  simpa only [ConcreteCategory.comp_apply] using
                    ConcreteCategory.congr_hom
                      (OrderedCech.coefficientMapDegree_π
                        (0 : S.X₁.presheaf ⟶ S.X₃.presheaf) U.family q σ) c.1
          _ = 0 := AddMonoidHom.zero_apply _
          _ = OrderedCech.π S.X₃.presheaf U.family q σ 0 :=
            (map_zero _).symm
  have hcocycle : coefficientCocycle S.g.hom U q
      (coefficientCocycle S.f.hom U q c) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hcocycle, map_zero, map_zero]

/-- Exactness of the actual refinement-colimit coefficient maps at every middle term. -/
theorem exactAtMiddle_function
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    Function.Exact (cechCohomologyCoefficientMap S.f.hom q)
      (cechCohomologyCoefficientMap S.g.hom q) := by
  intro x
  constructor
  · intro hx
    obtain ⟨U, c, hc⟩ := cechCohomology_exists_cocycle_rep S.X₂.presheaf q x
    cases q with
    | zero =>
        have hkernel : cechCohomologyCoefficientMap S.g.hom 0
            (toCechCohomology S.X₂.presheaf 0 U
              (cocycleClass S.X₂.presheaf U 0 c)) = 0 := by
          rw [hc]
          exact hx
        obtain ⟨V, a, ha⟩ := exists_left_preimage_degree_zero hS U c hkernel
        exact ⟨toCechCohomology S.X₁.presheaf 0 V
          (cocycleClass S.X₁.presheaf V 0 a), ha.trans hc⟩
    | succ n =>
        have hkernel : cechCohomologyCoefficientMap S.g.hom (n + 1)
            (toCechCohomology S.X₂.presheaf (n + 1) U
              (cocycleClass S.X₂.presheaf U (n + 1) c)) = 0 := by
          rw [hc]
          exact hx
        obtain ⟨V, a, ha⟩ := exists_left_preimage_succ hS U n c hkernel
        exact ⟨toCechCohomology S.X₁.presheaf (n + 1) V
          (cocycleClass S.X₁.presheaf V (n + 1) a), ha.trans hc⟩
  · rintro ⟨y, rfl⟩
    calc
      cechCohomologyCoefficientMap S.g.hom q
          (cechCohomologyCoefficientMap S.f.hom q y) =
        (0 : cechCohomology S.X₁.presheaf q ⟶
          cechCohomology S.X₃.presheaf q) y := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom (coefficientMaps_comp_zero S q) y
      _ = 0 := AddMonoidHom.zero_apply _

/-- The categorical short complex of consecutive coefficient maps in degree `q`. -/
noncomputable def coefficientCechShortComplex
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (q : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (cechCohomologyCoefficientMap S.f.hom q)
    (cechCohomologyCoefficientMap S.g.hom q)
    (coefficientMaps_comp_zero S q)

/-- Categorical exactness of the two consecutive coefficient maps in every degree. -/
theorem coefficientCechShortComplex_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    (coefficientCechShortComplex S q).Exact := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact exactAtMiddle_function hS q

/-! ## Exactness at the right term -/

/-- A middle-valued cocycle itself supplies a boundary presentation for its coefficient image:
the lift is the original cocycle and its descended differential is zero. -/
def boundaryPresentationOfMiddleCocycle
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (U : SetOpenCover X) (q : ℕ)
    (b : CechCocycle S.X₂.presheaf U q) :
    BoundaryPresentation S U q (coefficientCocycle S.g.hom U q b) where
  cover := U
  refinement := Refinement.refl U.family
  lift := b.1
  descended := 0
  lift_eq := by
    have hrefinement := congrArg (fun k => k.f q)
      (OrderedCech.refinementMap_refl S.X₃.presheaf U.family)
    exact (ConcreteCategory.congr_hom hrefinement
      (OrderedCech.coefficientMapDegree S.g.hom U.family q b.1)).symm
  descended_eq := by
    rw [map_zero, b.2]

/-- The boundary presentation furnished by a middle cocycle has zero descended Cech class. -/
theorem boundaryPresentationOfMiddleCocycle_cechClass_eq_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (b : CechCocycle S.X₂.presheaf U q) :
    (boundaryPresentationOfMiddleCocycle (S := S) U q b).cechClass hS = 0 := by
  let P := boundaryPresentationOfMiddleCocycle (S := S) U q b
  change P.cechClass hS = 0
  have hzero : P.descendedCocycle hS = 0 := by
    apply Subtype.ext
    rfl
  have hclass : cocycleClass S.X₁.presheaf P.cover (q + 1)
      (P.descendedCocycle hS) = 0 := by
    calc
      cocycleClass S.X₁.presheaf P.cover (q + 1) (P.descendedCocycle hS) =
          cocycleClass S.X₁.presheaf P.cover (q + 1)
            (0 : CechCocycle S.X₁.presheaf P.cover (q + 1)) :=
        congrArg (cocycleClass S.X₁.presheaf P.cover (q + 1)) hzero
      _ = 0 := map_zero _
  calc
    P.cechClass hS =
        toCechCohomology S.X₁.presheaf (q + 1) P.cover
          (cocycleClass S.X₁.presheaf P.cover (q + 1)
            (P.descendedCocycle hS)) := rfl
    _ = toCechCohomology S.X₁.presheaf (q + 1) P.cover 0 := by rw [hclass]
    _ = 0 := map_zero _

/-- The right coefficient map followed by the connecting homomorphism is zero. -/
theorem coefficientMap_comp_connectingHom
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    cechCohomologyCoefficientMap S.g.hom q ≫ connectingHom hS q = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change connectingHom hS q (cechCohomologyCoefficientMap S.g.hom q x) = 0
  obtain ⟨U, b, hb⟩ := cechCohomology_exists_cocycle_rep S.X₂.presheaf q x
  rw [← hb, cechCohomologyCoefficientMap_cocycleClass,
    connectingHom_cocycleClass_eq_cechClass]
  exact boundaryPresentationOfMiddleCocycle_cechClass_eq_zero hS U q b

/-- If the descended class of a boundary presentation vanishes, then after refinement its
descended cocycle is literally the differential of a cochain. -/
theorem exists_refinement_descended_eq_differential
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) (hP : P.cechClass hS = 0) :
    ∃ (W : SetOpenCover X) (s : Refinement W.family P.cover.family)
      (e : OrderedCech.object (A := AddCommGrpCat.{u})
        S.X₁.presheaf W.family q),
      OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended =
        OrderedCech.differential S.X₁.presheaf W.family q e := by
  obtain ⟨W, s, e, he⟩ := exists_refinement_cocycle_eq_differential
    S.X₁.presheaf P.cover q (P.descendedCocycle hS) hP
  exact ⟨W, s, e, he⟩

/-- Correct a refined middle lift by subtracting the coefficient image of a primitive for its
descended differential. -/
def correctedLiftCocycle
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family)
    (e : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₁.presheaf W.family q)
    (he : OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended =
      OrderedCech.differential S.X₁.presheaf W.family q e) :
    CechCocycle S.X₂.presheaf W q :=
  ⟨OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift -
      OrderedCech.coefficientMapDegree S.f.hom W.family q e, by
    change OrderedCech.differential S.X₂.presheaf W.family q
      (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift -
        OrderedCech.coefficientMapDegree S.f.hom W.family q e) = 0
    have hrefinement :
        OrderedCech.differential S.X₂.presheaf W.family q
            (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift) =
          OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
            (OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          (OrderedCech.refinementMapDegree_comp_differential
            S.X₂.presheaf s q) P.lift
    have hcoefficient :
        OrderedCech.differential S.X₂.presheaf W.family q
            (OrderedCech.coefficientMapDegree S.f.hom W.family q e) =
          OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1)
            (OrderedCech.differential S.X₁.presheaf W.family q e) := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          (OrderedCech.coefficientMapDegree_comp_differential
            S.f.hom W.family q) e
    have hcoefficientRefinement :
        OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1)
            (OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended) =
          OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
            (OrderedCech.coefficientMapDegree S.f.hom P.cover.family
              (q + 1) P.descended) := by
      have h := congrArg (fun k => k.f (q + 1))
        (OrderedCech.coefficientMap_comp_refinementMap S.f.hom s)
      simpa only [OrderedCech.coefficientMap_f, OrderedCech.refinementMap_f,
        HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
          (ConcreteCategory.congr_hom h P.descended).symm
    rw [map_sub, hrefinement, hcoefficient, ← he, hcoefficientRefinement,
      P.descended_eq, sub_self]⟩

/-- The underlying cochain of the corrected lift is the reviewed subtraction
`s*l - f(e)`. -/
theorem correctedLiftCocycle_coe
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family)
    (e : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₁.presheaf W.family q)
    (he : OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended =
      OrderedCech.differential S.X₁.presheaf W.family q e) :
    (correctedLiftCocycle P W s e he).1 =
      OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift -
        OrderedCech.coefficientMapDegree S.f.hom W.family q e :=
  rfl

/-- Correcting a boundary-presentation lift does not change its image in the right sheaf. -/
theorem correctedLiftCocycle_map
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family)
    (e : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₁.presheaf W.family q)
    (he : OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended =
      OrderedCech.differential S.X₁.presheaf W.family q e) :
    coefficientCocycle S.g.hom W q
        (correctedLiftCocycle P W s e he) =
      refineCocycle S.X₃.presheaf (P.refinement.comp s) q c := by
  apply Subtype.ext
  have hcoefficientRefinement :
      OrderedCech.coefficientMapDegree S.g.hom W.family q
          (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift) =
        OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.coefficientMapDegree S.g.hom P.cover.family q P.lift) := by
    have h := congrArg (fun k => k.f q)
      (OrderedCech.coefficientMap_comp_refinementMap S.g.hom s)
    simpa only [OrderedCech.coefficientMap_f, OrderedCech.refinementMap_f,
      HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom h P.lift).symm
  have hzero :
      OrderedCech.coefficientMapDegree S.g.hom W.family q
          (OrderedCech.coefficientMapDegree S.f.hom W.family q e) = 0 := by
    change ((cochainShortComplex S W q).f ≫ (cochainShortComplex S W q).g) e = 0
    rw [(cochainShortComplex S W q).zero]
    rfl
  have hcomposition :
      OrderedCech.refinementMapDegree S.X₃.presheaf (P.refinement.comp s) q c.1 =
        OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.refinementMapDegree S.X₃.presheaf P.refinement q c.1) := by
    have h := congrArg (fun k => k.f q)
      (OrderedCech.refinementMap_comp S.X₃.presheaf P.refinement s)
    simpa only [OrderedCech.refinementMap_f, HomologicalComplex.comp_f,
      ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h c.1
  change OrderedCech.coefficientMapDegree S.g.hom W.family q
      (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift -
        OrderedCech.coefficientMapDegree S.f.hom W.family q e) =
    OrderedCech.refinementMapDegree S.X₃.presheaf (P.refinement.comp s) q c.1
  rw [map_sub, hcoefficientRefinement, hzero, sub_zero, P.lift_eq]
  exact hcomposition.symm

/-- A boundary presentation with zero descended class yields a middle-class preimage of its
original right-valued cocycle class. -/
theorem exists_middle_preimage_of_boundaryPresentation_eq_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) (hP : P.cechClass hS = 0) :
    ∃ (W : SetOpenCover X) (b : CechCocycle S.X₂.presheaf W q),
      cechCohomologyCoefficientMap S.g.hom q
          (toCechCohomology S.X₂.presheaf q W
            (cocycleClass S.X₂.presheaf W q b)) =
        toCechCohomology S.X₃.presheaf q U
          (cocycleClass S.X₃.presheaf U q c) := by
  obtain ⟨W, s, e, he⟩ := exists_refinement_descended_eq_differential hS P hP
  let b := correctedLiftCocycle P W s e he
  have hb : coefficientCocycle S.g.hom W q b =
      refineCocycle S.X₃.presheaf (P.refinement.comp s) q c :=
    correctedLiftCocycle_map P W s e he
  let h : U ≤ W := ⟨P.refinement.comp s⟩
  refine ⟨W, b, ?_⟩
  calc
    cechCohomologyCoefficientMap S.g.hom q
        (toCechCohomology S.X₂.presheaf q W
          (cocycleClass S.X₂.presheaf W q b)) =
      toCechCohomology S.X₃.presheaf q W
        (cocycleClass S.X₃.presheaf W q
          (coefficientCocycle S.g.hom W q b)) :=
            cechCohomologyCoefficientMap_cocycleClass S.g.hom W q b
    _ = toCechCohomology S.X₃.presheaf q W
        (cocycleClass S.X₃.presheaf W q
          (refineCocycle S.X₃.presheaf (P.refinement.comp s) q c)) := by rw [hb]
    _ = toCechCohomology S.X₃.presheaf q U
        (cocycleClass S.X₃.presheaf U q c) := by
          rw [← normalizedCechCohomologyMap_cocycleClass
            S.X₃.presheaf h (P.refinement.comp s) q c]
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom
              (normalizedCechCohomologyMap_comp_toCechCohomology
                S.X₃.presheaf q h)
              (cocycleClass S.X₃.presheaf U q c)

/-- Degree-zero specialization of the corrected-lift preimage construction. -/
theorem exists_middle_preimage_of_boundaryPresentation_eq_zero_degree_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) {U : SetOpenCover X}
    {c : CechCocycle S.X₃.presheaf U 0}
    (P : BoundaryPresentation S U 0 c) (hP : P.cechClass hS = 0) :
    ∃ (W : SetOpenCover X) (b : CechCocycle S.X₂.presheaf W 0),
      cechCohomologyCoefficientMap S.g.hom 0
          (toCechCohomology S.X₂.presheaf 0 W
            (cocycleClass S.X₂.presheaf W 0 b)) =
        toCechCohomology S.X₃.presheaf 0 U
          (cocycleClass S.X₃.presheaf U 0 c) :=
  exists_middle_preimage_of_boundaryPresentation_eq_zero hS P hP

/-- Exactness of the coefficient map and connecting homomorphism at every right term. -/
theorem exactAtRight_function
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    Function.Exact (cechCohomologyCoefficientMap S.g.hom q)
      (connectingHom hS q) := by
  intro x
  constructor
  · intro hx
    obtain ⟨U, c, P, hrep, hconnecting⟩ :=
      connectingHom_exists_boundaryPresentation hS q x
    have hP : P.cechClass hS = 0 := hconnecting.symm.trans hx
    obtain ⟨W, b, hb⟩ :=
      exists_middle_preimage_of_boundaryPresentation_eq_zero hS P hP
    exact ⟨toCechCohomology S.X₂.presheaf q W
      (cocycleClass S.X₂.presheaf W q b), hb.trans hrep⟩
  · rintro ⟨y, rfl⟩
    calc
      connectingHom hS q (cechCohomologyCoefficientMap S.g.hom q y) =
        (0 : cechCohomology S.X₂.presheaf q ⟶
          cechCohomology S.X₁.presheaf (q + 1)) y := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom (coefficientMap_comp_connectingHom hS q) y
      _ = 0 := AddMonoidHom.zero_apply _

/-- The categorical short complex consisting of a right coefficient map and the following
connecting homomorphism. -/
noncomputable def coefficientConnectingCechShortComplex
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (cechCohomologyCoefficientMap S.g.hom q)
    (connectingHom hS q) (coefficientMap_comp_connectingHom hS q)

/-- Categorical exactness of the right coefficient map and the connecting homomorphism. -/
theorem coefficientConnectingCechShortComplex_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    (coefficientConnectingCechShortComplex hS q).Exact := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact exactAtRight_function hS q

end TopologicalSpace.OpenCover.SetOpenCover
