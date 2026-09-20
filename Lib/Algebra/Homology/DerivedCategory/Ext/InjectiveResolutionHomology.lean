/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.ShortComplex.AbCycleClass
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Positive homology of an evaluated injective resolution

For an injective resolution `R` of `F`, this file identifies the strictly positive homology of
the literal complex `Hom(A, R•)` with Mathlib's native `Ext A F`.  The comparison is natural in
the represented object `A`, so it packages as a natural isomorphism on `Cᵒᵖ`.

The proof maps the direct cycles-modulo-boundaries quotient to `Ext` using
`InjectiveResolution.extMk`.  Surjectivity and injectivity are exactly
`InjectiveResolution.extMk_surjective` and `InjectiveResolution.extMk_eq_zero_iff`.
Degree zero, which uses the augmentation kernel, is deliberately separate.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §2.5 (`Ext` as the right
  derived functor of `Hom`, computed from an injective resolution) and §2.7 (its agreement with
  the projective computation).
* [R. Hartshorne, *Algebraic geometry*][hartshorne77], Chapter III, §1.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian CochainComplex.HomComplex

namespace CategoryTheory

universe v u


namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
/-- `homologyIsoSc'` is natural in the homological complex. -/
theorem homologyIsoSc'_hom_naturality {D : Type*} [Category* D] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex D c}
    (φ : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    HomologicalComplex.homologyMap φ j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' D c i j k).map φ) := by
  let H := ShortComplex.homologyFunctor D
  change H.map ((HomologicalComplex.shortComplexFunctor D c j).map φ) ≫
      H.map ((HomologicalComplex.natIsoSc' D c i j k hi hk).hom.app L) =
    H.map ((HomologicalComplex.natIsoSc' D c i j k hi hk).hom.app K) ≫
      H.map ((HomologicalComplex.shortComplexFunctor' D c i j k).map φ)
  simpa only [Functor.map_comp] using congrArg H.map
    ((HomologicalComplex.natIsoSc' D c i j k hi hk).hom.naturality φ)

end HomologicalComplex

namespace InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  {F : C} (R : InjectiveResolution F)

/-- The literal complex `A ↦ Hom(A, R•)`. -/
abbrev evaluatedResolution (A : C) : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj R.cocomplex

/-- Precomposition on the literal evaluated resolution. -/
abbrev evaluatedResolutionMap {A A' : C} (a : A' ⟶ A) :
    evaluatedResolution R A ⟶ evaluatedResolution R A' :=
  (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℕ)).app
    R.cocomplex

omit [HasExt C] in
/-- The explicit underlying group in every degree of the evaluated resolution. -/
def evaluatedResolutionXAddEquiv (A : C) (i : ℕ) :
    (evaluatedResolution R A).X i ≃+ (A ⟶ R.cocomplex.X i) := AddEquiv.refl _

omit [HasExt C] in
/-- Under the explicit description of the terms, the differential of the evaluated resolution is
postcomposition with the differential of the resolution. -/
@[simp] theorem evaluatedResolutionXAddEquiv_d (A : C) (i j : ℕ)
    (x : (evaluatedResolution R A).X i) :
    evaluatedResolutionXAddEquiv R A j ((evaluatedResolution R A).d i j x) =
      evaluatedResolutionXAddEquiv R A i x ≫ R.cocomplex.d i j := rfl

/-- Three explicit consecutive terms around positive degree `n + 1`. -/
abbrev positiveShortComplex (A : C) (n : ℕ) : ShortComplex AddCommGrpCat.{v} :=
  (evaluatedResolution R A).sc' n (n + 1) ((n + 1) + 1)

/-- Precomposition on the three explicit terms in positive degree. -/
abbrev positiveShortComplexMap {A A' : C} (a : A' ⟶ A) (n : ℕ) :
    positiveShortComplex R A n ⟶ positiveShortComplex R A' n :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
    n (n + 1) ((n + 1) + 1)).map (evaluatedResolutionMap R a)

omit [HasExt C] in
/-- Explicit form of the incoming term in the positive-degree short complex. -/
def positiveX₁AddEquiv (A : C) (n : ℕ) :
    (positiveShortComplex R A n).X₁ ≃+ (A ⟶ R.cocomplex.X n) := AddEquiv.refl _

omit [HasExt C] in
/-- Explicit form of the cycle term in the positive-degree short complex. -/
def positiveX₂AddEquiv (A : C) (n : ℕ) :
    (positiveShortComplex R A n).X₂ ≃+ (A ⟶ R.cocomplex.X (n + 1)) := AddEquiv.refl _

omit [HasExt C] in
/-- Explicit form of the outgoing term in the positive-degree short complex. -/
def positiveX₃AddEquiv (A : C) (n : ℕ) :
    (positiveShortComplex R A n).X₃ ≃+ (A ⟶ R.cocomplex.X ((n + 1) + 1)) :=
  AddEquiv.refl _

omit [HasExt C] in
/-- The incoming map of the positive-degree short complex is postcomposition with `d n (n+1)`. -/
@[simp] theorem positiveShortComplex_f_apply (A : C) (n : ℕ)
    (x : (positiveShortComplex R A n).X₁) :
    positiveX₂AddEquiv R A n ((positiveShortComplex R A n).f x) =
      positiveX₁AddEquiv R A n x ≫ R.cocomplex.d n (n + 1) := rfl

omit [HasExt C] in
/-- The outgoing map of the positive-degree short complex is postcomposition with `d (n+1) (n+2)`. -/
@[simp] theorem positiveShortComplex_g_apply (A : C) (n : ℕ)
    (x : (positiveShortComplex R A n).X₂) :
    positiveX₃AddEquiv R A n ((positiveShortComplex R A n).g x) =
      positiveX₂AddEquiv R A n x ≫
        R.cocomplex.d (n + 1) ((n + 1) + 1) := rfl

omit [HasExt C] in
/-- Precomposition acts on the middle term of the positive-degree short complex by composing
with `a` on the left. -/
@[simp] theorem positiveShortComplexMap_τ₂_apply {A A' : C} (a : A' ⟶ A)
    (n : ℕ) (x : (positiveShortComplex R A n).X₂) :
    positiveX₂AddEquiv R A' n ((positiveShortComplexMap R a n).τ₂ x) =
      a ≫ positiveX₂AddEquiv R A n x := rfl

omit [HasExt C] in
/-- A member of the explicit kernel is a literal cocycle in the resolution. -/
theorem positiveCycle_isCycle (A : C) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    positiveX₂AddEquiv R A n z.1 ≫
      R.cocomplex.d (n + 1) ((n + 1) + 1) = 0 := by
  have hz := AddMonoidHom.mem_ker.mp z.property
  have hz' := congrArg (positiveX₃AddEquiv R A n) hz
  rw [positiveShortComplex_g_apply] at hz'
  exact hz'.trans (positiveX₃AddEquiv R A n).map_zero

omit [HasExt C] in
/-- Precomposition sends an explicit positive-degree cycle to a cycle. -/
def positiveCyclePrecomp {A A' : C} (a : A' ⟶ A) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    AddMonoidHom.ker ((positiveShortComplex R A' n).g.hom) :=
  ⟨(positiveX₂AddEquiv R A' n).symm
      (a ≫ positiveX₂AddEquiv R A n z.1), by
    rw [AddMonoidHom.mem_ker]
    apply (positiveX₃AddEquiv R A' n).injective
    rw [positiveShortComplex_g_apply, AddEquiv.apply_symm_apply,
      (positiveX₃AddEquiv R A' n).map_zero, Category.assoc,
      positiveCycle_isCycle]
    simp⟩

omit [HasExt C] in
/-- Precomposition sends a cocycle to the cocycle obtained by composing with `a`. -/
theorem positiveShortComplexMap_τ₂_cycle {A A' : C} (a : A' ⟶ A)
    (n : ℕ) (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    (positiveShortComplexMap R a n).τ₂ z.1 =
      (positiveCyclePrecomp R a n z).1 := by
  apply (positiveX₂AddEquiv R A' n).injective
  rw [positiveShortComplexMap_τ₂_apply]
  unfold positiveCyclePrecomp
  rw [AddEquiv.apply_symm_apply]

/-- Cycles in positive degree map directly to Ext through Mathlib's native
injective-resolution constructor. -/
def positiveCyclesToExt (A : C) (n : ℕ) :
    AddMonoidHom.ker ((positiveShortComplex R A n).g.hom) →+
      Ext A F (n + 1) where
  toFun z := R.extMk (positiveX₂AddEquiv R A n z.1)
      ((n + 1) + 1) rfl (positiveCycle_isCycle R A n z)
  map_zero' := by
    change R.extMk (positiveX₂AddEquiv R A n (0 :
      AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)))
        ((n + 1) + 1) rfl _ = 0
    have hz : positiveX₂AddEquiv R A n (0 :
        AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) = 0 :=
      (positiveX₂AddEquiv R A n).map_zero
    simpa only [hz] using (R.extMk_zero (X := A) ((n + 1) + 1) rfl)
  map_add' x y := by
    symm
    apply R.add_extMk

/-- The cycle-to-Ext map is natural under precomposition. -/
theorem positiveCyclesToExt_precomp {A A' : C} (a : A' ⟶ A) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    ((extFunctor (C := C) (n + 1)).map a.op).app F
        (positiveCyclesToExt R A n z) =
      positiveCyclesToExt R A' n (positiveCyclePrecomp R a n z) := by
  change (Ext.mk₀ a).comp
      (R.extMk (positiveX₂AddEquiv R A n z.1) ((n + 1) + 1) rfl
        (positiveCycle_isCycle R A n z)) (zero_add (n + 1)) =
    R.extMk
      (positiveX₂AddEquiv R A' n (positiveCyclePrecomp R a n z).1)
      ((n + 1) + 1) rfl
        (positiveCycle_isCycle R A' n (positiveCyclePrecomp R a n z))
  rw [R.mk₀_comp_extMk]
  congr 1

/-- A literal boundary has trivial Ext class. -/
theorem positiveCyclesToExt_boundary (A : C) (n : ℕ)
    (x : (positiveShortComplex R A n).X₁) :
    positiveCyclesToExt R A n
        ((positiveShortComplex R A n).abToCycles x) = 0 := by
  change R.extMk
    (positiveX₁AddEquiv R A n x ≫ R.cocomplex.d n (n + 1))
      ((n + 1) + 1) rfl
      (by rw [Category.assoc, R.complex_d_comp n]; simp) = 0
  apply (R.extMk_eq_zero_iff _ _ rfl _ n rfl).2
  exact ⟨positiveX₁AddEquiv R A n x, rfl⟩

/-- The positive-degree comparison after quotienting cycles by boundaries. -/
def positiveQuotientToExt (A : C) (n : ℕ) :
    (AddMonoidHom.ker ((positiveShortComplex R A n).g.hom) ⧸
        AddMonoidHom.range ((positiveShortComplex R A n).abToCycles)) →+
      Ext A F (n + 1) :=
  QuotientAddGroup.lift _ (positiveCyclesToExt R A n) (by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    rw [AddMonoidHom.mem_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact positiveCyclesToExt_boundary R A n x)

/-- Every class in `Extⁿ⁺¹(A, F)` comes from a cocycle in `Hom(A, R•)`. -/
theorem positiveQuotientToExt_surjective (A : C) (n : ℕ) :
    Function.Surjective (positiveQuotientToExt R A n) := by
  intro α
  obtain ⟨f, hf, hfα⟩ := R.extMk_surjective α ((n + 1) + 1) rfl
  let z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom) :=
    ⟨(positiveX₂AddEquiv R A n).symm f, by
      rw [AddMonoidHom.mem_ker]
      apply (positiveX₃AddEquiv R A n).injective
      rw [positiveShortComplex_g_apply, AddEquiv.apply_symm_apply,
        (positiveX₃AddEquiv R A n).map_zero]
      exact hf⟩
  refine ⟨QuotientAddGroup.mk' _ z, ?_⟩
  change positiveCyclesToExt R A n z = α
  change R.extMk (positiveX₂AddEquiv R A n z.1) ((n + 1) + 1) rfl
    (positiveCycle_isCycle R A n z) = α
  have hz : positiveX₂AddEquiv R A n z.1 = f := AddEquiv.apply_symm_apply _ _
  simpa only [hz] using hfα

/-- Every class in `Extⁿ⁺¹(A, F)` is the class of a literal cocycle. -/
theorem positiveCyclesToExt_surjective (A : C) (n : ℕ) :
    Function.Surjective (positiveCyclesToExt R A n) := by
  intro α
  obtain ⟨q, hq⟩ := positiveQuotientToExt_surjective R A n α
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  exact ⟨z, hq⟩

/-- A cocycle whose Ext class vanishes is a coboundary. -/
theorem positiveQuotientToExt_injective (A : C) (n : ℕ) :
    Function.Injective (positiveQuotientToExt R A n) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  apply (QuotientAddGroup.eq_zero_iff z).2
  rw [AddMonoidHom.mem_range]
  change positiveCyclesToExt R A n z = 0 at hq
  change R.extMk (positiveX₂AddEquiv R A n z.1)
    ((n + 1) + 1) rfl (positiveCycle_isCycle R A n z) = 0 at hq
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff _ _ rfl _ n rfl).1 hq
  refine ⟨(positiveX₁AddEquiv R A n).symm g, ?_⟩
  apply Subtype.ext
  apply (positiveX₂AddEquiv R A n).injective
  change positiveX₂AddEquiv R A n
      ((positiveShortComplex R A n).f ((positiveX₁AddEquiv R A n).symm g)) =
    positiveX₂AddEquiv R A n z.1
  rw [positiveShortComplex_f_apply, AddEquiv.apply_symm_apply]
  exact hg

/-- Cocycles modulo coboundaries in positive degree are in bijection with `Extⁿ⁺¹(A, F)`. -/
theorem positiveQuotientToExt_bijective (A : C) (n : ℕ) :
    Function.Bijective (positiveQuotientToExt R A n) :=
  ⟨positiveQuotientToExt_injective R A n, positiveQuotientToExt_surjective R A n⟩

/-- In every strictly positive degree, homology of the evaluated injective
resolution is canonically isomorphic to Mathlib's `Ext`. -/
def positiveHomologyExtIso (A : C) (n : ℕ) :
    (evaluatedResolution R A).homology (n + 1) ≅ AddCommGrpCat.of (Ext A F (n + 1)) :=
  (evaluatedResolution R A).homologyIsoSc' n (n + 1) ((n + 1) + 1) (by simp) (by simp) ≪≫
    (positiveShortComplex R A n).abHomologyIso ≪≫
      (AddEquiv.ofBijective (positiveQuotientToExt R A n)
        (positiveQuotientToExt_bijective R A n)).toAddCommGrpIso

/-- The homology class represented by an explicit positive-degree cycle. -/
def positiveCycleClass (A : C) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    (evaluatedResolution R A).homology (n + 1) :=
  ((evaluatedResolution R A).homologyIsoSc' n (n + 1) ((n + 1) + 1)
      (by simp) (by simp)).inv
    (ShortComplex.shortCycleClass (positiveShortComplex R A n) z.1
      (AddMonoidHom.mem_ker.mp z.property))

omit [HasExt C] in
/-- The explicit positive-degree representative is natural under
precomposition. -/
theorem positiveCycleClass_naturality {A A' : C} (a : A' ⟶ A) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    HomologicalComplex.homologyMap (evaluatedResolutionMap R a) (n + 1)
        (positiveCycleClass R A n z) =
      positiveCycleClass R A' n (positiveCyclePrecomp R a n z) := by
  apply (AddCommGrpCat.mono_iff_injective
    ((evaluatedResolution R A').homologyIsoSc' n (n + 1) ((n + 1) + 1)
      (by simp) (by simp)).hom).mp inferInstance
  rw [← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyIsoSc'_hom_naturality (evaluatedResolutionMap R a),
    ConcreteCategory.comp_apply]
  simp only [positiveCycleClass, Iso.inv_hom_id_apply]
  have hmap := ShortComplex.shortHomologyMap_cycleClass
    (positiveShortComplexMap R a n) z.1
    (AddMonoidHom.mem_ker.mp z.property)
    (AddMonoidHom.mem_ker.mp (positiveCyclePrecomp R a n z).property)
  rw [hmap]
  unfold ShortComplex.shortCycleClass
  apply congrArg (fun q : AddMonoidHom.ker
      ((positiveShortComplex R A' n).g.hom) =>
    (positiveShortComplex R A' n).homologyπ
      ((positiveShortComplex R A' n).abCyclesIso.inv q))
  apply Subtype.ext
  exact positiveShortComplexMap_τ₂_cycle R a n z

/-- The comparison isomorphism sends the class of a cocycle to its `Ext` class. -/
theorem positiveHomologyExtIso_hom_cycleClass (A : C) (n : ℕ)
    (z : AddMonoidHom.ker ((positiveShortComplex R A n).g.hom)) :
    (positiveHomologyExtIso R A n).hom (positiveCycleClass R A n z) =
      positiveCyclesToExt R A n z := by
  simp only [positiveHomologyExtIso, positiveCycleClass, Iso.trans_hom,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  have hz : (positiveShortComplex R A n).abHomologyIso.hom
      ((positiveShortComplex R A n).homologyπ
        ((positiveShortComplex R A n).abCyclesIso.inv z)) =
      QuotientAddGroup.mk' _ z := by
    rw [← ConcreteCategory.comp_apply,
      ShortComplex.ab_homologyπ_comp_abHomologyIso_hom,
      ConcreteCategory.comp_apply]
    have hzi : (positiveShortComplex R A n).abCyclesIso.hom
        ((positiveShortComplex R A n).abCyclesIso.inv z) = z := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        ConcreteCategory.congr_hom
          (positiveShortComplex R A n).abCyclesIso.inv_hom_id z
    rw [hzi]
    rfl
  unfold ShortComplex.shortCycleClass
  rw [hz]
  rfl

/-- Every element of the positive homology of the evaluated resolution is the class of a cocycle. -/
theorem positiveCycleClass_surjective (A : C) (n : ℕ) :
    Function.Surjective (positiveCycleClass R A n) := by
  intro x
  obtain ⟨z, hz⟩ := positiveCyclesToExt_surjective R A n
    ((positiveHomologyExtIso R A n).hom x)
  refine ⟨z, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective
    (positiveHomologyExtIso R A n).hom).mp inferInstance
  rw [positiveHomologyExtIso_hom_cycleClass, hz]

/-- The positive-degree comparison between the homology of the evaluated resolution and `Ext`
is natural in the represented object. -/
@[reassoc]
theorem positiveHomologyExtIso_hom_naturality {A A' : C} (a : A' ⟶ A)
    (n : ℕ) :
    HomologicalComplex.homologyMap (evaluatedResolutionMap R a) (n + 1) ≫
        (positiveHomologyExtIso R A' n).hom =
      (positiveHomologyExtIso R A n).hom ≫
        ((extFunctor (C := C) (n + 1)).map a.op).app F := by
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨z, rfl⟩ := positiveCycleClass_surjective R A n x
  change (positiveHomologyExtIso R A' n).hom
      (HomologicalComplex.homologyMap (evaluatedResolutionMap R a) (n + 1)
        (positiveCycleClass R A n z)) =
    ((extFunctor (C := C) (n + 1)).map a.op).app F
      ((positiveHomologyExtIso R A n).hom (positiveCycleClass R A n z))
  rw [positiveCycleClass_naturality,
    positiveHomologyExtIso_hom_cycleClass,
    positiveHomologyExtIso_hom_cycleClass,
    positiveCyclesToExt_precomp]

/-- Homology of a literally evaluated complex, functorial in the
coyoneda variable. -/
def coyonedaHomologyFunctor (K : CochainComplex C ℕ) (m : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat where
  obj A := (((preadditiveCoyoneda.obj A).mapHomologicalComplex (.up ℕ)).obj K).homology m
  map a := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a) (.up ℕ)).app K) m
  map_id A := by
    have h : ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (𝟙 A))
        (.up ℕ)).app K) = 𝟙 _ := by
      ext i f
      exact Category.id_comp f
    exact (congrArg (fun φ => HomologicalComplex.homologyMap φ m) h).trans
      (HomologicalComplex.homologyMap_id _ _)
  map_comp a b := by
    simp only [Functor.map_comp, NatTrans.mapHomologicalComplex_comp,
      NatTrans.comp_app, HomologicalComplex.homologyMap_comp]

/-- In positive degree, the direct quotient comparison packages as a
natural isomorphism of functors on represented objects. -/
def positiveHomologyExtNatIso (n : ℕ) :
    coyonedaHomologyFunctor R.cocomplex (n + 1) ≅
      (extFunctor (C := C) (n + 1)).flip.obj F :=
  NatIso.ofComponents (fun A => positiveHomologyExtIso R A.unop n)
    (fun a => positiveHomologyExtIso_hom_naturality R a.unop n)

end InjectiveResolution

end CategoryTheory
