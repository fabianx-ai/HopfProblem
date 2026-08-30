/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactFunctoriality
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Endpoint comparisons for Ext and exact functors

Given an exact additive functor `R : C ⥤ D` and a morphism `η : A ⟶ R.obj V`, this file
packages the textbook comparison

`Extⁿ(V,Y) ⟶ Extⁿ(A,R(Y))`.

It records its compatibility with morphisms, connecting classes, composites of exact functors,
and natural transformations, all in arbitrary degree.  A degree-zero representing-object
comparison becomes an equivalence in every degree when the source has enough injectives and
`R` preserves injectives.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' w'' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Abelian.Ext.ExactFunctorComparison

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w'} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w''} E]

/-- The Ext comparison induced by an exact functor and a morphism into the image of the source
object. -/
def map (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {V : C} {A : D} (η : A ⟶ R.obj V) (Y : C) (n : ℕ) :
    Ext.{w} V Y n →+ Ext.{w'} A (R.obj Y) n where
  toFun e := (Ext.mk₀ η).comp (e.mapExactFunctor R) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp

/-- In degree zero, the endpoint comparison is the literal map of morphisms. -/
theorem map_mk₀ (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V Y : C} {A : D} (η : A ⟶ R.obj V) (f : V ⟶ Y) :
    map R η Y 0 (Ext.mk₀ f) = Ext.mk₀ (η ≫ R.map f) := by
  change (Ext.mk₀ η).comp ((Ext.mk₀ f).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- The endpoint comparison commutes with covariant Ext maps. -/
theorem map_naturality (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V Y Z : C} {A : D} (η : A ⟶ R.obj V)
    (f : Y ⟶ Z) {n : ℕ} (e : Ext.{w} V Y n) :
    map R η Z n (e.comp (Ext.mk₀ f) (add_zero n)) =
      (map R η Y n e).comp (Ext.mk₀ (R.map f)) (add_zero n) := by
  simp only [map, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- The endpoint comparison commutes with the connecting class of every short exact sequence. -/
theorem map_connecting (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V : C} {A : D} (η : A ⟶ R.obj V)
    {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ} (e : Ext.{w} V S.X₃ n) :
    map R η S.X₁ (n + 1) (e.comp hS.extClass rfl) =
      (map R η S.X₃ n e).comp (hS.map_of_exact R).extClass rfl := by
  simp only [map, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ η) (e.mapExactFunctor R)
    (hS.map_of_exact R).extClass (zero_add n) rfl (by omega)).symm

/-- A bijective degree-zero morphism comparison makes the degree-zero endpoint comparison
bijective. -/
theorem map_zero_bijective (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V : C} {A : D} (η : A ⟶ R.obj V)
    (Y : C) (hη : Function.Bijective (fun f : V ⟶ Y ↦ η ≫ R.map f)) :
    Function.Bijective (map R η Y 0) := by
  constructor
  · intro e e' he
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective V Y).surjective e
    obtain ⟨f', rfl⟩ := (Ext.mk₀_bijective V Y).surjective e'
    apply congrArg Ext.mk₀
    apply hη.injective
    exact (Ext.mk₀_bijective A (R.obj Y)).injective
      ((map_mk₀ R η f).symm.trans (he.trans (map_mk₀ R η f')))
  · intro e
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (R.obj Y)).surjective e
    obtain ⟨f, hf⟩ := hη.surjective g
    exact ⟨Ext.mk₀ f, (map_mk₀ R η f).trans (congrArg Ext.mk₀ hf)⟩

attribute [local instance] Ext.subsingleton_of_injective in
/-- A degree-zero representing-object comparison extends to a bijection in every Ext degree when
the exact functor preserves injectives. -/
theorem map_bijective (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V : C} {A : D} (η : A ⟶ R.obj V)
    [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (hη : ∀ Y : C, Function.Bijective (fun f : V ⟶ Y ↦ η ≫ R.map f))
    (Y : C) (n : ℕ) : Function.Bijective (map R η Y n) := by
  induction n generalizing Y with
  | zero => exact map_zero_bijective R η Y (hη Y)
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ := R.injective_obj_of_injective I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (map R η S.X₂ n) (map R η S.X₃ n) (map R η S.X₁ (n + 1))
      (by ext e; exact (map_naturality R η S.g e).symm)
      (by ext e; exact (map_connecting R η hS e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' V hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁
        (by subsingleton) rfl)

/-- The additive equivalence supplied by a representing-object comparison and preservation of
injectives. -/
def equiv (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V : C} {A : D} (η : A ⟶ R.obj V)
    [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (hη : ∀ Y : C, Function.Bijective (fun f : V ⟶ Y ↦ η ≫ R.map f))
    (Y : C) (n : ℕ) : Ext.{w} V Y n ≃+ Ext.{w'} A (R.obj Y) n :=
  AddEquiv.ofBijective (map R η Y n) (map_bijective R η hη Y n)

/-- Endpoint comparison carries precomposition to precomposition through the mapped source
morphism, in every degree. -/
theorem precompose (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {V' V F : C} {A : D} (η : A ⟶ R.obj V')
    (g : V' ⟶ V) (n : ℕ) (α : Ext.{w} V F n) :
    map R η F n ((Ext.mk₀ g).comp α (zero_add n)) =
      map R (η ≫ R.map g) F n α := by
  change (Ext.mk₀ η).comp
    (((Ext.mk₀ g).comp α (zero_add n)).mapExactFunctor R) (zero_add n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.mk₀_comp_mk₀_assoc η (R.map g) (α.mapExactFunctor R)

/-- Sequential endpoint comparisons agree with the comparison for the composite exact functor, in
every degree. -/
theorem comp (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (S : D ⥤ E) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] [EnoughInjectives C]
    {V F : C} {A : D} {B : E} (η : A ⟶ R.obj V) (ν : B ⟶ S.obj A)
    {n : ℕ} (α : Ext.{w} V F n) :
    map S ν (R.obj F) n (map R η F n α) =
      map (R ⋙ S) (ν ≫ S.map η) F n α := by
  change (Ext.mk₀ ν).comp
    (((Ext.mk₀ η).comp (α.mapExactFunctor R) (zero_add n)).mapExactFunctor S)
      (zero_add n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_compFunctor]
  exact Ext.mk₀_comp_mk₀_assoc ν (S.map η) (α.mapExactFunctor (R ⋙ S))

/-- A natural transformation compares endpoint comparisons after the corresponding coefficient
component, in every degree. -/
theorem natTrans (R S : C ⥤ D)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (ρ : R ⟶ S) [EnoughInjectives C] {V F : C} {A : D} (η : A ⟶ R.obj V)
    {n : ℕ} (α : Ext.{w} V F n) :
    (map R η F n α).comp (Ext.mk₀ (ρ.app F)) (add_zero n) =
      map S (η ≫ ρ.app V) F n α := by
  change ((Ext.mk₀ η).comp (α.mapExactFunctor R) (zero_add n)).comp
    (Ext.mk₀ (ρ.app F)) (add_zero n) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_natTrans R S ρ α]
  exact Ext.mk₀_comp_mk₀_assoc η (ρ.app V) (α.mapExactFunctor S)

/-- Sequential comparisons followed by a coefficient natural transformation equal the comparison
at the proved composite endpoint, in every degree. -/
theorem comp_natTrans
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : D ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (Q : C ⥤ E) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (ρ : R ⋙ S ⟶ Q) [EnoughInjectives C] {V F : C} {A : D} {B : E}
    (η : A ⟶ R.obj V) (ν : B ⟶ S.obj A) (μ : B ⟶ Q.obj V)
    (h : ν ≫ S.map η ≫ ρ.app V = μ) {n : ℕ} (α : Ext.{w} V F n) :
    (map S ν (R.obj F) n (map R η F n α)).comp
        (Ext.mk₀ (ρ.app F)) (add_zero n) = map Q μ F n α := by
  have he : (ν ≫ S.map η) ≫ ρ.app V = μ := (Category.assoc _ _ _).trans h
  exact (congrArg (fun β : Ext.{w''} B ((R ⋙ S).obj F) n ↦
      β.comp (Ext.mk₀ (ρ.app F)) (add_zero n)) (comp R S η ν α)).trans
    ((natTrans (R ⋙ S) Q ρ (ν ≫ S.map η) α).trans
      (congrArg (fun e : B ⟶ Q.obj V ↦ map Q e F n α) he))

/-- A natural transformation to the identity functor recovers the original Ext class when its
source endpoint is the identity. -/
theorem natTrans_id (R : C ⥤ C) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (ρ : R ⟶ Functor.id C) [EnoughInjectives C]
    {V F : C} (η : V ⟶ R.obj V) (hη : η ≫ ρ.app V = 𝟙 V)
    {n : ℕ} (α : Ext.{w} V F n) :
    (map R η F n α).comp (Ext.mk₀ (ρ.app F)) (add_zero n) = α := by
  have hid : map (Functor.id C) (𝟙 V) F n α = α := by
    change (Ext.mk₀ (𝟙 V)).comp
      (α.mapExactFunctor (Functor.id C)) (zero_add n) = α
    exact (Ext.mk₀_id_comp (α.mapExactFunctor (Functor.id C))).trans
      (Ext.mapExactFunctor_id α)
  exact (natTrans R (Functor.id C) ρ η α).trans
    ((congrArg (fun e : V ⟶ V ↦ map (Functor.id C) e F n α) hη).trans hid)

end CategoryTheory.Abelian.Ext.ExactFunctorComparison
