/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Effaceable and universal cohomological delta functors

Reusable definitions of effaceability and the universal extension property for cohomological
delta functors.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A delta functor is effaceable at degree `n` when every object embeds into one on which the
induced degree-`n` map vanishes (L-E1). -/
def EffaceableAt (T : CohomologicalDeltaFunctor C D) (n : ℕ) : Prop :=
  ∀ A : C, ∃ (M : C) (i : A ⟶ M), Mono i ∧ (T.T n).obj.map i = 0

/-- A delta functor is effaceable when it is effaceable in every positive degree (L-E2). -/
def Effaceable (T : CohomologicalDeltaFunctor C D) : Prop :=
  ∀ n : ℕ, 0 < n → T.EffaceableAt n

/-- Universality is the unique extension of every degree-zero natural transformation to a
morphism of delta functors (L-U1). -/
def IsUniversal (T : CohomologicalDeltaFunctor C D) : Prop :=
  ∀ (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj),
    ∃! η : Hom T S, η.app 0 = η₀

/-- The universal extension selected from the unique-existence property (L-U2). -/
def IsUniversal.extend {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) : Hom T S :=
  (h S η₀).exists.choose

/-- The selected universal extension has the prescribed degree-zero component (L-U3). -/
theorem IsUniversal.extend_app_zero {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) :
    (h.extend S η₀).app 0 = η₀ :=
  (h S η₀).exists.choose_spec

/-- Universal morphisms agreeing in degree zero agree in every degree (L-U4). -/
theorem IsUniversal.hom_ext {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    {S : CohomologicalDeltaFunctor C D} {η η' : Hom T S}
    (h0 : η.app 0 = η'.app 0) : η = η' :=
  (h S (η.app 0)).unique rfl h0.symm

/-! ## Constructing the next degree from effacements -/

/-- An effacement of `A` in degree `m`: a monomorphism killed by `Tᵐ` (U-E1; before (U5)). -/
structure Effacement (T : CohomologicalDeltaFunctor C D) (m : ℕ) (A : C) where
  M : C
  i : A ⟶ M
  mono : Mono i
  map_eq_zero : (T.T m).obj.map i = 0

attribute [instance] Effacement.mono

namespace Effacement

variable {T S : CohomologicalDeltaFunctor C D} {m n : ℕ} {A A' : C}

/-- The canonical cokernel short complex of an effacement (U-E2). -/
def shortComplex (e : Effacement T m A) : ShortComplex C :=
  ShortComplex.mk e.i (cokernel.π e.i) (cokernel.condition e.i)

/-- The cokernel short complex of an effacement is short exact (U-E3). -/
theorem shortExact (e : Effacement T m A) : e.shortComplex.ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel e.i) e.mono
    (inferInstance : Epi (cokernel.π e.i))

end Effacement

/-- Choose an effacement from effaceability at a degree (U-E4). -/
def EffaceableAt.effacement {T : CohomologicalDeltaFunctor C D} {m : ℕ} (h : T.EffaceableAt m)
    (A : C) : Effacement T m A where
  M := (h A).choose
  i := (h A).choose_spec.choose
  mono := (h A).choose_spec.choose_spec.1
  map_eq_zero := (h A).choose_spec.choose_spec.2

namespace Effacement

variable {T S : CohomologicalDeltaFunctor C D} {m n : ℕ} {A A' : C}

/-- The connecting morphism associated to an effacement is epic (U-G1; equation (U5)). -/
theorem epi_δ (e : Effacement T (n + 1) A) : Epi (T.δ e.shortExact n) :=
  (T.exact₃ e.shortExact n).epi_f e.map_eq_zero

/-- The candidate next component vanishes on the preceding image (U-G2a; equation (U6)). -/
theorem map_comp_δ_zero (η : (T.T n).obj ⟶ (S.T n).obj)
    (e : Effacement T (n + 1) A) :
    (T.T n).obj.map e.shortComplex.g ≫ (η.app (cokernel e.i) ≫ S.δ e.shortExact n) = 0 := by
  change (T.T n).obj.map e.shortComplex.g ≫
    (η.app e.shortComplex.X₃ ≫ S.δ e.shortExact n) = 0
  rw [← Category.assoc, η.naturality, Category.assoc, S.comp₂ e.shortExact n, comp_zero]

/-- The next-degree component factored through the epic connecting morphism
(U-G2b; equations (U7)–(U8)). -/
def component (η : (T.T n).obj ⟶ (S.T n).obj) (e : Effacement T (n + 1) A) :
    (T.T (n + 1)).obj.obj A ⟶ (S.T (n + 1)).obj.obj A :=
  haveI := e.epi_δ
  (T.exact₂ e.shortExact n).desc (η.app (cokernel e.i) ≫ S.δ e.shortExact n)
    (map_comp_δ_zero η e)

/-- The defining square for an effacement component (U-G2c; equation (U7)). -/
theorem δ_component (η : (T.T n).obj ⟶ (S.T n).obj) (e : Effacement T (n + 1) A) :
    T.δ e.shortExact n ≫ component η e = η.app (cokernel e.i) ≫ S.δ e.shortExact n :=
  haveI := e.epi_δ
  (T.exact₂ e.shortExact n).g_desc _ _

/-- The cokernel obligation induced by a commuting square of effacements
(U-G3a′; equation (U9)). -/
theorem comm_comp_π (e : Effacement T m A) (e' : Effacement T m A') (a : A ⟶ A')
    (b : e.M ⟶ e'.M) (h : e.i ≫ b = a ≫ e'.i) :
    e.i ≫ (b ≫ cokernel.π e'.i) = 0 := by
  rw [← Category.assoc, h, Category.assoc, cokernel.condition, comp_zero]

/-- A commuting square of effacements induces a morphism of their cokernel sequences
(U-G3a; equation (U9)). -/
def homOfComm (e : Effacement T m A) (e' : Effacement T m A') (a : A ⟶ A')
    (b : e.M ⟶ e'.M) (h : e.i ≫ b = a ≫ e'.i) : e.shortComplex ⟶ e'.shortComplex where
  τ₁ := a
  τ₂ := b
  τ₃ := cokernel.desc e.i (b ≫ cokernel.π e'.i) (comm_comp_π e e' a b h)
  comm₁₂ := h.symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- Components respect comparisons of effacements (U-G3b; equations (U10)–(U11)). -/
theorem component_comm (η : (T.T n).obj ⟶ (S.T n).obj)
    (e : Effacement T (n + 1) A) (e' : Effacement T (n + 1) A') (a : A ⟶ A') (b : e.M ⟶ e'.M)
    (h : e.i ≫ b = a ≫ e'.i) :
    (T.T (n + 1)).obj.map a ≫ component η e' = component η e ≫ (S.T (n + 1)).obj.map a := by
  let dT : (T.T n).obj.obj (cokernel e.i) ⟶ (T.T (n + 1)).obj.obj A := T.δ e.shortExact n
  let dT' : (T.T n).obj.obj (cokernel e'.i) ⟶ (T.T (n + 1)).obj.obj A' := T.δ e'.shortExact n
  let dS : (S.T n).obj.obj (cokernel e.i) ⟶ (S.T (n + 1)).obj.obj A := S.δ e.shortExact n
  let dS' : (S.T n).obj.obj (cokernel e'.i) ⟶ (S.T (n + 1)).obj.obj A' := S.δ e'.shortExact n
  let c : cokernel e.i ⟶ cokernel e'.i := (homOfComm e e' a b h).τ₃
  let _ : Epi dT := e.epi_δ
  apply (cancel_epi dT).mp
  have hT := T.naturality e.shortExact e'.shortExact (homOfComm e e' a b h) n
  change (T.T n).obj.map c ≫ dT' =
    dT ≫ (T.T (n + 1)).obj.map a at hT
  have hS := S.naturality e.shortExact e'.shortExact (homOfComm e e' a b h) n
  change (S.T n).obj.map c ≫ dS' =
    dS ≫ (S.T (n + 1)).obj.map a at hS
  have hη := η.naturality (homOfComm e e' a b h).τ₃
  change (T.T n).obj.map c ≫ η.app (cokernel e'.i) =
    η.app (cokernel e.i) ≫ (S.T n).obj.map c at hη
  have hδe' := δ_component η e'
  change dT' ≫ component η e' = η.app (cokernel e'.i) ≫ dS' at hδe'
  have hδe := δ_component η e
  change dT ≫ component η e = η.app (cokernel e.i) ≫ dS at hδe
  calc dT ≫ (T.T (n + 1)).obj.map a ≫ component η e'
      = (T.T n).obj.map c ≫ dT' ≫ component η e' := by
        rw [← Category.assoc, ← hT, Category.assoc]
    _ = (T.T n).obj.map c ≫ η.app (cokernel e'.i) ≫ dS' := by
        rw [hδe']
    _ = η.app (cokernel e.i) ≫
        (S.T n).obj.map c ≫ dS' := by
        rw [← Category.assoc, hη, Category.assoc]
    _ = η.app (cokernel e.i) ≫ dS ≫
        (S.T (n + 1)).obj.map a := by
        rw [hS]
    _ = dT ≫ component η e ≫ (S.T (n + 1)).obj.map a := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (S.T (n + 1)).obj.map a) hδe.symm

/-- The biproduct common effacement is killed by the functor (U-G3c; equation (U13)). -/
theorem biprod_map_eq_zero (e e' : Effacement T m A) :
    (T.T m).obj.map (biprod.lift e.i e'.i) = 0 := by
  simp only [Limits.biprod.lift_eq, CategoryTheory.Functor.map_add,
    CategoryTheory.Functor.map_comp, e.map_eq_zero, e'.map_eq_zero, zero_comp, add_zero]

/-- The common biproduct effacement comparing two choices (U-G3d; equation (U12)). -/
def biprod (e e' : Effacement T m A) : Effacement T m A where
  M := e.M ⊞ e'.M
  i := biprod.lift e.i e'.i
  mono := mono_of_mono_fac (biprod.lift_fst e.i e'.i)
  map_eq_zero := biprod_map_eq_zero e e'

/-- Comparison with the left summand of a common effacement (U-G3e-left; equation (U14)). -/
theorem component_biprod_left (η : (T.T n).obj ⟶ (S.T n).obj)
    (e e' : Effacement T (n + 1) A) :
    component η (e.biprod e') = component η e := by
  have h := component_comm η (e.biprod e') e (𝟙 A) Limits.biprod.fst
    (by rw [Category.id_comp]; exact Limits.biprod.lift_fst e.i e'.i)
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, eq_comm] at h

/-- Comparison with the right summand of a common effacement (U-G3e-right; equation (U14)). -/
theorem component_biprod_right (η : (T.T n).obj ⟶ (S.T n).obj)
    (e e' : Effacement T (n + 1) A) :
    component η (e.biprod e') = component η e' := by
  have h := component_comm η (e.biprod e') e' (𝟙 A) Limits.biprod.snd
    (by rw [Category.id_comp]; exact Limits.biprod.lift_snd e.i e'.i)
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, eq_comm] at h

/-- The constructed component is independent of the chosen effacement (U-G3f). -/
theorem component_eq (η : (T.T n).obj ⟶ (S.T n).obj)
    (e e' : Effacement T (n + 1) A) : component η e = component η e' :=
  (component_biprod_left η e e').symm.trans (component_biprod_right η e e')

/-- The graph effacement is killed by the functor (U-G4a; equation (U16)). -/
theorem graph_map_eq_zero (e : Effacement T m A) (f : A ⟶ A')
    (e' : Effacement T m A') :
    (T.T m).obj.map (biprod.lift e.i (f ≫ e'.i)) = 0 := by
  simp only [Limits.biprod.lift_eq, CategoryTheory.Functor.map_add,
    CategoryTheory.Functor.map_comp, e.map_eq_zero, e'.map_eq_zero, zero_comp, comp_zero, add_zero]

/-- The graph effacement associated to an arbitrary morphism (U-G4b; equation (U15)). -/
def graph (e : Effacement T m A) (f : A ⟶ A') (e' : Effacement T m A') :
    Effacement T m A where
  M := e.M ⊞ e'.M
  i := biprod.lift e.i (f ≫ e'.i)
  mono := mono_of_mono_fac (biprod.lift_fst e.i (f ≫ e'.i))
  map_eq_zero := graph_map_eq_zero e f e'

/-- Comparing along the graph effacement (U-G4c; equation (U17)). -/
theorem component_graph (η : (T.T n).obj ⟶ (S.T n).obj)
    (e : Effacement T (n + 1) A) (f : A ⟶ A') (e' : Effacement T (n + 1) A') :
    (T.T (n + 1)).obj.map f ≫ component η e' =
      component η (e.graph f e') ≫ (S.T (n + 1)).obj.map f :=
  component_comm η (e.graph f e') e' f Limits.biprod.snd (Limits.biprod.lift_snd _ _)

/-- The constructed components are natural in the object (U-G4d; equation (U18)). -/
theorem component_naturality (η : (T.T n).obj ⟶ (S.T n).obj)
    (e : Effacement T (n + 1) A) (e' : Effacement T (n + 1) A') (f : A ⟶ A') :
    (T.T (n + 1)).obj.map f ≫ component η e' = component η e ≫ (S.T (n + 1)).obj.map f :=
  (component_graph η e f e').trans (by rw [component_eq η (e.graph f e') e])

end Effacement

section

variable {T S : CohomologicalDeltaFunctor C D} {n : ℕ}

/-- The natural transformation in the next degree selected from effaceability
(U-N1; after equation (U18)). -/
def nextApp (η : (T.T n).obj ⟶ (S.T n).obj) (h : T.EffaceableAt (n + 1)) :
    (T.T (n + 1)).obj ⟶ (S.T (n + 1)).obj where
  app A := Effacement.component η (h.effacement A)
  naturality _ _ f := Effacement.component_naturality η _ _ f

/-- The selected next-degree component at an object (U-N2). -/
theorem nextApp_app (η : (T.T n).obj ⟶ (S.T n).obj) (h : T.EffaceableAt (n + 1)) (A : C) :
    (nextApp η h).app A = Effacement.component η (h.effacement A) := rfl

/-- The selected component agrees with the component from every effacement (U-N3; (U7)). -/
theorem nextApp_app_eq_component (η : (T.T n).obj ⟶ (S.T n).obj) (h : T.EffaceableAt (n + 1))
    {A : C} (e : Effacement T (n + 1) A) :
    (nextApp η h).app A = Effacement.component η e :=
  Effacement.component_eq η _ e

end

end CategoryTheory.CohomologicalDeltaFunctor
