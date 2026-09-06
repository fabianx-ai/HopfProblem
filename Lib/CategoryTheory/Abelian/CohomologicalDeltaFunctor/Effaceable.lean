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

namespace Effacement

variable {T S : CohomologicalDeltaFunctor C D} {m n : ℕ}

set_option linter.unusedVariables false in
/-- Enlarging through the middle object of a short exact sequence remains effacing
(U-G5a; equation (U19)). -/
theorem ofShortExact_map_eq_zero {E : ShortComplex C} (hE : E.ShortExact)
    (e : Effacement T m E.X₂) : (T.T m).obj.map (E.f ≫ e.i) = 0 := by
  rw [CategoryTheory.Functor.map_comp, e.map_eq_zero, comp_zero]

/-- The effacement of the left object obtained by composing through the middle object
(U-G5b; before equation (U19)). -/
def ofShortExact {E : ShortComplex C} (hE : E.ShortExact) (e : Effacement T m E.X₂) :
    Effacement T m E.X₁ where
  M := e.M
  i := E.f ≫ e.i
  mono := haveI := hE.mono_f; mono_comp _ _
  map_eq_zero := ofShortExact_map_eq_zero hE e

/-- The cokernel obligation for the middle-object enlargement (U-G5b′; before (U20)). -/
theorem f_comp_comp_π {E : ShortComplex C} (e : Effacement T m E.X₂) :
    E.f ≫ (e.i ≫ cokernel.π (E.f ≫ e.i)) = 0 := by
  rw [← Category.assoc, cokernel.condition]

/-- The morphism from an arbitrary short exact sequence to its effacing enlargement
(U-G5c; equation (U20)). -/
def homOfShortExact {E : ShortComplex C} (hE : E.ShortExact)
    (e : Effacement T m E.X₂) : E ⟶ (ofShortExact hE e).shortComplex where
  τ₁ := 𝟙 _
  τ₂ := e.i
  τ₃ := haveI := hE.epi_g
    hE.exact.desc (e.i ≫ cokernel.π (E.f ≫ e.i)) (f_comp_comp_π e)
  comm₁₂ := Category.id_comp _
  comm₂₃ := haveI := hE.epi_g; (hE.exact.g_desc _ _).symm

end Effacement

section Assembly

variable {T S : CohomologicalDeltaFunctor C D} {n : ℕ}

/-- The next-degree transformation commutes with the connecting morphism of every short exact
sequence (U-G5d; equations (U21)–(U22)). -/
theorem nextApp_comm (η : (T.T n).obj ⟶ (S.T n).obj) (h : T.EffaceableAt (n + 1))
    {E : ShortComplex C} (hE : E.ShortExact) :
    T.δ hE n ≫ (nextApp η h).app E.X₁ = η.app E.X₃ ≫ S.δ hE n := by
  let e := Effacement.ofShortExact hE (h.effacement E.X₂)
  let φ := Effacement.homOfShortExact hE (h.effacement E.X₂)
  let c : E.X₃ ⟶ cokernel e.i := φ.τ₃
  let dT : (T.T n).obj.obj (cokernel e.i) ⟶ (T.T (n + 1)).obj.obj E.X₁ := T.δ e.shortExact n
  let dS : (S.T n).obj.obj (cokernel e.i) ⟶ (S.T (n + 1)).obj.obj E.X₁ := S.δ e.shortExact n
  have hT := T.naturality hE e.shortExact φ n
  change (T.T n).obj.map c ≫ dT =
    T.δ hE n ≫ (T.T (n + 1)).obj.map (𝟙 E.X₁) at hT
  have hS := S.naturality hE e.shortExact φ n
  change (S.T n).obj.map c ≫ dS =
    S.δ hE n ≫ (S.T (n + 1)).obj.map (𝟙 E.X₁) at hS
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hT hS
  have hη := η.naturality c
  have hδ := Effacement.δ_component η e
  change dT ≫ Effacement.component η e = η.app (cokernel e.i) ≫ dS at hδ
  rw [nextApp_app_eq_component η h e, ← hT, Category.assoc, hδ,
    ← Category.assoc, hη, Category.assoc, hS]

/-- A next-degree extension compatible with every effacing connecting morphism is unique
(U-G6; equation (U23)). -/
theorem nextApp_unique (η : (T.T n).obj ⟶ (S.T n).obj) (h : T.EffaceableAt (n + 1))
    (θ : (T.T (n + 1)).obj ⟶ (S.T (n + 1)).obj)
    (hθ : ∀ {A : C} (e : Effacement T (n + 1) A),
      T.δ e.shortExact n ≫ θ.app A = η.app (cokernel e.i) ≫ S.δ e.shortExact n) :
    θ = nextApp η h := by
  apply NatTrans.ext
  funext A
  let e := h.effacement A
  let dT : (T.T n).obj.obj (cokernel e.i) ⟶ (T.T (n + 1)).obj.obj A := T.δ e.shortExact n
  let dS : (S.T n).obj.obj (cokernel e.i) ⟶ (S.T (n + 1)).obj.obj A := S.δ e.shortExact n
  let _ : Epi dT := e.epi_δ
  apply (cancel_epi dT).mp
  rw [nextApp_app]
  have hθe := hθ e
  change dT ≫ θ.app A = η.app (cokernel e.i) ≫ dS at hθe
  have hδe := Effacement.δ_component η e
  change dT ≫ Effacement.component η e = η.app (cokernel e.i) ≫ dS at hδe
  exact hθe.trans hδe.symm

/-- The recursively constructed degreewise family extending a degree-zero transformation
(U-A1; induction after (U22)). -/
def Effaceable.extendApp (hT : T.Effaceable) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) :
    ∀ n : ℕ, (T.T n).obj ⟶ (S.T n).obj
  | 0 => η₀
  | n + 1 => nextApp (Effaceable.extendApp hT η₀ n) (hT (n + 1) (Nat.succ_pos n))

/-- The recursive extension starts with the prescribed degree-zero transformation (U-A2). -/
theorem Effaceable.extendApp_zero (hT : T.Effaceable) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) :
    Effaceable.extendApp hT η₀ 0 = η₀ := rfl

/-- The successor equation for the recursive extension (U-A3). -/
theorem Effaceable.extendApp_succ (hT : T.Effaceable) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj)
    (n : ℕ) :
    Effaceable.extendApp hT η₀ (n + 1) =
      nextApp (Effaceable.extendApp hT η₀ n) (hT (n + 1) (Nat.succ_pos n)) := rfl

/-- The recursive family assembled as a morphism of cohomological delta functors (U-A4). -/
def Effaceable.extendHom (hT : T.Effaceable) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) : Hom T S where
  app := Effaceable.extendApp hT η₀
  comm hE n := nextApp_comm (Effaceable.extendApp hT η₀ n)
    (hT (n + 1) (Nat.succ_pos n)) hE

/-- The assembled morphism has the prescribed degree-zero component (U-A5). -/
theorem Effaceable.extendHom_app_zero (hT : T.Effaceable)
    (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) :
    (Effaceable.extendHom hT η₀).app 0 = η₀ := rfl

/-- Every morphism out of an effaceable delta functor is the recursively constructed extension
of its degree-zero component (U-A6; final induction after (U23)). -/
theorem Effaceable.hom_eq_extendHom (hT : T.Effaceable) (θ : Hom T S) :
    θ = Effaceable.extendHom hT (θ.app 0) := by
  apply Hom.ext
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change θ.app n = Effaceable.extendApp hT (θ.app 0) n at ih
    exact nextApp_unique (Effaceable.extendApp hT (θ.app 0) n)
      (hT (n + 1) (Nat.succ_pos n)) (θ.app (n + 1))
      (fun {A} e => by
        let dT : (T.T n).obj.obj (cokernel e.i) ⟶ (T.T (n + 1)).obj.obj A :=
          T.δ e.shortExact n
        let dS : (S.T n).obj.obj (cokernel e.i) ⟶ (S.T (n + 1)).obj.obj A :=
          S.δ e.shortExact n
        change dT ≫ (θ.app (n + 1)).app A =
          (Effaceable.extendApp hT (θ.app 0) n).app (cokernel e.i) ≫ dS
        have hcomm := θ.comm e.shortExact n
        change dT ≫ (θ.app (n + 1)).app A = (θ.app n).app (cokernel e.i) ≫ dS at hcomm
        rw [hcomm, ih])

/-- Hartshorne III.1.3A / Grothendieck, Tôhoku II.2.2.1 / Stacks 010T: an effaceable
cohomological delta functor is universal (U-A7). -/
theorem Effaceable.isUniversal (hT : T.Effaceable) : T.IsUniversal :=
  fun S η₀ =>
    ⟨Effaceable.extendHom hT η₀, Effaceable.extendHom_app_zero hT η₀,
      fun θ hθ => by rw [Effaceable.hom_eq_extendHom hT θ, hθ]⟩

end Assembly

end CategoryTheory.CohomologicalDeltaFunctor
