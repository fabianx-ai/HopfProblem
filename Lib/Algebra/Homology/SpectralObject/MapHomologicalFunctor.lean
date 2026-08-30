/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# Applying a homological functor to a triangulated spectral object

A homological functor turns every distinguished triangle of a triangulated spectral object into
the functorial long exact sequence required by an abelian spectral object.
-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

namespace Triangulated.SpectralObject

universe uC vC uA vA uι vι

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Type uι} [Category.{vι} ι]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Apply a homological functor, together with all of its shifts, to a triangulated spectral
object. -/
@[simps]
noncomputable def mapHomologicalFunctor
    (X : SpectralObject C ι) (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ] :
    Abelian.SpectralObject A ι := by
  have hmor₁ (D : ComposableArrows ι 2) :
      X.ω₁.map ((ComposableArrows.mapFunctorArrows ι 0 1 0 2 2).app D) =
        (X.ω₂.obj D).mor₁ := by
    rw [X.ω₂_obj_mor₁]
    apply congrArg X.ω₁.map
    apply ComposableArrows.hom_ext₁
    · simp [ComposableArrows.mapFunctorArrows]
    · simp [ComposableArrows.mapFunctorArrows]
  have hmor₂ (D : ComposableArrows ι 2) :
      X.ω₁.map ((ComposableArrows.mapFunctorArrows ι 0 2 1 2 2).app D) =
        (X.ω₂.obj D).mor₂ := by
    rw [X.ω₂_obj_mor₂]
    apply congrArg X.ω₁.map
    apply ComposableArrows.hom_ext₁
    · simp [ComposableArrows.mapFunctorArrows]
    · simp [ComposableArrows.mapFunctorArrows]
  exact
    { H n := X.ω₁ ⋙ F.shift n
      δ' n₀ n₁ h :=
        { app D := F.homologySequenceδ (X.ω₂.obj D) n₀ n₁ h
          naturality D D' φ := F.homologySequenceδ_naturality
            (X.ω₂.obj D) (X.ω₂.obj D') (X.ω₂.map φ) n₀ n₁ h }
      exact₁' n₀ n₁ h D := by
        rw [Functor.comp_map, hmor₁ D]
        exact (F.homologySequence_exact₁
          (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
      exact₂' n D := by
        rw [Functor.comp_map, hmor₁ D, Functor.comp_map, hmor₂ D]
        exact (F.homologySequence_exact₂
          (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n).exact_toComposableArrows
      exact₃' n₀ n₁ h D := by
        rw [Functor.comp_map, hmor₂ D]
        exact (F.homologySequence_exact₃
          (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows }

end Triangulated.SpectralObject

end CategoryTheory
