/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.Neighborhood
public import Lib.CategoryTheory.Sites.Leray.HigherDirectImageSheafification
public import Lib.CategoryTheory.Sites.Leray.StalkLocalCriterion

/-!
# Stalk evaluation and normalization-relative derived adapters

For a map `f : X ⟶ Y`, a point `y : Y` and a sheaf `F` on `X`, the cohomology groups
`Hⁿ(f⁻¹U, F)` of the inverse images of the open neighbourhoods `U` of `y` form a filtered system,
and the higher direct image has the local description

`(Rⁿf_*F)_y = colim_{U ∋ y} Hⁿ(f⁻¹U, F)`

(Godement, *Topologie algébrique et théorie des faisceaux*, II.4.11; Hartshorne, *Algebraic
Geometry*, III.8.1).  This file builds the map out of that colimit induced by a compatible family
of evaluations on a finite closed subspace `i : T ⟶ X` contained in the fibre over `y`, and gives
the filtered-colimit criterion for it to be bijective.

The comparison with a pushed injective resolution is kept relative to an explicit natural
isomorphism `ρ` between the resolution homology presheaf and the Ext-defined cohomology presheaf;
this file chooses no such `ρ` and asserts no proper base change theorem.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}}

section Stalk

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- The Ext-defined source cohomology presheaf on inverse-image opens. -/
abbrev sourceCohomologyPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{0} Y :=
  (Opens.map f).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf F n

/-- The explicit-resolution source presheaf used by the current higher-direct-image theorem. -/
abbrev sourceResolutionPresheaf (I : InjectiveResolution F) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{0} Y :=
  homologyPresheaf (pushedResolution f I) n

omit [T2Space T] in
include hfi in
/-- Every inverse-image neighborhood of `y` contains the whole selected source. -/
theorem fibre_mem_preimage (U : Opens Y) (hy : y ∈ U) (t : T) :
    i t ∈ (Opens.map f).obj U := by
  change f (i t) ∈ U
  rw [hfi t]
  exact hy

/-- The neighborhood evaluations form their canonical cocone. -/
def evaluationCocone (n : ℕ) :
    Cocone ((OpenNhds.inclusion y).op ⋙ sourceCohomologyPresheaf (F := F) f n) where
  pt := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n)
  ι :=
    { app U := AddCommGrpCat.ofHom
        (X := ↥(CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U.unop.val)))
        (Y := CategoryTheory.Sheaf.H.{0} G n)
        (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U.unop.val)
          (fibre_mem_preimage i f y hfi U.unop.val U.unop.property) n)
      naturality U V r := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        exact cohomologyEvaluation_restrict i hi hfinite κ
          ((Opens.map f).map ((OpenNhds.inclusion y).map r.unop))
          (fibre_mem_preimage i f y hfi V.unop.val V.unop.property)
          (fibre_mem_preimage i f y hfi U.unop.val U.unop.property) n a }

/-- The colimit universal property gives the canonical cohomology-presheaf stalk map. -/
def presheafStalkEvaluation (n : ℕ) :
    TopCat.Presheaf.stalk (sourceCohomologyPresheaf (F := F) f n) y ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n) :=
  colimit.desc _ (evaluationCocone i hi hfinite κ f y hfi n)

/-- The stalk map on a neighborhood germ is the literal finite-closed Ext restriction. -/
theorem presheafStalkEvaluation_germ (n : ℕ) (U : Opens Y) (hy : y ∈ U) :
    TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy ≫
      presheafStalkEvaluation i hi hfinite κ f y hfi n =
        AddCommGrpCat.ofHom
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
            (fibre_mem_preimage i f y hfi U hy) n) :=
  colimit.ι_desc (evaluationCocone i hi hfinite κ f y hfi n) (op ⟨U, hy⟩)

/-- A normalization comparing the explicit source resolution presheaf `U ↦ Hⁿ(Γ(f⁻¹U, I))` with
the Ext-defined source cohomology presheaf `U ↦ Hⁿ(f⁻¹U, F)`. -/
abbrev ResolutionCohomologyNormalization (I : InjectiveResolution F) (n : ℕ) :=
  sourceResolutionPresheaf f I n ≅ sourceCohomologyPresheaf (F := F) f n

/-- Relative to a normalization `ρ`, the stalk of `Rⁿf_*F` at `y` is the stalk at `y` of the
cohomology presheaf `U ↦ Hⁿ(f⁻¹U, F)`, i.e. the filtered colimit `colim_{U ∋ y} Hⁿ(f⁻¹U, F)`
(Godement II.4.11, Hartshorne III.8.1). -/
def derivedStalkIso (I : InjectiveResolution F) (n : ℕ)
    (ρ : ResolutionCohomologyNormalization (F := F) f I n) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F n).obj y ≅
      TopCat.Presheaf.stalk (sourceCohomologyPresheaf (F := F) f n) y :=
  higherDirectImageResolutionStalkIso f F I n y ≪≫
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).mapIso ρ

/-- The evaluation map from the stalk `(Rⁿf_*F)_y` to `Hⁿ(T, G)`, relative to a normalization
`ρ`: the stalk comparison followed by the colimit evaluation. -/
def derivedStalkEvaluation (I : InjectiveResolution F) (n : ℕ)
    (ρ : ResolutionCohomologyNormalization (F := F) f I n) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F n).obj y ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n) :=
  (derivedStalkIso (F := F) f y I n ρ).hom ≫
    presheafStalkEvaluation i hi hfinite κ f y hfi n

/-- Relative to the displayed resolution normalization, an Ext-defined neighborhood class
determines a class in the literal derived stalk. -/
def derivedNeighborhoodGerm (I : InjectiveResolution F) (n : ℕ)
    (ρ : ResolutionCohomologyNormalization (F := F) f I n)
    (U : Opens Y) (hy : y ∈ U) :
    CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U) ⟶
      TopCat.Presheaf.stalk (higherDirectImageSheaf f F n).obj y :=
  TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy ≫
    (derivedStalkIso (F := F) f y I n ρ).inv

/-- On the germ of a neighborhood class, the derived stalk evaluation is the evaluation
`Hⁿ(f⁻¹U, F) → Hⁿ(T, G)` of that neighborhood. -/
theorem derivedStalkEvaluation_germ (I : InjectiveResolution F) (n : ℕ)
    (ρ : ResolutionCohomologyNormalization (F := F) f I n)
    (U : Opens Y) (hy : y ∈ U) :
    derivedNeighborhoodGerm (F := F) f y I n ρ U hy ≫
      derivedStalkEvaluation i hi hfinite κ f y hfi I n ρ =
        AddCommGrpCat.ofHom
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
            (fibre_mem_preimage i f y hfi U hy) n) := by
  rw [derivedNeighborhoodGerm, derivedStalkEvaluation, Category.assoc,
    (derivedStalkIso (F := F) f y I n ρ).inv_hom_id_assoc]
  exact presheafStalkEvaluation_germ i hi hfinite κ f y hfi n U hy

end Stalk

section LocalCriterion

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- The canonical cohomology-presheaf stalk evaluation is bijective under the standard local
lift-and-kill hypotheses. -/
theorem presheafStalkEvaluation_bijective_of_local_lift_kill (n : ℕ)
    (hlift : ∀ b : CategoryTheory.Sheaf.H.{0} G n,
      ∃ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)),
        cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a = b)
    (hkill : ∀ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)),
      cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a = 0 →
        ∃ (V : Opens Y) (hVU : V ≤ U) (_hyV : y ∈ V),
          (sourceCohomologyPresheaf (F := F) f n).map (homOfLE hVU).op a = 0) :
    Function.Bijective (presheafStalkEvaluation i hi hfinite κ f y hfi n) := by
  let e : ∀ (U : Opens Y), y ∈ U →
      ((sourceCohomologyPresheaf (F := F) f n).obj (op U) ⟶
        AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n)) :=
    fun U hy ↦ AddCommGrpCat.ofHom
      (X := (sourceCohomologyPresheaf (F := F) f n).obj (op U))
      (Y := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n))
      (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
        (fibre_mem_preimage i f y hfi U hy) n)
  apply stalkMap_bijective_of_local_lift_kill
    (sourceCohomologyPresheaf (F := F) f n) y
    (AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n))
    (presheafStalkEvaluation i hi hfinite κ f y hfi n) e
  · intro U hy
    dsimp [e]
    exact presheafStalkEvaluation_germ i hi hfinite κ f y hfi n U hy
  · exact hlift
  · exact hkill

/-- With an explicit resolution normalization, the same local hypotheses make the literal
higher-direct-image stalk evaluation an isomorphism. -/
theorem derivedStalkEvaluation_isIso_of_local_lift_kill
    (I : InjectiveResolution F) (n : ℕ)
    (ρ : ResolutionCohomologyNormalization (F := F) f I n)
    (hlift : ∀ b : CategoryTheory.Sheaf.H.{0} G n,
      ∃ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)),
        cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a = b)
    (hkill : ∀ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)),
      cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a = 0 →
        ∃ (V : Opens Y) (hVU : V ≤ U) (_hyV : y ∈ V),
          (sourceCohomologyPresheaf (F := F) f n).map (homOfLE hVU).op a = 0) :
    IsIso (derivedStalkEvaluation i hi hfinite κ f y hfi I n ρ) := by
  let m := presheafStalkEvaluation i hi hfinite κ f y hfi n
  have hm := presheafStalkEvaluation_bijective_of_local_lift_kill
    i hi hfinite κ f y hfi n hlift hkill
  let _ : IsIso m := (ConcreteCategory.isIso_iff_bijective m).mpr hm
  change IsIso ((derivedStalkIso (F := F) f y I n ρ).hom ≫ m)
  infer_instance

end LocalCriterion

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
