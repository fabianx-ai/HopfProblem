/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.Colimit
public import Lib.Topology.Sheaves.Cohomology.Cech.MultiplicityVanishing
public import Lib.Topology.Sheaves.Cohomology.Cech.RangeCover

/-!
# Direct-limit Cech vanishing from covering dimension

This file implements the Cech-colimit half of textbook section CD-07. If a space has covering
dimension at most `n`, every representative of a direct-limit Cech class can be refined to a
set-valued cover of multiplicity at most `n + 1`. In every degree `a > n`, CD-06 makes the
fixed-cover class zero there, so the original class is zero in the refinement-directed colimit.

The result applies to every sheaf of abelian groups. No separation, compactness,
paracompactness, or comparison with derived sheaf cohomology is used here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}

/-- If `X` has covering dimension at most `n`, its direct-limit normalized Cech cohomology with
coefficients in any abelian sheaf is subsingleton in every degree `a > n`. -/
theorem cechCohomology_subsingleton_of_coveringDimensionLE
    {n a : ℕ} (hX : HasCoveringDimensionLE X n)
    (F : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (ha : n < a) :
    Subsingleton
      (cechCohomology (A := AddCommGrpCat.{max u v}) F.presheaf a) := by
  -- Restrict the standard filtered-colimit preservation instance to the cover universe.
  let _ : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, u, u}
      (forget AddCommGrpCat.{max u v})
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨U, y, rfl⟩ := cechCohomology_exists_rep F.presheaf a x
  obtain ⟨V, hUV, hV⟩ := hX.exists_multiplicityLE_refinement U
  apply toCechCohomology_apply_eq_zero_of_refinement F.presheaf a hUV y
  let _ : Subsingleton
      (normalizedCechCohomology (A := AddCommGrpCat.{max u v}) F.presheaf V a) :=
    normalizedCechCohomology_subsingleton_of_multiplicityLE F V hV ha
  exact Subsingleton.elim _ _

/-- If `X` has covering dimension at most `n`, its direct-limit normalized Cech cohomology with
coefficients in any abelian sheaf is a zero object in every degree `a > n`. -/
theorem cechCohomology_isZero_of_coveringDimensionLE
    {n a : ℕ} (hX : HasCoveringDimensionLE X n)
    (F : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (ha : n < a) :
    IsZero (cechCohomology (A := AddCommGrpCat.{max u v}) F.presheaf a) := by
  exact @AddCommGrpCat.isZero_of_subsingleton _
    (cechCohomology_subsingleton_of_coveringDimensionLE hX F ha)

end TopologicalSpace.OpenCover.SetOpenCover
