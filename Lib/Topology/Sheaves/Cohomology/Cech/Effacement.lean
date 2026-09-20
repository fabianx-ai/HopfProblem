/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.GodementEnvelope
public import Lib.Topology.Sheaves.Cohomology.Cech.FlasqueAcyclic
public import Lib.Topology.Sheaves.Cohomology.Cech.DeltaFunctor
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Effaceable

@[expose] public section

/-!
# Effacement of Cech cohomology by the Godement envelope

This file proves directly from fixed-cover flasque acyclicity that the Godement germ embedding
effaces positive-degree Cech cohomology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalSpace.OpenCover.SetOpenCover

universe u

variable {X : TopCat.{u}}

/-- For every abelian sheaf `F` on `X` and every degree `q > 0`, the refinement-colimit Čech
cohomology of the Godement envelope of `F` vanishes: the envelope is flasque, and for a flasque
sheaf the normalized Čech cohomology of every fixed cover vanishes in positive degrees. -/
theorem cechCohomology_isZero_godementEnvelope
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {q : ℕ} (hq : 0 < q) :
    IsZero
      (cechCohomology
        (TopCat.SheafCohomology.Godement.envelope F).presheaf q) :=
  (colimit.isColimit
      (normalizedCechCohomologyFunctor
        (TopCat.SheafCohomology.Godement.envelope F).presheaf q)).isZero_pt
    ((normalizedCechCohomologyFunctor
        (TopCat.SheafCohomology.Godement.envelope F).presheaf q).isZero_iff.mpr
      (fun U => normalizedCechCohomology_isZero_of_isFlasque
        (TopCat.SheafCohomology.Godement.envelope F) U hq))

/-- For every abelian sheaf `F` on `X` and every degree `q > 0`, the map induced on degree-`q`
Čech cohomology by the germ embedding `F ⟶ Godement.envelope F` is zero, because its target is
a zero object. -/
theorem cechCohomology_germEmbedding_eq_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {q : ℕ} (hq : 0 < q) :
    cechCohomologyCoefficientMap
      (TopCat.SheafCohomology.Godement.germEmbedding F).hom q = 0 :=
  (cechCohomology_isZero_godementEnvelope F hq).eq_of_tgt
    (cechCohomologyCoefficientMap
      (TopCat.SheafCohomology.Godement.germEmbedding F).hom q) 0

/-- On a paracompact Hausdorff space `X`, the Čech cohomological delta functor is effaceable in
every positive degree: every abelian sheaf `F` admits the monomorphism `germEmbedding` into its
Godement envelope, and that monomorphism induces the zero map in every positive degree. -/
theorem cechCohomologyDeltaFunctor_effaceable
    (X : TopCat.{u}) [ParacompactSpace X] [T2Space X] :
    (cechCohomologyDeltaFunctor X).Effaceable := by
  intro q hq F
  exact ⟨TopCat.SheafCohomology.Godement.envelope F,
    TopCat.SheafCohomology.Godement.germEmbedding F, inferInstance,
    cechCohomology_germEmbedding_eq_zero F hq⟩

end TopologicalSpace.OpenCover.SetOpenCover
