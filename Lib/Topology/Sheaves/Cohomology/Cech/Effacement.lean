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

/-- Textbook source: “Effacement by the Godement germ sheaf,” the sentence preceding (C28)
and equation (C28). The positive-degree Čech cohomology of the Godement envelope vanishes. -/
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

/-- Textbook source: “Effacement by the Godement germ sheaf,” the sentence after (C28).
The germ embedding induces the zero map on positive-degree Čech cohomology. -/
theorem cechCohomology_germEmbedding_eq_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {q : ℕ} (hq : 0 < q) :
    cechCohomologyCoefficientMap
      (TopCat.SheafCohomology.Godement.germEmbedding F).hom q = 0 :=
  (cechCohomology_isZero_godementEnvelope F hq).eq_of_tgt
    (cechCohomologyCoefficientMap
      (TopCat.SheafCohomology.Godement.germEmbedding F).hom q) 0

/-- Textbook source: “Effacement by the Godement germ sheaf,” final two sentences following
(C28). The Čech cohomological delta functor is effaceable in every positive degree. -/
theorem cechCohomologyDeltaFunctor_effaceable
    (X : TopCat.{u}) [ParacompactSpace X] [T2Space X] :
    (cechCohomologyDeltaFunctor X).Effaceable := by
  intro q hq F
  exact ⟨TopCat.SheafCohomology.Godement.envelope F,
    TopCat.SheafCohomology.Godement.germEmbedding F, inferInstance,
    cechCohomology_germEmbedding_eq_zero F hq⟩

end TopologicalSpace.OpenCover.SetOpenCover
