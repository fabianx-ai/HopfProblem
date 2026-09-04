/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive
public import Lib.Topology.Sheaves.OpenRestriction.NearbyEvaluationCompatibility

/-!
# Cofinal extensionality for positive-degree derived neighborhood germs

The canonical Ext-defined neighborhood germs jointly generate the actual higher-direct-image
stalk.  It is enough to test maps out of that stalk on a cofinal family of neighborhoods.  This
is the formal reduction needed to replace a global special-to-nearby square by a coordinate-disc
identity.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre

variable {X Y : TopCat.{0}} [T2Space X] [T1Space Y]
  (f : X ⟶ Y) (y : Y) (A : AddCommGrpCat.{0})
  (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)

omit [T2Space X] [T1Space Y] in
/-- Two maps out of an actual positive-degree higher-direct-image stalk agree if their
composites with the canonical Ext neighborhood germs agree after one sufficiently small
shrinking of every neighborhood. -/
theorem canonicalNeighborhoodGermPositive_hom_ext_of_cofinal
    {B : AddCommGrpCat.{0}}
    {u v : TopCat.Presheaf.stalk
        (higherDirectImageSheaf f (TopCat.ConstantSheaf.sheaf X A) (n + 1)).obj y ⟶ B}
    (hlocal : ∀ (U : Opens Y) (_hyU : y ∈ U),
      ∃ (V : Opens Y) (_hVU : V ≤ U) (hyV : y ∈ V),
        canonicalNeighborhoodGermPositive f y A I n V hyV ≫ u =
          canonicalNeighborhoodGermPositive f y A I n V hyV ≫ v) :
    u = v := by
  let e := canonicalDerivedStalkIsoPositive f y I n
  apply (cancel_epi e.inv).mp
  apply (sourceCohomologyPresheaf
    (F := TopCat.ConstantSheaf.sheaf X A) f (n + 1)).stalk_hom_ext_of_cofinal
  intro U hyU
  obtain ⟨V, hVU, hyV, hV⟩ := hlocal U hyU
  refine ⟨V, hVU, hyV, ?_⟩
  simpa only [canonicalNeighborhoodGermPositive, neighborhoodGerm,
    derivedNeighborhoodGerm, canonicalDerivedStalkIsoPositive, e,
    Category.assoc] using hV

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre
