/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module
public import Lib.Topology.Dimension.SphereTwo
public import Lib.Topology.Sheaves.Cohomology.CoveringDimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Lib.CategoryTheory.Sites.Leray.ResolutionTransgression

/-!
# Two-sphere specialisation of the covering-dimension vanishing theorem

Proof-specific application file.  The textbook result behind everything here is
Godement, *Topologie algébrique et théorie des faisceaux*, II.5.12: on a
paracompact Hausdorff space of Lebesgue covering dimension at most `n`, the
right-derived global-sections functor kills every abelian sheaf in degrees
above `n`.  That general theorem is the library declaration
`TopCat.SheafCohomology.derivedGlobalSections_isZero_of_coveringDimensionLE`
in `Lib/Topology/Sheaves/Cohomology/CoveringDimension.lean`; the dimension
input for the two-sphere is
`TopologicalSpace.SphereTwo.hasCoveringDimensionLE_two_of_homeomorph` in
`Lib/Topology/Dimension/SphereTwo.lean`.

This module adds no mathematics to those two.  It only instantiates them at
`n = 2` for a space presented by a homeomorphism to the standard two-sphere,
and then rephrases the instance in the three shapes the project's manuscript
asks for (Corollary 6.5, equations (9), (14), (11) and (10)): vanishing for an
arbitrary coefficient sheaf in degrees at least three, the equivalent
projective-dimension bound for the constant integer sheaf, and the substitution
of a higher direct image into the coefficient slot.  Singling out the
two-sphere, fixing `TopCat.{0}` and `AddCommGrpCat.{0}`, and naming the
manuscript's equations are exactly why this is not library material: it lives
under `Hopf/Proof/` and the general statements stay in `Lib/`.

The same homeomorphism supplies all hypotheses.  The sphere is compact in its
finite-dimensional real ambient space, so it is paracompact, and its metric
topology is Hausdorff; both transport along the homeomorphism.  No constancy,
constructibility, rank, freeness, finite-generation or torsion condition is
imposed on the coefficient sheaf.
-/

public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open TopCat.SheafCohomology
open CategoryTheory.Sheaf.Leray

variable {B : TopCat.{0}}
local instance : ((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
    (op ⊤)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology B) AddCommGrpCat.{0} ⋙
    (evaluation _ _).obj (op ⊤)).Additive)
local instance : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{0}) :=
  hasExt_of_enoughInjectives.{0,0,1} _

namespace TopCat.Sheaf

/-- Every abelian sheaf on a space supplied with a homeomorphism to the standard
two-sphere has zero derived global sections in degrees at least three. Both the
dimension bound and the paracompact Hausdorff hypotheses are obtained from the
same homeomorphism; no additional coefficient hypothesis is required. -/
theorem derivedGlobalSections_isZero_of_homeomorph_sphereTwo
    {B : TopCat.{0}}
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (F : TopCat.Sheaf AddCommGrpCat.{0} B)
    {a : ℕ} (ha : 3 ≤ a) :
    IsZero ((((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
      (op ⊤)).rightDerived a).obj F) := by
  let : ProperSpace (EuclideanSpace ℝ (Fin 3)) :=
    FiniteDimensional.proper_real (EuclideanSpace ℝ (Fin 3))
  let : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Metric.sphere.compactSpace (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : ParacompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    paracompact_of_compact
  let : T2Space (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := inferInstance
  let : ParacompactSpace B := (Homeomorph.paracompactSpace_iff g).mpr inferInstance
  let : T2Space B := g.symm.t2Space
  have dimension : HasCoveringDimensionLE B 2 :=
    TopologicalSpace.SphereTwo.hasCoveringDimensionLE_two_of_homeomorph g
  have degree : 2 < a := lt_of_lt_of_le (by decide : 2 < 3) ha
  exact TopCat.SheafCohomology.derivedGlobalSections_isZero_of_coveringDimensionLE
    dimension F degree

/-- The constant integer sheaf on a space homeomorphic to the standard two-sphere
has projective dimension strictly less than three, in the Ext-vanishing sense
of Corollary 6.5, equation (14). For every coefficient sheaf and degree at least
three, the fixed Ext/global-sections comparison identifies Ext with the zero
derived-global-sections object. Its underlying group is therefore subsingleton,
which is precisely the native projective-dimension bound.

Derived-global-sections vanishing is the primary statement; this bound is its
categorical reformulation. The first variable remains the constant integer
sheaf: this does not bound injective dimensions for arbitrary first variables.
It asserts neither enough projectives nor a length-two projective resolution.

The uniform arbitrary-sheaf cutoff is stronger than the application's pair of
degree-three and degree-four vanishings in equation (10). Constant coefficients
alone would not suffice for a possibly nonconstant higher direct-image sheaf.
Constructibility may matter for calculations in degrees zero, one and two,
but no local acyclicity, local-system, finiteness, torsion-freeness or
stratification hypothesis enters this high-degree cutoff. The supplied
homeomorphism verifies paracompactness, Hausdorffness and Lebesgue covering
dimension at most two. The upstream textbook inputs are injective resolutions,
the arbitrary-sheaf Čech comparison on paracompact Hausdorff spaces, Lebesgue
numbers, shrinking barycentric subdivisions and the standard sphere
triangulation. No further geometric or constructibility calculation is needed
for the application's pair. -/
theorem hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
    {B : TopCat.{0}}
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    HasProjectiveDimensionLT
      ((constantSheaf (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0} ℤ))) 3 := by
  apply HasProjectiveDimensionLT.mk
  intro a ha F e
  let P := (constantSheaf (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))
  let Γ := (sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj (op ⊤)
  let Φ := extFunctorObjIsoDerivedGlobalSections B a
  let component : AddCommGrpCat.of (Ext.{0} P F a) ≅ (Γ.rightDerived a).obj F :=
    Φ.app F
  have actualD : IsZero ((Γ.rightDerived a).obj F) :=
    derivedGlobalSections_isZero_of_homeomorph_sphereTwo g F ha
  have actualExt : IsZero (AddCommGrpCat.of (Ext.{0} P F a)) :=
    actualD.of_iso component
  have nativeSmall : Subsingleton (Ext.{0} P F a) :=
    AddCommGrpCat.subsingleton_of_isZero actualExt
  exact nativeSmall.elim e 0

/-- Higher direct images are abelian sheaves, so the sphere's uniform vanishing
applies to every `R^b f_* F` in every degree `a > 2`. This is the coefficient
substitution of Corollary 6.5, equation (11), also for arbitrary source sheaves.
For the integral sheaf it says that the displayed Leray terms
`H^a(B, R^b f_* ℤ)` have no columns above two. Here those terms are literal
derived global sections; no spectral-sequence construction or identification
with a different cohomology carrier is asserted. -/
theorem higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
    {Y B : TopCat.{0}}
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (f : Y ⟶ B) (F : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (b : ℕ) {a : ℕ} (ha : 2 < a) :
    IsZero ((((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
      (op ⊤)).rightDerived a).obj (higherDirectImageSheaf f F b)) :=
  TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
    g (higherDirectImageSheaf f F b) (Nat.succ_le_of_lt ha)

/-- The degree-three and degree-four vanishings for the first higher direct
image of the constant integer sheaf, Corollary 6.5, equation (10). Substitute
the same integral sheaf and `b = 1` into the uniform result, first at three and
then at four. This pair is the particular high-degree input required by the
application; the all-degree, arbitrary-coefficient statement is stronger. No
constancy or constructibility assumption on the higher direct image is needed. -/
theorem higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo
    {Y B : TopCat.{0}}
    (g : B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (f : Y ⟶ B) :
    IsZero ((((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
      (op ⊤)).rightDerived 3).obj (higherDirectImageSheaf f (TopCat.ConstantSheaf.integralSheaf Y) 1)) ∧
    IsZero ((((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
      (op ⊤)).rightDerived 4).obj (higherDirectImageSheaf f (TopCat.ConstantSheaf.integralSheaf Y) 1)) :=
  ⟨higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
      g f (TopCat.ConstantSheaf.integralSheaf Y) 1 (by decide),
    higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
      g f (TopCat.ConstantSheaf.integralSheaf Y) 1 (by decide)⟩

end TopCat.Sheaf
