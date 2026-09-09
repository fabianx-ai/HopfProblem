module
public import Lib.Topology.Dimension.SphereTwo
public import Lib.Topology.Sheaves.Cohomology.CoveringDimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Arbitrary-coefficient cohomology vanishing on a two-sphere

For any space homeomorphic to the standard two-sphere, every abelian sheaf has
vanishing derived global sections in every degree at least three (Corollary 6.5,
equation (9)). The same given homeomorphism supplies the covering-dimension bound
two and transports the sphere's paracompact Hausdorff properties. The sphere is
compact in its proper finite-dimensional real ambient space; compactness gives
paracompactness, while its inherited metric topology gives Hausdorffness.

Apply the covering-dimension theorem with n = 2, since a ≥ 3 implies a > 2.
No constancy, constructibility, rank, freeness, finite-generation or torsion
condition is imposed on the coefficient sheaf. This formal application uses
Type0 spaces and native abelian-group coefficients in the same universe; its
target is the right-derived functor of literal sections at the top open.
-/

public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open TopCat.SheafCohomology

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

end TopCat.Sheaf
