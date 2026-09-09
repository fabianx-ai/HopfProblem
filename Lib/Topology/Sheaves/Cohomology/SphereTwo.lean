module
public import Lib.Topology.Dimension.SphereTwo
public import Lib.Topology.Sheaves.Cohomology.CoveringDimension

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
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.SheafCohomology

variable {B : TopCat.{0}}
local instance : ((sheafSections (Opens.grothendieckTopology B) AddCommGrpCat.{0}).obj
    (op ⊤)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology B) AddCommGrpCat.{0} ⋙
    (evaluation _ _).obj (op ⊤)).Additive)

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

end TopCat.Sheaf
