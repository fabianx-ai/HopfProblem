module
public import Lib.Topology.Sheaves.Cohomology.Cech.CoveringDimensionVanishing
public import Lib.Topology.Sheaves.Cohomology.Cech.DerivedGlobalSections

/-!
# Covering dimension bounds derived sheaf cohomology

On a paracompact Hausdorff space of covering dimension at most n, the right-derived
functors of literal global sections vanish in every degree a > n, for every sheaf
of abelian groups. This is the covering-dimension theorem (5) of textbook CD07.

The earlier Čech vanishing theorem supplies the full refinement argument: choose
an order on a cover's indices and use the normalized alternating cochain product
over increasing (a+1)-tuples, with alternating restriction differential. Empty
intersections contribute zero sections. Low-multiplicity set-valued refinements
are cofinal in the thin refinement preorder. A class represented on a cover
therefore becomes zero on such a refinement when a > n, since all relevant
intersections are empty. Eventual equality in the direct limit makes the original
Čech class zero. Those cochain, refinement and colimit results are reused here.

The only remaining step transports that zero object through the original natural
Čech-to-derived comparison at the given coefficient sheaf. Dimension supplies
low-multiplicity refinements and Čech vanishing; paracompactness and Hausdorffness
supply the comparison. Neither role replaces the other. The target is the actual
right-derived functor of sections at the top open, not a substituted cohomology
carrier. The space and arbitrary abelian coefficients share an ambient universe.
-/

public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopologicalSpace.OpenCover.SetOpenCover
open TopCat.SheafCohomology
variable {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
local instance : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op ⊤)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op ⊤)).Additive)

namespace TopCat.SheafCohomology

/-- Above the covering dimension, every abelian sheaf has zero derived global
sections. The dimension bound gives Čech vanishing; the original paracompact
Hausdorff comparison transports it to the literal right-derived functor. -/
theorem derivedGlobalSections_isZero_of_coveringDimensionLE
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    {n a : ℕ} (hX : HasCoveringDimensionLE X n)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ha : n < a) :
    IsZero ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived a).obj F) := by
  have cechZero :
      IsZero (cechCohomology (A := AddCommGrpCat.{u}) F.presheaf a) :=
    cechCohomology_isZero_of_coveringDimensionLE.{u,u} hX F ha
  have sourceZero : IsZero (((cechCohomologyDeltaFunctor X).T a).obj.obj F) :=
    cechZero
  let comparison :
      ((cechCohomologyDeltaFunctor X).T a).obj.obj F ≅
        ((derivedGlobalSectionsDeltaFunctor X).T a).obj.obj F :=
    (cechCohomologyIsoDerivedGlobalSections X a).app F
  have transported : IsZero (((derivedGlobalSectionsDeltaFunctor X).T a).obj.obj F) :=
    sourceZero.of_iso comparison.symm
  simpa only [derivedGlobalSectionsDegree] using transported

/-- Equivalently, the group of derived global sections has only one element above
the covering dimension, for arbitrary abelian coefficients on a paracompact
Hausdorff space. This is the carrier form of the same zero-object statement. -/
theorem derivedGlobalSections_subsingleton_of_coveringDimensionLE
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    {n a : ℕ} (hX : HasCoveringDimensionLE X n)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ha : n < a) :
    Subsingleton ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived a).obj F) :=
  AddCommGrpCat.subsingleton_of_isZero
    (derivedGlobalSections_isZero_of_coveringDimensionLE hX F ha)

end TopCat.SheafCohomology
