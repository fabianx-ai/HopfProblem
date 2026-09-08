module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.RightDerived
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
/-!
# Derived global sections on an arbitrary space

The textbook M00-D construction (1600–1607 before its comparison conclusion), with
D02 (41–60), specializes the derived delta functor to literal sections at the top open.
The space and abelian-group coefficients share an arbitrary ambient universe `u`;
no independently sized universe or lifting compatibility is asserted here.
This is derived global sections, not the native Ext-defined sheaf cohomology model:
identifying those models is a separate later comparison, not an input here.
-/

public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.CohomologicalDeltaFunctor
namespace TopCat.SheafCohomology
variable (X : TopCat.{u})

local instance : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op ⊤)).Additive)
local instance : PreservesFiniteLimits ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op ⊤)))

/-- The derived delta functor of literal global sections, for arbitrary sheaf coefficients
on an arbitrary space (M00-D, textbook 1600–1607). -/
@[expose] def derivedGlobalSectionsDeltaFunctor : CohomologicalDeltaFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) AddCommGrpCat.{u} :=
  ofRightDerived ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤))
/-- Each degree is the same fixed right-derived global-sections functor of D02. -/
theorem derivedGlobalSectionsDegree (n : ℕ) :
    ((derivedGlobalSectionsDeltaFunctor X).T n).obj = ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived n := rfl
/-- The boundary is the positive, choice-independent derived connecting morphism;
no new resolution family or sign convention is introduced by specialization. -/
theorem derivedGlobalSectionsBoundary {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact) (n : ℕ) :
    (derivedGlobalSectionsDeltaFunctor X).δ hS n = ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerivedConnecting hS n := rfl
/-- Canonical degree-zero normalization to literal global sections, from left exactness.
This is the derived normalization, not an Ext-model degree-zero equivalence. -/
@[expose] def derivedGlobalSectionsDegreeZeroIso :
    ((derivedGlobalSectionsDeltaFunctor X).T 0).obj ≅ ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) :=
  ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerivedZeroIsoSelf
/-- Positive degrees are effaceable by embedding a sheaf into an injective sheaf,
using the generic injective vanishing argument (M00-D, textbook 1606–1607). -/
theorem derivedGlobalSectionsEffaceable : (derivedGlobalSectionsDeltaFunctor X).Effaceable :=
  ofRightDerived_effaceable ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤))
/-- Derived global sections is universal as a source delta functor: positive effacement
supplies the unique extension of prescribed degree-zero data (M00-D). -/
theorem derivedGlobalSectionsIsUniversal : (derivedGlobalSectionsDeltaFunctor X).IsUniversal :=
  ofRightDerived_isUniversal ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤))

end TopCat.SheafCohomology
