module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.RightDerived
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lib.Topology.Sheaves.ConstantSheaf.GlobalSections
public import Lib.CategoryTheory.Abelian.RightDerived
/-!
# Derived global sections on an arbitrary space

The textbook M00-D construction (1600–1607 before its comparison conclusion), with
D02 (41–60), specializes the derived delta functor to literal sections at the top open.
The space and abelian-group coefficients share an arbitrary ambient universe `u`;
no independently sized universe or lifting compatibility is asserted here.
The derived construction does not use the native Ext model as an input. The final
comparison identifies native Ext with these degree functors through evaluation on
the same resolution, with the fixed degree-zero normalization.
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

open CategoryTheory.Abelian
namespace TopCat.SheafCohomology
variable (X : TopCat.{u})

local instance : HasExt.{u}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u, u, u + 1} _
local instance : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op ⊤)).Additive)
local instance : PreservesFiniteLimits ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation _ _).obj (op ⊤)))

/-- Native Ext from the constant integer sheaf computes derived global sections.
On any original injective resolution, evaluation gives an isomorphism from the
Hom complex to the global-sections complex: naturality commutes with every
differential and comparison map. Taking cohomology after the native Ext comparison
therefore gives an additive, coefficient-natural isomorphism independent of the
resolution. Its inverse uses inverse evaluation and the inverse Ext comparison,
in reverse order (textbook M09, C29f). No boundary compatibility is asserted here. -/
def extFunctorObjIsoDerivedGlobalSections (q : ℕ) :
    extFunctorObj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) q ≅ ((derivedGlobalSectionsDeltaFunctor X).T q).obj :=
  extFunctorObjIsoRightDerived
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) q ≪≫
    NatIso.rightDerived
      (NatIso.ofComponents
        (fun A => (TopCat.ConstantSheaf.homGlobalSectionsAddEquiv X A).toAddCommGrpIso)
        (by intro A B f; ext h
            exact TopCat.ConstantSheaf.homGlobalSectionsAddEquiv_naturality X A h f) :
        preadditiveCoyoneda.obj (op
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) q

/-- The comparison is precisely the fixed native Ext/right-derived identification
followed by derived evaluation. This equation exposes both original-resolution
computations without changing the chosen comparison or identifying carriers by fiat. -/
theorem extFunctorObjIsoDerivedGlobalSections_eq (q : ℕ) :
    extFunctorObjIsoDerivedGlobalSections X q =
      extFunctorObjIsoRightDerived
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) q ≪≫
        NatIso.rightDerived
          (NatIso.ofComponents
            (fun A => (TopCat.ConstantSheaf.homGlobalSectionsAddEquiv X A).toAddCommGrpIso)
            (by intro A B f; ext h
                exact TopCat.ConstantSheaf.homGlobalSectionsAddEquiv_naturality X A h f) :
            preadditiveCoyoneda.obj (op
              ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
                (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
              (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) q := by
  unfold extFunctorObjIsoDerivedGlobalSections
  rfl

/-- Canonical degree zero after the comparison is the already-fixed Ext evaluation
normalization. On every original resolution the cocycle factors through the same
augmentation, and evaluation takes that factor at the sheafification-unit image
of 1. Thus the canonical-zero square uses the same kernel factorization and
generator, not a newly chosen normalization (textbook M09, final sentence). -/
theorem extFunctorObjIsoDerivedGlobalSections_zero :
    (extFunctorObjIsoDerivedGlobalSections X 0).hom ≫
      (derivedGlobalSectionsDegreeZeroIso X).hom =
        (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom := by
  have hΦ := congrArg Iso.hom (extFunctorObjIsoDerivedGlobalSections_eq X 0)
  rw [Iso.trans_hom] at hΦ
  change (extFunctorObjIsoDerivedGlobalSections X 0).hom ≫
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerivedZeroIsoSelf.hom = _
  rw [hΦ]
  erw [Category.assoc, NatIso.rightDerived_zero_hom, ← Category.assoc]
  have hG := congrArg Iso.hom (extFunctorObjZeroIsoCoyoneda_eq
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))))
  rw [Iso.trans_hom] at hG
  rw [← hG]
  ext A x
  exact (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections_hom_app X A x).symm

end TopCat.SheafCohomology
