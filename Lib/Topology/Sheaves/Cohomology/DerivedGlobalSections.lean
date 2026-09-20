module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.RightDerived
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lib.Topology.Sheaves.ConstantSheaf.GlobalSections
public import Lib.CategoryTheory.Abelian.RightDerived
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Ext
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

/-- The fixed native Ext comparison with derived global sections commutes with
the positive connecting maps of every original short exact coefficient sequence
(textbook M10, C29g). The same compatible resolution triple computes both
boundaries: a lift satisfies `j(a) = db`, and evaluation sends it to
`d α(b) = α(db) = α(j(a)) = j α(a)`. The native comparison followed by derived
evaluation therefore gives the ordinary commuting square, with no new sign. -/
theorem extFunctorObjIsoDerivedGlobalSections_hom_connecting
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) :
    extConnecting ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hS n ≫
      (extFunctorObjIsoDerivedGlobalSections X (n + 1)).hom.app S.X₁ =
    (extFunctorObjIsoDerivedGlobalSections X n).hom.app S.X₃ ≫
      (derivedGlobalSectionsDeltaFunctor X).δ hS n := by
  let P := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let L := preadditiveCoyoneda.obj (op P)
  let Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
  let α : L ≅ Γ := NatIso.ofComponents
    (fun A => (TopCat.ConstantSheaf.homGlobalSectionsAddEquiv X A).toAddCommGrpIso)
    (by intro A B f; ext h
        exact TopCat.ConstantSheaf.homGlobalSectionsAddEquiv_naturality X A h f)
  have fixedPhi (i : ℕ) :
      extFunctorObjIsoDerivedGlobalSections X i =
        extFunctorObjIsoRightDerived P i ≪≫ NatIso.rightDerived α i :=
    extFunctorObjIsoDerivedGlobalSections_eq X i
  have factors (i : ℕ) := congrArg Iso.hom (fixedPhi i)
  simp only [Iso.trans_hom] at factors
  have native :
      extConnecting P hS n ≫ (extFunctorObjIsoRightDerived P (n+1)).hom.app S.X₁ =
        (extFunctorObjIsoRightDerived P n).hom.app S.X₃ ≫ L.rightDerivedConnecting hS n := by
    dsimp only [L]
    rw [extConnecting_eq_rightDerived]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have derived := NatIso.rightDerived_hom_connecting α hS n
  rw [factors (n+1), factors n, NatTrans.comp_app, NatTrans.comp_app,
    derivedGlobalSectionsBoundary]
  change extConnecting P hS n ≫
      ((extFunctorObjIsoRightDerived P (n+1)).hom.app S.X₁ ≫
        (NatIso.rightDerived α (n+1)).hom.app S.X₁) =
    ((extFunctorObjIsoRightDerived P n).hom.app S.X₃ ≫
      (NatIso.rightDerived α n).hom.app S.X₃) ≫ Γ.rightDerivedConnecting hS n
  rw [← Category.assoc, native, Category.assoc, derived, ← Category.assoc]

/-- The inverse of the same fixed Ext/global-sections comparison also commutes
with positive connecting maps (textbook M10, inverse C29g). Inverse evaluation
and the inverse native comparison act in reverse order on the same original
resolution triple. Their lift calculation still uses `j(a) = db`; hence this
is the inverse ordinary-sign square, not a separately chosen comparison. -/
theorem extFunctorObjIsoDerivedGlobalSections_inv_connecting
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) :
    (derivedGlobalSectionsDeltaFunctor X).δ hS n ≫
      (extFunctorObjIsoDerivedGlobalSections X (n + 1)).inv.app S.X₁ =
    (extFunctorObjIsoDerivedGlobalSections X n).inv.app S.X₃ ≫
      extConnecting ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hS n := by
  let P := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let L := preadditiveCoyoneda.obj (op P)
  let Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
  let α : L ≅ Γ := NatIso.ofComponents
    (fun A => (TopCat.ConstantSheaf.homGlobalSectionsAddEquiv X A).toAddCommGrpIso)
    (by intro A B f; ext h
        exact TopCat.ConstantSheaf.homGlobalSectionsAddEquiv_naturality X A h f)
  have fixedPhi (i : ℕ) :
      extFunctorObjIsoDerivedGlobalSections X i =
        extFunctorObjIsoRightDerived P i ≪≫ NatIso.rightDerived α i :=
    extFunctorObjIsoDerivedGlobalSections_eq X i
  have factors (i : ℕ) := congrArg Iso.inv (fixedPhi i)
  simp only [Iso.trans_inv] at factors
  have native :
      L.rightDerivedConnecting hS n ≫ (extFunctorObjIsoRightDerived P (n+1)).inv.app S.X₁ =
        (extFunctorObjIsoRightDerived P n).inv.app S.X₃ ≫ extConnecting P hS n := by
    dsimp only [L]
    rw [extConnecting_eq_rightDerived]
    simp only [Iso.inv_hom_id_app_assoc]
  have derived := NatIso.rightDerived_inv_connecting α hS n
  rw [factors (n+1), factors n, NatTrans.comp_app, NatTrans.comp_app,
    derivedGlobalSectionsBoundary]
  change Γ.rightDerivedConnecting hS n ≫
      ((NatIso.rightDerived α (n+1)).inv.app S.X₁ ≫
        (extFunctorObjIsoRightDerived P (n+1)).inv.app S.X₁) =
    ((NatIso.rightDerived α n).inv.app S.X₃ ≫
      (extFunctorObjIsoRightDerived P n).inv.app S.X₃) ≫ extConnecting P hS n
  rw [← Category.assoc, derived, Category.assoc, native, ← Category.assoc]

/-- The fixed native Ext comparison is a morphism to the derived global-sections
delta functor (textbook M10, C29g and its assembly). Its degree maps are the
already constructed comparison, and its commutation field uses the positive
boundary square for every original coefficient short exact sequence. -/
def extDerivedGlobalSectionsHom : CohomologicalDeltaFunctor.Hom
    (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) (derivedGlobalSectionsDeltaFunctor X) where
  app q := (extFunctorObjIsoDerivedGlobalSections X q).hom
  comm h q := extFunctorObjIsoDerivedGlobalSections_hom_connecting X h q

/-- The inverse fixed comparison is a delta morphism in the reverse direction
(textbook M10). The same inverse degree maps and inverse positive boundary
squares are used; no alternative comparison or degreewise sign is chosen. -/
def extDerivedGlobalSectionsInv : CohomologicalDeltaFunctor.Hom
    (derivedGlobalSectionsDeltaFunctor X)
    (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) where
  app q := (extFunctorObjIsoDerivedGlobalSections X q).inv
  comm h q := extFunctorObjIsoDerivedGlobalSections_inv_connecting X h q

/-- Every whole degree natural transformation of the forward delta morphism is
the fixed native Ext/global-sections comparison (textbook M10 assembly). -/
theorem extDerivedGlobalSectionsHom_app (n : ℕ) :
    (extDerivedGlobalSectionsHom X).app n =
      (extFunctorObjIsoDerivedGlobalSections X n).hom := by
  unfold extDerivedGlobalSectionsHom
  rfl

/-- Every whole degree natural transformation of the reverse delta morphism is
the inverse of the same fixed comparison (textbook M10 assembly). -/
theorem extDerivedGlobalSectionsInv_app (n : ℕ) :
    (extDerivedGlobalSectionsInv X).app n =
      (extFunctorObjIsoDerivedGlobalSections X n).inv := by
  unfold extDerivedGlobalSectionsInv
  rfl

/-- Forward comparison followed by inverse comparison is the identity on the
native Ext delta functor, as a whole delta morphism (textbook M10). -/
theorem extDerivedGlobalSectionsHom_comp_inv :
    CohomologicalDeltaFunctor.Hom.comp (extDerivedGlobalSectionsHom X) (extDerivedGlobalSectionsInv X) =
      CohomologicalDeltaFunctor.Hom.id (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) := by
  apply CohomologicalDeltaFunctor.Hom.ext
  intro q
  rw [CohomologicalDeltaFunctor.Hom.comp_app, CohomologicalDeltaFunctor.Hom.id_app, extDerivedGlobalSectionsHom_app,
    extDerivedGlobalSectionsInv_app]
  exact (extFunctorObjIsoDerivedGlobalSections X q).hom_inv_id

/-- Inverse comparison followed by forward comparison is the identity on actual
derived global sections, as a whole delta morphism (textbook M10). -/
theorem extDerivedGlobalSectionsInv_comp_hom :
    CohomologicalDeltaFunctor.Hom.comp (extDerivedGlobalSectionsInv X) (extDerivedGlobalSectionsHom X) =
      CohomologicalDeltaFunctor.Hom.id (derivedGlobalSectionsDeltaFunctor X) := by
  apply CohomologicalDeltaFunctor.Hom.ext
  intro q
  rw [CohomologicalDeltaFunctor.Hom.comp_app, CohomologicalDeltaFunctor.Hom.id_app, extDerivedGlobalSectionsInv_app,
    extDerivedGlobalSectionsHom_app]
  exact (extFunctorObjIsoDerivedGlobalSections X q).inv_hom_id

/-- The forward delta morphism has the fixed degree-zero component: native
evaluation followed by the inverse canonical derived normalization. This is
the textbook `κ⁻¹ ε`, with the same evaluation and normalization as in M09. -/
theorem extDerivedGlobalSectionsHom_app_zero :
    (extDerivedGlobalSectionsHom X).app 0 =
      (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv := by
  rw [extDerivedGlobalSectionsHom_app]
  apply (cancel_mono (derivedGlobalSectionsDegreeZeroIso X).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    extFunctorObjIsoDerivedGlobalSections_zero X

/-- Any other native Ext to derived-global-sections delta morphism with the same
degree-zero normalization equals the constructed comparison (textbook M10,
final canonicity statement). Universality of the Ext SOURCE verifies uniqueness
after construction; it neither defines the comparison nor replaces its boundary
calculation. -/
theorem extDerivedGlobalSectionsHom_unique
    (η : CohomologicalDeltaFunctor.Hom (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) (derivedGlobalSectionsDeltaFunctor X))
    (hη : η.app 0 =
      (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv) :
    η = extDerivedGlobalSectionsHom X :=
  (ofExt_isUniversal
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).hom_ext
    (hη.trans (extDerivedGlobalSectionsHom_app_zero X).symm)

end TopCat.SheafCohomology
