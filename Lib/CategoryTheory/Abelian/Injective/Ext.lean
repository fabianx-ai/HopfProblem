module
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Lib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Lib.CategoryTheory.Abelian.RightDerived.Connecting
public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CochainComplex HomComplex
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-!
# Ext computed by an injective resolution

For a fixed object P of an abelian category with enough injectives, native derived-category
Ext is computed by the cohomology of the nonnegative complex Hom(P,I). The identification
is natural in the coefficient and independent of the chosen resolution.

`Ext^n(P, -)` is the `n`-th right derived functor of `Hom(P, -)`, computed by an injective
resolution of the second variable: Weibel, *An Introduction to Homological Algebra*,
§2.5 and §2.7; Hartshorne, *Algebraic Geometry* III.1.1A and Exercise III.6.4.
-/

section Representations
variable (P A : C) (I : InjectiveResolution A)

-- Representation-only single-source Hom-complex constructor.
private def singleHomComplexIso : HomComplex ((singleFunctor C 0).obj P) I.cochainComplex ≅
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := P) (K := I.cochainComplex)
      (zero_add n)).toAddCommGrpIso) ?_
  intro i j hij
  ext x
  obtain ⟨f, rfl⟩ := (Cochain.fromSingleEquiv (X := P) (K := I.cochainComplex)
    (zero_add i)).symm.surjective x
  change (Cochain.fromSingleEquiv (zero_add i)) (Cochain.fromSingleMk f (zero_add i)) ≫
      I.cochainComplex.d i j =
    (Cochain.fromSingleEquiv (zero_add j)) (δ i j (Cochain.fromSingleMk f (zero_add i)))
  rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]

-- Representation-only commutation of Hom with extension by zero.
set_option backward.isDefEq.respectTransparency false in
private def homMapExtendIso : ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ≅
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
      ComplexShape.embeddingUpNat := by
  let F := preadditiveCoyoneda.obj (op P)
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let eX : ∀ o : Option ℕ, F.obj (HomologicalComplex.extend.X I.cocomplex o) ≅
      HomologicalComplex.extend.X K o
    | some n => Iso.refl _
    | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero AddCommGrpCat)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => eX (ComplexShape.embeddingUpNat.r n)) ?_
  intro i j hij
  change (eX (ComplexShape.embeddingUpNat.r i)).hom ≫
    HomologicalComplex.extend.d K (ComplexShape.embeddingUpNat.r i) (ComplexShape.embeddingUpNat.r j) =
    F.map (HomologicalComplex.extend.d I.cocomplex (ComplexShape.embeddingUpNat.r i)
      (ComplexShape.embeddingUpNat.r j)) ≫ (eX (ComplexShape.embeddingUpNat.r j)).hom
  cases hi : ComplexShape.embeddingUpNat.r i <;> cases hj : ComplexShape.embeddingUpNat.r j <;>
    simp [eX, HomologicalComplex.extend.d, HomologicalComplex.extend.X, K]

end Representations

set_option backward.isDefEq.respectTransparency false in
/-- Native Ext in every nonnegative degree is the homology of the actual fixed-source
Hom complex of any injective resolution (textbook lines 1634–1639). -/
noncomputable def extHomologyIso (P : C) {A : C} (I : InjectiveResolution A) (q : ℕ) : AddCommGrpCat.of (Ext.{v} P A q) ≅
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q :=
  I.extAddEquivCohomologyClass.toAddCommGrpIso ≪≫
    ((leftHomologyData ((singleFunctor C 0).obj P) I.cochainComplex (q : ℤ)).homologyIso).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (q : ℤ)).mapIso
      (singleHomComplexIso P A I) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (q : ℤ)).mapIso
      (homMapExtendIso P A I) ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat rfl

set_option backward.isDefEq.respectTransparency false in
/-- The resolution comparison sends an Ext cocycle to its actual Hom-complex homology
class, including degree zero (textbook lines 1634–1639). -/
theorem extHomologyIso_hom_extMk (P : C) {A : C} (I : InjectiveResolution A) (q : ℕ)
    (f : P ⟶ I.cocomplex.X q) (hf : f ≫ I.cocomplex.d q (q + 1) = 0) :
    (extHomologyIso P I q).hom (I.extMk f (q + 1) rfl hf) =
      let K := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      K.homologyπ q ((K.sc q).abCyclesIso.inv ⟨f, by
        change f ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
        rw [CochainComplex.next]
        exact hf⟩) := by
  let K := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let H := leftHomologyData ((singleFunctor C 0).obj P) I.cochainComplex (q : ℤ)
  let c : Cocycle ((singleFunctor C 0).obj P) I.cochainComplex (q : ℤ) :=
    Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso q q rfl).inv) (zero_add _)
      ((q+1 : ℕ) : ℤ) (by lia) (by
        rw [I.cochainComplex_d (q : ℤ) ((q+1 : ℕ) : ℤ) q (q+1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])
  have hc : I.extEquivCohomologyClass (I.extMk f (q+1) rfl hf) = CohomologyClass.mk c := by
    exact I.extEquivCohomologyClass_extMk f (q+1) rfl hf
  change (H.homologyIso.inv ≫
    HomologicalComplex.homologyMap (singleHomComplexIso P A I).hom (q : ℤ) ≫
    HomologicalComplex.homologyMap (homMapExtendIso P A I).hom (q : ℤ) ≫
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).hom)
      (I.extEquivCohomologyClass (I.extMk f (q+1) rfl hf)) = _
  rw [hc]
  change (H.π ≫ H.homologyIso.inv ≫
    HomologicalComplex.homologyMap (singleHomComplexIso P A I).hom (q : ℤ) ≫
    HomologicalComplex.homologyMap (homMapExtendIso P A I).hom (q : ℤ) ≫
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).hom) c = _
  rw [H.π_comp_homologyIso_inv_assoc]
  change (H.cyclesIso.inv ≫
    (HomComplex ((singleFunctor C 0).obj P) I.cochainComplex).homologyπ (q : ℤ) ≫
    HomologicalComplex.homologyMap (singleHomComplexIso P A I).hom (q : ℤ) ≫
    HomologicalComplex.homologyMap (homMapExtendIso P A I).hom (q : ℤ) ≫
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).hom) c = _
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  change K.homologyπ q
    ((H.cyclesIso.inv ≫
      HomologicalComplex.cyclesMap (singleHomComplexIso P A I).hom (q : ℤ) ≫
      HomologicalComplex.cyclesMap (homMapExtendIso P A I).hom (q : ℤ) ≫
      (K.extendCyclesIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).hom) c) = _
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles q)).mp inferInstance
  change (H.cyclesIso.inv ≫
    HomologicalComplex.cyclesMap (singleHomComplexIso P A I).hom (q : ℤ) ≫
    HomologicalComplex.cyclesMap (homMapExtendIso P A I).hom (q : ℤ) ≫
    (K.extendCyclesIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).hom ≫ K.iCycles q) c = _
  rw [HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
  simp only [HomologicalComplex.iCycles]
  rw [H.cyclesIso_inv_comp_iCycles_assoc]
  erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
  dsimp [H, leftHomologyData, leftHomologyData', singleHomComplexIso, c]
  change (K.extendXIso ComplexShape.embeddingUpNat (i' := (q : ℤ)) rfl).hom
    ((homMapExtendIso P A I).hom.f (q : ℤ)
      ((Cochain.fromSingleEquiv (zero_add (q : ℤ)))
        (Cochain.fromSingleMk (f ≫ (I.cochainComplexXIso q q rfl).inv) (zero_add (q : ℤ))))) = f
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  let F := preadditiveCoyoneda.obj (op P)
  let eX : ∀ o : Option ℕ, F.obj (HomologicalComplex.extend.X I.cocomplex o) ≅
      HomologicalComplex.extend.X K o
    | some n => Iso.refl _
    | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero AddCommGrpCat)
  have component (o : Option ℕ) (ho : o = some q) :
      (HomologicalComplex.extend.XIso K ho).hom
        ((eX o).hom (f ≫ (HomologicalComplex.extend.XIso I.cocomplex ho).inv)) = f := by
    subst o
    dsimp [eX, HomologicalComplex.extend.XIso]
    exact Category.comp_id f
  exact component _ (ComplexShape.embeddingUpNat.r_eq_some (i := q) rfl)

/-- A coefficient map extended to any map of injective resolutions induces the native
Ext map on the actual Hom-complex cohomology (textbook lines 1640–1648). -/
theorem extHomologyIso_hom_naturality (P : C) {A B : C}
    (I : InjectiveResolution A) (J : InjectiveResolution B) {f : A ⟶ B}
    (φ : I.Hom J f) (q : ℕ) :
    (extFunctorObj P q).map f ≫ (extHomologyIso P J q).hom =
      (extHomologyIso P I q).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).map φ.hom) q := by
  ext α
  obtain ⟨x, hx, rfl⟩ := I.extMk_surjective α (q+1) rfl
  change (extHomologyIso P J q).hom
    ((I.extMk x (q+1) rfl hx).comp (Ext.mk₀ f) (add_zero q)) =
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).map φ.hom) q)
        ((extHomologyIso P I q).hom (I.extMk x (q+1) rfl hx))
  rw [I.extMk_comp_mk₀ x (q+1) rfl hx φ,
    extHomologyIso_hom_extMk, extHomologyIso_hom_extMk]
  let K := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let ψ := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).map φ.hom
  change L.homologyπ q _ = (K.homologyπ q ≫ HomologicalComplex.homologyMap ψ q) _
  rw [HomologicalComplex.homologyπ_naturality]
  change L.homologyπ q _ = L.homologyπ q _
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (L.iCycles q)).mp inferInstance
  change _ = (HomologicalComplex.cyclesMap ψ q ≫ L.iCycles q) _
  rw [HomologicalComplex.cyclesMap_i]
  dsimp [L, K, HomologicalComplex.iCycles]
  erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
  change x ≫ φ.hom.f q = ψ.f q _
  congr 1
  erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Abelian
open CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-- For fixed `P`, `Ext^q(P, -)` is the `q`-th right derived functor of `Hom(P, -)`,
naturally in the coefficient object (cf. Weibel §2.5). -/
noncomputable def extFunctorObjIsoRightDerived (P : C) (q : ℕ) :
  extFunctorObj P q ≅ (preadditiveCoyoneda.obj (op P)).rightDerived q :=
  NatIso.ofComponents (fun A =>
    extHomologyIso P (injectiveResolution A) q ≪≫
      ((injectiveResolution A).isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).symm) (by
    intro A B f
    let I := injectiveResolution A
    let J := injectiveResolution B
    let φ : I.Hom J f := ⟨InjectiveResolution.desc f J I, by
      simpa using InjectiveResolution.desc_commutes_zero f J I⟩
    change (extFunctorObj P q).map f ≫
      (extHomologyIso P J q).hom ≫ (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).inv =
      ((extHomologyIso P I q).hom ≫ (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).inv) ≫
        ((preadditiveCoyoneda.obj (op P)).rightDerived q).map f
    let F := preadditiveCoyoneda.obj (op P)
    let ψ := HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) q
    have hn : (I.isoRightDerivedObj F q).inv ≫ (F.rightDerived q).map f =
        ψ ≫ (J.isoRightDerivedObj F q).inv :=
      InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ.hom
        (by simpa using φ.ι_f_zero_comp_hom_f_zero) F q
    let a : (extFunctorObj P q).obj A ⟶
        ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q :=
      (extHomologyIso P I q).hom
    let b : (extFunctorObj P q).obj B ⟶
        ((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homology q :=
      (extHomologyIso P J q).hom
    let dI : ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q ⟶
        (F.rightDerived q).obj A := (I.isoRightDerivedObj F q).inv
    let dJ : ((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homology q ⟶
        (F.rightDerived q).obj B := (J.isoRightDerivedObj F q).inv
    have he : (extFunctorObj P q).map f ≫ b = a ≫ ψ :=
      extHomologyIso_hom_naturality P I J φ q
    change (extFunctorObj P q).map f ≫ b ≫ dJ = (a ≫ dI) ≫ (F.rightDerived q).map f
    calc
      _ = ((extFunctorObj P q).map f ≫ b) ≫ dJ := (Category.assoc _ _ _).symm
      _ = (a ≫ ψ) ≫ dJ := congrArg (fun z => z ≫ dJ) he
      _ = a ≫ (ψ ≫ dJ) := Category.assoc _ _ _
      _ = a ≫ (dI ≫ (F.rightDerived q).map f) := congrArg (fun z => a ≫ z) hn.symm
      _ = _ := (Category.assoc _ _ _).symm)

/-- The one natural Ext/right-derived identification is computed by any injective
resolution; hence different resolution computations agree canonically
(textbook lines 1647–1648). -/
theorem extFunctorObjIsoRightDerived_hom_app (P : C) {A : C}
    (I : InjectiveResolution A) (q : ℕ) :
    (extFunctorObjIsoRightDerived P q).hom.app A =
      (extHomologyIso P I q).hom ≫ (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).inv := by
  let J := injectiveResolution A
  let φ : J.Hom I (𝟙 A) := ⟨InjectiveResolution.desc (𝟙 A) I J, by
    simpa using InjectiveResolution.desc_commutes_zero (𝟙 A) I J⟩
  have h₁ := extHomologyIso_hom_naturality P J I φ q
  simp only [Functor.map_id] at h₁
  erw [Category.id_comp] at h₁
  change (extHomologyIso P J q).hom ≫ (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).inv =
    (extHomologyIso P I q).hom ≫ (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) q).inv
  erw [h₁, Category.assoc]
  have h₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 A) J I φ.hom
    (by simpa using φ.ι_f_zero_comp_hom_f_zero) (preadditiveCoyoneda.obj (op P)) q
  simp only [Functor.map_id, Category.comp_id] at h₂
  exact congrArg (fun z => (extHomologyIso P J q).hom ≫ z) h₂

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-- For fixed P, the canonical natural identification Ext⁰(P,-) ≅ Hom(P,-) is the
native Ext/right-derived comparison followed by the canonical degree-zero comparison.
It does not assert equality of separately chosen models. -/
noncomputable def extFunctorObjZeroIsoCoyoneda (P : C) :
    extFunctorObj P 0 ≅ preadditiveCoyoneda.obj (op P) :=
  extFunctorObjIsoRightDerived P 0 ≪≫
    (preadditiveCoyoneda.obj (op P)).rightDerivedZeroIsoSelf

end CategoryTheory.Abelian

namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

set_option backward.isDefEq.respectTransparency false in
/-- In any injective resolution, the canonical Ext⁰-to-Hom identification sends a
degree-zero cocycle to its factorization through the original augmentation. The
augmentation is a kernel, so this factorization is unique. -/
theorem extFunctorObjZeroIsoCoyoneda_hom_app_extMk (P : C) {A : C}
    (I : InjectiveResolution A) (f : P ⟶ I.cocomplex.X 0)
    (hf : f ≫ I.cocomplex.d 0 1 = 0) :
    (CategoryTheory.Abelian.extFunctorObjZeroIsoCoyoneda P).hom.app A
      (I.extMk f 1 rfl hf) ≫ I.ι.f 0 = f := by
  let F := preadditiveCoyoneda.obj (op P)
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := extFunctorObjZeroIsoCoyoneda P
  let α := I.extMk f 1 rfl hf
  let x := e.hom.app A α
  let c : K.cycles 0 := (K.sc 0).abCyclesIso.inv ⟨f, by
    change f ≫ I.cocomplex.d 0 ((ComplexShape.up ℕ).next 0) = 0
    rw [CochainComplex.next]
    exact hf⟩
  have he : e.hom.app A ≫ F.toRightDerivedZero.app A =
      (extFunctorObjIsoRightDerived P 0).hom.app A := by
    change ((extFunctorObjIsoRightDerived P 0).hom.app A ≫
      F.rightDerivedZeroIsoSelf.hom.app A) ≫ F.toRightDerivedZero.app A = _
    rw [Category.assoc, F.rightDerivedZeroIsoSelf_hom_inv_id_app, Category.comp_id]
  rw [extFunctorObjIsoRightDerived_hom_app P I 0, I.toRightDerivedZero_eq F] at he
  have h := ConcreteCategory.congr_hom he α
  change (I.isoRightDerivedObj F 0).inv
      (K.homologyπ 0 (I.toRightDerivedZero' F x)) =
    (I.isoRightDerivedObj F 0).inv ((I.extHomologyIso P 0).hom α) at h
  have hα : (I.extHomologyIso P 0).hom α = K.homologyπ 0 c :=
    I.extHomologyIso_hom_extMk P 0 f hf
  rw [hα] at h
  have hπ : K.homologyπ 0 (I.toRightDerivedZero' F x) = K.homologyπ 0 c :=
    (AddCommGrpCat.mono_iff_injective (I.isoRightDerivedObj F 0).inv).mp inferInstance h
  have hc : I.toRightDerivedZero' F x = c :=
    (AddCommGrpCat.mono_iff_injective (CochainComplex.isoHomologyπ₀ K).hom).mp
      inferInstance hπ
  have hi := congrArg (fun z => K.iCycles 0 z) hc
  change (I.toRightDerivedZero' F ≫ K.iCycles 0) x = K.iCycles 0 c at hi
  rw [I.toRightDerivedZero'_comp_iCycles F] at hi
  have hci : K.iCycles 0 c = f := (K.sc 0).abCyclesIso_inv_apply_iCycles _
  exact hi.trans hci

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-- The additive native Ext boundary is the fixed right-derived boundary of Hom(P,-)
under the canonical native comparison. It is independent of resolution choices;
its positive lift convention is computed by any compatible resolution below. -/
def extConnecting (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (extFunctorObj P n).obj S.X₃ ⟶ (extFunctorObj P (n + 1)).obj S.X₁ :=
  (extFunctorObjIsoRightDerived P n).hom.app S.X₃ ≫
    (preadditiveCoyoneda.obj (op P)).rightDerivedConnecting hS n ≫
    (extFunctorObjIsoRightDerived P (n + 1)).inv.app S.X₁

/-- Compute the same native Ext boundary on any original compatible triple of
injective resolutions. On the actual Hom complexes it sends the class of z to
the class of a, with r(b)=z and j(a)=db. Canonical comparisons retain the sign,
all lift/representative choices and degree zero. -/
theorem extConnecting_eq (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (z : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ i, ((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) i)).ShortExact)
    (hM : ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))).ShortExact) :
    extConnecting P hS n =
      (InjectiveResolution.extHomologyIso P IC n).hom ≫ hM.δ n (n + 1) rfl ≫
        (InjectiveResolution.extHomologyIso P IA (n + 1)).inv := by
  have hA : ((extFunctorObjIsoRightDerived P (n + 1)).app S.X₁).inv =
      (InjectiveResolution.extHomologyIso P IA (n + 1) ≪≫
        (IA.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) (n + 1)).symm).inv :=
    congrArg Iso.inv (Iso.ext (extFunctorObjIsoRightDerived_hom_app P IA (n + 1)))
  change (extFunctorObjIsoRightDerived P (n + 1)).inv.app S.X₁ =
    (IA.isoRightDerivedObj (preadditiveCoyoneda.obj (op P)) (n + 1)).hom ≫
      (InjectiveResolution.extHomologyIso P IA (n + 1)).inv at hA
  unfold extConnecting
  rw [extFunctorObjIsoRightDerived_hom_app P IC n, hA,
    Functor.rightDerivedConnecting_eq (preadditiveCoyoneda.obj (op P)) hS n
      IA IB IC j q z ha hb he hM]
  let F := preadditiveCoyoneda.obj (op P)
  let HC := ((F.mapHomologicalComplex (.up ℕ)).obj IC.cocomplex).homology n
  let HA := ((F.mapHomologicalComplex (.up ℕ)).obj IA.cocomplex).homology (n + 1)
  let eC : (extFunctorObj P n).obj S.X₃ ≅ HC :=
    InjectiveResolution.extHomologyIso P IC n
  let eA : (extFunctorObj P (n + 1)).obj S.X₁ ≅ HA :=
    InjectiveResolution.extHomologyIso P IA (n + 1)
  let tC : (F.rightDerived n).obj S.X₃ ≅ HC := IC.isoRightDerivedObj F n
  let tA : (F.rightDerived (n + 1)).obj S.X₁ ≅ HA := IA.isoRightDerivedObj F (n + 1)
  let d : HC ⟶ HA := hM.δ n (n + 1) rfl
  change (eC.hom ≫ tC.inv) ≫ (tC.hom ≫ d ≫ tA.inv) ≫ (tA.hom ≫ eA.inv) =
    eC.hom ≫ d ≫ eA.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The original quotient map followed by the positive Ext boundary is zero: a closed
lift has zero differential. This is the converse before the boundary. -/
theorem comp_extConnecting (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
  (extFunctorObj P n).map S.g ≫ extConnecting P hS n = 0 := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  have hq' := InjectiveResolution.extHomologyIso_hom_naturality P IB IC
    (show IB.Hom IC S.g from ⟨q, by simpa using HomologicalComplex.congr_hom haq 0⟩) n
  rw [extConnecting_eq P hS n IA IB IC j q z haj haq he hM]
  rw [← Category.assoc, hq', Category.assoc]
  change (IB.extHomologyIso P n).hom ≫ HomologicalComplex.homologyMap M.g n ≫
    hM.δ n (n+1) rfl ≫ (IA.extHomologyIso P (n+1)).inv = 0
  simpa only [Category.assoc, comp_zero, zero_comp] using
    congrArg (fun f => (IB.extHomologyIso P n).hom ≫ f ≫
      (IA.extHomologyIso P (n+1)).inv) (hM.comp_δ n (n+1) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The positive Ext boundary followed by the original subobject map is zero: its
image is a differential. This is the converse after the boundary. -/
theorem extConnecting_comp (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
  extConnecting P hS n ≫ (extFunctorObj P (n+1)).map S.f = 0 := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  have hj' := InjectiveResolution.extHomologyIso_hom_naturality P IA IB
    (show IA.Hom IB S.f from ⟨j, by simpa using HomologicalComplex.congr_hom haj 0⟩) (n+1)
  apply (cancel_mono (IB.extHomologyIso P (n+1)).hom).mp
  rw [zero_comp, Category.assoc, hj', extConnecting_eq P hS n IA IB IC j q z haj haq he hM]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (IC.extHomologyIso P n).hom ≫ hM.δ n (n+1) rfl ≫
    HomologicalComplex.homologyMap M.f (n+1) = 0
  simpa only [comp_zero] using
    congrArg (fun f => (IC.extHomologyIso P n).hom ≫ f) (hM.δ_comp n (n+1) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the middle coefficient in every nonnegative Ext degree. If r(b)=dw,
lift w to v and replace b by b-dv. The closed result has a unique closed preimage
under j; the converse is rj=0. -/
theorem ext_exact₁ (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
  (S.map (extFunctorObj P n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  let e : (S.map (extFunctorObj P n)) ≅
      ShortComplex.mk (HomologicalComplex.homologyMap M.f n)
        (HomologicalComplex.homologyMap M.g n)
        (by rw [← HomologicalComplex.homologyMap_comp, M.zero,
          HomologicalComplex.homologyMap_zero]) := by
    refine ShortComplex.isoMk (IA.extHomologyIso P n) (IB.extHomologyIso P n)
      (IC.extHomologyIso P n) ?_ ?_
    · exact (InjectiveResolution.extHomologyIso_hom_naturality P IA IB
        ⟨j, by simpa using HomologicalComplex.congr_hom haj 0⟩ n).symm
    · exact (InjectiveResolution.extHomologyIso_hom_naturality P IB IC
        ⟨q, by simpa using HomologicalComplex.congr_hom haq 0⟩ n).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₂ n)

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the quotient before the positive Ext boundary. If a=dt, replace
its lift b by b-j(t), which is closed with the same quotient. The converse is
the zero composite before the boundary. -/
theorem ext_exact₂ (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
  (ShortComplex.mk ((extFunctorObj P n).map S.g) (extConnecting P hS n)
    (comp_extConnecting P hS n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  let e : (ShortComplex.mk ((extFunctorObj P n).map S.g) (extConnecting P hS n)
      (comp_extConnecting P hS n)) ≅
      (ShortComplex.mk (HomologicalComplex.homologyMap M.g n) (hM.δ n (n+1) rfl)
        (hM.comp_δ n (n+1) rfl)) := by
    refine ShortComplex.isoMk (IB.extHomologyIso P n) (IC.extHomologyIso P n)
      (IA.extHomologyIso P (n+1)) ?_ ?_
    · exact (InjectiveResolution.extHomologyIso_hom_naturality P IB IC
        ⟨q, by simpa using HomologicalComplex.congr_hom haq 0⟩ n).symm
    · dsimp
      rw [extConnecting_eq P hS n IA IB IC j q z haj haq he hM]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₃ n (n+1) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the next subobject after the positive Ext boundary. If j(a)=db,
r(b) is closed and its positive boundary represents a. The converse is the zero
composite after the boundary. -/
theorem ext_exact₃ (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
  (ShortComplex.mk (extConnecting P hS n) ((extFunctorObj P (n+1)).map S.f)
    (extConnecting_comp P hS n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  let e : (ShortComplex.mk (extConnecting P hS n) ((extFunctorObj P (n+1)).map S.f)
      (extConnecting_comp P hS n)) ≅
      (ShortComplex.mk (hM.δ n (n+1) rfl) (HomologicalComplex.homologyMap M.f (n+1))
        (hM.δ_comp n (n+1) rfl)) := by
    refine ShortComplex.isoMk (IC.extHomologyIso P n) (IA.extHomologyIso P (n+1))
      (IB.extHomologyIso P (n+1)) ?_ ?_
    · dsimp
      rw [extConnecting_eq P hS n IA IB IC j q z haj haq he hM]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact (InjectiveResolution.extHomologyIso_hom_naturality P IA IB
        ⟨j, by simpa using HomologicalComplex.congr_hom haj 0⟩ (n+1)).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₁ n (n+1) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The original subobject map is injective in degree-zero Ext. Nonnegative
resolutions have no incoming differential at zero: homology is the outgoing
kernel, and degreewise monicity gives injection. Transport uses the original
augmentation-compatible comparison. -/
theorem ext_zero_injective (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
  Function.Injective ((extFunctorObj P 0).map S.f) := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  let M := (ShortComplex.mk j q z).map
    ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ))
  have hmono : Mono (HomologicalComplex.homologyMap M.f 0) := by
    let : Mono (M.f.f 0) := ((HomologicalComplex.shortExact_iff_degreewise_shortExact M).mp hM 0).mono_f
    exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel M.f 0 (by simp)
  have hi := (AddCommGrpCat.mono_iff_injective (HomologicalComplex.homologyMap M.f 0)).mp hmono
  have hs := InjectiveResolution.extHomologyIso_hom_naturality P IA IB
    (show IA.Hom IB S.f from ⟨j, by simpa using HomologicalComplex.congr_hom haj 0⟩) 0
  intro x y hxy
  have hx := CategoryTheory.congr_fun hs x
  have hy := CategoryTheory.congr_fun hs y
  simp only [CategoryTheory.comp_apply] at hx hy
  have ht : (IA.extHomologyIso P 0).hom x = (IA.extHomologyIso P 0).hom y := by
    apply hi
    exact hx.symm.trans ((congrArg (fun z => (IB.extHomologyIso P 0).hom z) hxy).trans hy)
  have hu := congrArg (fun z => (IA.extHomologyIso P 0).inv z) ht
  simpa only [← CategoryTheory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply] using hu


set_option backward.isDefEq.respectTransparency false in
/-- The positive native Ext boundary is natural for every original morphism of
short exact sequences.
A strict comparison sends a chosen cochain lift to a lift of the image cocycle;
its differential is the image of the original differential. The same positive
boundary square passes through the canonical resolution identifications.
The quotient coefficient map is in degree n and the subobject map in degree n+1.
Ordinary adjacent squares follow from the native degree functors' laws. -/
theorem extConnecting_naturality (P : C) {S S' : ShortComplex C}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (f : S ⟶ S') (n : ℕ) :
    (extFunctorObj P n).map f.τ₃ ≫ extConnecting P hS' n =
      extConnecting P hS n ≫ (extFunctorObj P (n+1)).map f.τ₁ := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp := fun n =>
    letI : Injective (((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA.cocomplex.X n))
    (he n).splittingOfInjective
  have hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  obtain ⟨T',h0',L',R',eA',eB',eC',rA',rB',rC',hT',hL',hR',hB',hel',her',hrl',hrr',hA',hB'',hC',
    sqA',sqB',sqC',IA',IB',IC',hIA',hIB',hIC',ha',hb',hc'⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S' hS'
  obtain ⟨j',q',z',haj',haq',hj',hq',hse',hs'⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S' hS'
      T' h0' L' R' eA' eB' eC' rA' rB' rC' hel' her' hrl' hrr' sqA' sqB' sqC'
      IA' IB' IC' hIA' hIB' hIC' ha' hb' hc'
  have he' := fun n => (hs' n).1
  let sp' := fun n =>
    letI : Injective (((ShortComplex.mk j' q' z').map
      (HomologicalComplex.eval C (.up ℕ) n)).X₁) :=
      inferInstanceAs (Injective (IA'.cocomplex.X n))
    (he' n).splittingOfInjective
  have hM' := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j' q' z').map
      ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)))
    (fun n => ((sp' n).map (preadditiveCoyoneda.obj (op P))).shortExact)
  obtain ⟨φ, aφ, bφ, cφ⟩ :=
    InjectiveResolution.exists_strict_comparison_of_compatible_resolutions
      S S' hS hS' f IA IB IC j q z haj haq he IA' IB' IC' j' q' z' haj' haq' he'
  let Ψ := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℕ)).mapShortComplex.map φ
  have hd := HomologicalComplex.HomologySequence.δ_naturality Ψ hM hM' n (n+1) rfl
  have hmiddle := InjectiveResolution.extHomologyIso_hom_naturality P IB IB'
    (show IB.Hom IB' f.τ₂ from ⟨φ.τ₂, by simpa using HomologicalComplex.congr_hom bφ 0⟩) n
  have hc := InjectiveResolution.extHomologyIso_hom_naturality P IC IC'
    (show IC.Hom IC' f.τ₃ from ⟨φ.τ₃, by simpa using HomologicalComplex.congr_hom cφ 0⟩) n
  have hleft := InjectiveResolution.extHomologyIso_hom_naturality P IA IA'
    (show IA.Hom IA' f.τ₁ from ⟨φ.τ₁, by simpa using HomologicalComplex.congr_hom aφ 0⟩) (n+1)
  apply (cancel_mono (IA'.extHomologyIso P (n+1)).hom).mp
  rw [Category.assoc, Category.assoc, hleft,
    extConnecting_eq P hS n IA IB IC j q z haj haq he hM,
    extConnecting_eq P hS' n IA' IB' IC' j' q' z' haj' haq' he' hM']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hc, Category.assoc]
  exact congrArg (fun t => (IC.extHomologyIso P n).hom ≫ t) hd.symm

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-- The canonical identification of degree-zero Ext with Hom is the degree-zero
Ext-to-right-derived comparison followed by the Hom functor's canonical zero-degree
identification. This records the fixed composition without exposing its definition. -/
theorem extFunctorObjZeroIsoCoyoneda_eq (P : C) :
    extFunctorObjZeroIsoCoyoneda P =
      extFunctorObjIsoRightDerived P 0 ≪≫
        (preadditiveCoyoneda.obj (op P)).rightDerivedZeroIsoSelf := by
  unfold extFunctorObjZeroIsoCoyoneda
  rfl

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v, v, u} C

/-- The native Ext boundary is the right-derived Hom boundary conjugated by the
same canonical Ext-to-right-derived comparison in consecutive degrees. This is
the defining composition of the positive connecting map: on a compatible resolution
the lift satisfies `j(a) = db`, with no additional sign. The equation retains that
fixed comparison for both forward and inverse transport. -/
theorem extConnecting_eq_rightDerived (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) :
    extConnecting P hS n =
      (extFunctorObjIsoRightDerived P n).hom.app S.X₃ ≫
        (preadditiveCoyoneda.obj (op P)).rightDerivedConnecting hS n ≫
        (extFunctorObjIsoRightDerived P (n + 1)).inv.app S.X₁ := by
  unfold extConnecting
  rfl

end CategoryTheory.Abelian
