/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module
public import Lib.CategoryTheory.Abelian.Injective.CompatibleResolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Category.Grp.Abelian
public import Lib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.EpiMono
public section
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedVariables false
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Two arbitrary compatible triples compute the same positive derived boundary.
The strict identity-sequence comparison retains all three augmentation equations.
Its three theta computations and complex naturality give the displayed
postcomposition equality; cancellation proves choice independence (PD-L21,
TEXTBOOK 1520–1538). Individual comparison choices are already controlled by
the canonical computation isomorphisms; no simultaneous homotopy is required. -/
private theorem choice_independent
    (S : ShortComplex C) (hS : S.ShortExact) (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (n : ℕ)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (z : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ i, ((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM : ((ShortComplex.mk j q z).map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
    (IA' : InjectiveResolution S.X₁) (IB' : InjectiveResolution S.X₂)
    (IC' : InjectiveResolution S.X₃)
    (j' : IA'.cocomplex ⟶ IB'.cocomplex) (q' : IB'.cocomplex ⟶ IC'.cocomplex)
    (z' : j' ≫ q' = 0)
    (ha' : IA'.ι ≫ j' = (CochainComplex.single₀ C).map S.f ≫ IB'.ι)
    (hb' : IB'.ι ≫ q' = (CochainComplex.single₀ C).map S.g ≫ IC'.ι)
    (he' : ∀ i, ((ShortComplex.mk j' q' z').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM' : ((ShortComplex.mk j' q' z').map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    (IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
      (IA.isoRightDerivedObj F (n + 1)).inv = (IC'.isoRightDerivedObj F n).hom ≫ hM'.δ n (n + 1) rfl ≫
      (IA'.isoRightDerivedObj F (n + 1)).inv := by
  obtain ⟨φ, a0, b0, c0⟩ :=
    InjectiveResolution.exists_strict_comparison_of_compatible_resolutions
      S S hS hS (𝟙 S) IA IB IC j q z ha hb he IA' IB' IC' j' q' z' ha' hb' he'
  have a : IA.ι ≫ φ.τ₁ = IA'.ι := by simpa using a0
  have b : IB.ι ≫ φ.τ₂ = IB'.ι := by simpa using b0
  have c : IC.ι ≫ φ.τ₃ = IC'.ι := by simpa using c0
  have hA :
      (IA.isoRightDerivedObj F (n + 1)).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) =
          (IA'.isoRightDerivedObj F (n + 1)).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 S.X₁) IA IA' φ.τ₁
      (by simpa using HomologicalComplex.congr_hom a 0) F (n + 1)).symm
  have hB :
      (IB.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₂) n =
          (IB'.isoRightDerivedObj F n).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 S.X₂) IB IB' φ.τ₂
      (by simpa using HomologicalComplex.congr_hom b 0) F n).symm
  have hC :
      (IC.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n =
          (IC'.isoRightDerivedObj F n).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 S.X₃) IC IC' φ.τ₃
      (by simpa using HomologicalComplex.congr_hom c 0) F n).symm
  have hδ :
      hM.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n ≫
        hM'.δ n (n + 1) rfl :=
    HomologicalComplex.HomologySequence.δ_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapShortComplex.map φ)
      hM hM' n (n + 1) rfl
  apply (cancel_mono (IA'.isoRightDerivedObj F (n + 1)).hom).mp
  calc
    ((IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
        (IA.isoRightDerivedObj F (n + 1)).inv) ≫ (IA'.isoRightDerivedObj F (n + 1)).hom =
        (IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) := by
      rw [← hA]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (IC.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n ≫
          hM'.δ n (n + 1) rfl := by rw [hδ]
    _ = (IC'.isoRightDerivedObj F n).hom ≫ hM'.δ n (n + 1) rfl := by
      rw [← Category.assoc, hC]
    _ = ((IC'.isoRightDerivedObj F n).hom ≫ hM'.δ n (n + 1) rfl ≫
        (IA'.isoRightDerivedObj F (n + 1)).inv) ≫ (IA'.isoRightDerivedObj F (n + 1)).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Choose one compatible triple from the recursive construction, map its split
rows by the additive functor, and form the fixed-family composite. Independence
then computes this same map using every supplied compatible triple (PD-L21,
TEXTBOOK 1539–1540). Existence is separate from comparison of arbitrary choices. -/
private theorem exists_boundary
    (S : ShortComplex C) (hS : S.ShortExact) (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (n : ℕ) :
    ∃ d : (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁,
      ∀ (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (z : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ i, ((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM : ((ShortComplex.mk j q z).map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact), d = (IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
      (IA.isoRightDerivedObj F (n + 1)).inv := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  exact ⟨(IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
      (IA.isoRightDerivedObj F (n + 1)).inv,
    fun IA' IB' IC' j' q' z' ha' hb' he' hM' =>
      choice_independent S hS F n IA IB IC j q z haj haq he hM
        IA' IB' IC' j' q' z' ha' hb' he' hM'⟩

/-- The positive connecting morphism on the fixed injectively computed derived
groups. It is selected from the choice-independent computation predicate of
PD-L21, TEXTBOOK 1540; its value for every compatible choice is given below. -/
def rightDerivedConnecting (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  by exact Classical.choose (exists_boundary S hS F n)

/-- Compute the single derived connecting morphism by any original compatible
triple, with the canonical fixed-to-computed theta maps and positive complex
boundary. This is the all-choice conclusion of PD-L21, TEXTBOOK 1535–1540. -/
theorem rightDerivedConnecting_eq (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (z : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ i, ((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM : ((ShortComplex.mk j q z).map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    rightDerivedConnecting F hS n = (IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
      (IA.isoRightDerivedObj F (n + 1)).inv :=
  Classical.choose_spec (exists_boundary S hS F n) IA IB IC j q z ha hb he hM

/-- For arbitrary compatible resolutions of two short exact sequences, choose
one strict comparison extending the given object-sequence morphism. Its three
computation identities and the positive complex boundary square give equality
after postcomposition with the target computation isomorphism; cancelling that
isomorphism proves naturality on the fixed derived groups (TEXTBOOK 1542–1561).
No component monicity or epimorphicity is required. -/
private theorem connecting_naturality_of_compatible
    (S S' : ShortComplex C) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (f : S ⟶ S') (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (n : ℕ)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (z : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ i, ((ShortComplex.mk j q z).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM : ((ShortComplex.mk j q z).map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
    (IA' : InjectiveResolution S'.X₁) (IB' : InjectiveResolution S'.X₂)
    (IC' : InjectiveResolution S'.X₃)
    (j' : IA'.cocomplex ⟶ IB'.cocomplex) (q' : IB'.cocomplex ⟶ IC'.cocomplex)
    (z' : j' ≫ q' = 0)
    (ha' : IA'.ι ≫ j' = (CochainComplex.single₀ C).map S'.f ≫ IB'.ι)
    (hb' : IB'.ι ≫ q' = (CochainComplex.single₀ C).map S'.g ≫ IC'.ι)
    (he' : ∀ i, ((ShortComplex.mk j' q' z').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) i)).ShortExact)
    (hM' : ((ShortComplex.mk j' q' z').map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    (F.rightDerived n).map f.τ₃ ≫ F.rightDerivedConnecting hS' n =
      F.rightDerivedConnecting hS n ≫ (F.rightDerived (n + 1)).map f.τ₁ := by
  obtain ⟨φ, a, b, c⟩ :=
    InjectiveResolution.exists_strict_comparison_of_compatible_resolutions
      S S' hS hS' f IA IB IC j q z ha hb he IA' IB' IC' j' q' z' ha' hb' he'
  have hA :
      (IA.isoRightDerivedObj F (n + 1)).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) =
          (F.rightDerived (n + 1)).map f.τ₁ ≫ (IA'.isoRightDerivedObj F (n + 1)).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality f.τ₁ IA IA' φ.τ₁
      (by simpa using HomologicalComplex.congr_hom a 0) F (n + 1)).symm
  have hB :
      (IB.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₂) n =
          (F.rightDerived n).map f.τ₂ ≫ (IB'.isoRightDerivedObj F n).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality f.τ₂ IB IB' φ.τ₂
      (by simpa using HomologicalComplex.congr_hom b 0) F n).symm
  have hC :
      (IC.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n =
          (F.rightDerived n).map f.τ₃ ≫ (IC'.isoRightDerivedObj F n).hom := by
    simpa using (InjectiveResolution.isoRightDerivedObj_hom_naturality f.τ₃ IC IC' φ.τ₃
      (by simpa using HomologicalComplex.congr_hom c 0) F n).symm

  have hδ :
      hM.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n ≫
        hM'.δ n (n + 1) rfl :=
    HomologicalComplex.HomologySequence.δ_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapShortComplex.map φ)
      hM hM' n (n + 1) rfl

  rw [F.rightDerivedConnecting_eq hS n IA IB IC j q z ha hb he hM,
    F.rightDerivedConnecting_eq hS' n IA' IB' IC' j' q' z' ha' hb' he' hM']
  apply (cancel_mono (IA'.isoRightDerivedObj F (n + 1)).hom).mp
  symm
  calc
    (((IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
        (IA.isoRightDerivedObj F (n + 1)).inv) ≫
        (F.rightDerived (n + 1)).map f.τ₁) ≫ (IA'.isoRightDerivedObj F (n + 1)).hom =
      (IC.isoRightDerivedObj F n).hom ≫ hM.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₁) (n + 1) := by
      simp only [Category.assoc]
      rw [← hA]
      simp only [Iso.inv_hom_id_assoc]
    _ = (IC.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.τ₃) n ≫
        hM'.δ n (n + 1) rfl := by rw [hδ]
    _ = (F.rightDerived n).map f.τ₃ ≫
        (IC'.isoRightDerivedObj F n).hom ≫ hM'.δ n (n + 1) rfl := by
      rw [← Category.assoc, hC, Category.assoc]
    _ = ((F.rightDerived n).map f.τ₃ ≫
        (IC'.isoRightDerivedObj F n).hom ≫ hM'.δ n (n + 1) rfl ≫
        (IA'.isoRightDerivedObj F (n + 1)).inv) ≫
        (IA'.isoRightDerivedObj F (n + 1)).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The fixed positive derived connecting morphism is natural for every morphism
of short exact object sequences. Choose compatible resolutions on each side,
map their split rows by the additive functor, and apply the arbitrary-choice
comparison result (TEXTBOOK 1542–1563). The ordinary coefficient squares
separately follow from the derived functors' composition laws. -/
theorem rightDerivedConnecting_naturality
    (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (f : S ⟶ S') (n : ℕ) :
    (F.rightDerived n).map f.τ₃ ≫ F.rightDerivedConnecting hS' n =
      F.rightDerivedConnecting hS n ≫ (F.rightDerived (n + 1)).map f.τ₁ := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun n => (hs n).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  obtain ⟨T₂,h0₂,L₂,R₂,eA₂,eB₂,eC₂,rA₂,rB₂,rC₂,hT₂,hL₂,hR₂,hB₂,hel₂,her₂,hrl₂,hrr₂,hA₂,hB₂',hC₂,
    sqA₂,sqB₂,sqC₂,IA₂,IB₂,IC₂,hIA₂,hIB₂,hIC₂,ha₂,hb₂,hc₂⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S' hS'
  obtain ⟨j₂,q₂,z₂,haj₂,haq₂,hj₂,hq₂,hse₂,hs₂⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S' hS'
      T₂ h0₂ L₂ R₂ eA₂ eB₂ eC₂ rA₂ rB₂ rC₂ hel₂ her₂ hrl₂ hrr₂ sqA₂ sqB₂ sqC₂
      IA₂ IB₂ IC₂ hIA₂ hIB₂ hIC₂ ha₂ hb₂ hc₂
  have he₂ := fun n => (hs₂ n).1
  let sp₂ i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S' hS' IA₂ IB₂ IC₂ j₂ q₂ z₂ haj₂ haq₂ he₂).1 i)
  let hM₂ := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j₂ q₂ z₂).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp₂ i).map F).shortExact)
  exact connecting_naturality_of_compatible S S' hS hS' f F n
    IA IB IC j q z haj haq he hM
    IA₂ IB₂ IC₂ j₂ q₂ z₂ haj₂ haq₂ he₂ hM₂

/-- The degree-n coefficient map to the right term followed by the positive
connecting map is zero. Compute on a compatible triple, use the q computation
square and the complex boundary zero, and cancel theta at the next left term
(PD-L23, TEXTBOOK 1580–1582, first PD21). -/
theorem comp_rightDerivedConnecting (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (F.rightDerived n).map S.g ≫ F.rightDerivedConnecting hS n = 0 := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  have hqθ : (F.rightDerived n).map S.g ≫ (IC.isoRightDerivedObj F n).hom =
      (IB.isoRightDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q) n :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality S.g IB IC q
      (by simpa using HomologicalComplex.congr_hom haq 0) F n
  have hzero : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q) n ≫ hM.δ n (n + 1) rfl = 0 :=
    hM.comp_δ n (n + 1) rfl
  apply (cancel_mono (IA.isoRightDerivedObj F (n + 1)).hom).mp
  rw [Category.assoc, F.rightDerivedConnecting_eq hS n IA IB IC j q z haj haq he hM]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp]
  rw [← Category.assoc, hqθ, Category.assoc, hzero, comp_zero]

/-- The positive connecting map followed by the next left coefficient map
is zero. The j computation square identifies this with the complex boundary
zero after postcomposition by theta at the next middle term
(PD-L23, TEXTBOOK 1580–1582, second PD21). -/
theorem rightDerivedConnecting_comp (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    F.rightDerivedConnecting hS n ≫ (F.rightDerived (n + 1)).map S.f = 0 := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  have hjθ : (F.rightDerived (n + 1)).map S.f ≫ (IB.isoRightDerivedObj F (n + 1)).hom =
      (IA.isoRightDerivedObj F (n + 1)).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) (n + 1) :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality S.f IA IB j
      (by simpa using HomologicalComplex.congr_hom haj 0) F (n + 1)
  have hzero : hM.δ n (n + 1) rfl ≫ HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) (n + 1) = 0 :=
    hM.δ_comp n (n + 1) rfl
  apply (cancel_mono (IB.isoRightDerivedObj F (n + 1)).hom).mp
  rw [Category.assoc, hjθ,
    F.rightDerivedConnecting_eq hS n IA IB IC j q z haj haq he hM]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, zero_comp]
  rw [hzero, comp_zero]

/-- The fixed derived coefficient sequence is exact at the middle object
in every degree. All three theta maps identify the two coefficient arrows
with the homology sequence; transport its image/kernel equality through that
short-complex isomorphism (PD-L23, TEXTBOOK 1565–1579, first PD20).
The ordinary within-degree zero is the additive functor's map of S.zero. -/
theorem rightDerived_exact₁ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (S.map (F.rightDerived n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  let e : (S.map (F.rightDerived n)) ≅
      ShortComplex.mk
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) n)
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q) n)
        (by rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, z,
          Functor.map_zero, HomologicalComplex.homologyMap_zero]) :=
    ShortComplex.isoMk (IA.isoRightDerivedObj F n) (IB.isoRightDerivedObj F n)
      (IC.isoRightDerivedObj F n)
      (InjectiveResolution.isoRightDerivedObj_hom_naturality S.f IA IB j
        (by simpa using HomologicalComplex.congr_hom haj 0) F n).symm
      (InjectiveResolution.isoRightDerivedObj_hom_naturality S.g IB IC q
        (by simpa using HomologicalComplex.congr_hom haq 0) F n).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₂ n)

/-- The fixed derived sequence is exact at the right object before the
connecting map. Theta at the middle, right and next left terms identifies
both arrows with the corresponding complex homology pair; transport its
image/kernel equality (PD-L23, TEXTBOOK 1565–1579, second PD20). -/
theorem rightDerived_exact₂ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((F.rightDerived n).map S.g) (F.rightDerivedConnecting hS n)
      (comp_rightDerivedConnecting F hS n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  let e : ShortComplex.mk ((F.rightDerived n).map S.g) (F.rightDerivedConnecting hS n)
      (comp_rightDerivedConnecting F hS n) ≅
      ShortComplex.mk
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q) n)
        (hM.δ n (n + 1) rfl) (hM.comp_δ n (n + 1) rfl) := by
    refine ShortComplex.isoMk (IB.isoRightDerivedObj F n) (IC.isoRightDerivedObj F n)
      (IA.isoRightDerivedObj F (n + 1)) ?_ ?_
    · exact (InjectiveResolution.isoRightDerivedObj_hom_naturality S.g IB IC q
        (by simpa using HomologicalComplex.congr_hom haq 0) F n).symm
    · dsimp
      rw [F.rightDerivedConnecting_eq hS n IA IB IC j q z haj haq he hM]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₃ n (n + 1) rfl)

/-- The fixed derived sequence is exact at the next left object after the
connecting map. Theta at the right, next left and next middle terms identifies
the positive boundary and coefficient arrow with the corresponding homology
pair (PD-L23, TEXTBOOK 1565–1579, third PD20). -/
theorem rightDerived_exact₃ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (F.rightDerivedConnecting hS n) ((F.rightDerived (n + 1)).map S.f)
      (rightDerivedConnecting_comp F hS n)).Exact := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  let e : ShortComplex.mk (F.rightDerivedConnecting hS n) ((F.rightDerived (n + 1)).map S.f)
      (rightDerivedConnecting_comp F hS n) ≅
      ShortComplex.mk (hM.δ n (n + 1) rfl)
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) (n + 1))
        (hM.δ_comp n (n + 1) rfl) := by
    refine ShortComplex.isoMk (IC.isoRightDerivedObj F n) (IA.isoRightDerivedObj F (n + 1))
      (IB.isoRightDerivedObj F (n + 1)) ?_ ?_
    · dsimp
      rw [F.rightDerivedConnecting_eq hS n IA IB IC j q z haj haq he hM]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact (InjectiveResolution.isoRightDerivedObj_hom_naturality S.f IA IB j
        (by simpa using HomologicalComplex.congr_hom haj 0) F (n + 1)).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr (hM.homology_exact₁ n (n + 1) rfl)

/-- The initial degree-zero coefficient map is injective. Nonnegative
complexes have no incoming differential at zero, so the mapped component
monomorphism induces a homology monomorphism. The degree-zero theta square
transports it to the fixed family (PD-L23, TEXTBOOK 1586–1587).
This initial injection is retained separately from delta-functor assembly. -/
theorem rightDerived_zero_injective (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Injective ((F.rightDerived 0).map S.f) := by
  obtain ⟨T,h0,L,R,eA,eB,eC,rA,rB,rC,hT,hL,hR,hB,hel,her,hrl,hrr,hA,hB',hC,
    sqA,sqB,sqC,IA,IB,IC,hIA,hIB,hIC,ha,hb,hc⟩ :=
      InjectiveResolution.exists_recursive_injective_presentations S hS
  obtain ⟨j,q,z,haj,haq,hj,hq,hse,hs⟩ :=
    InjectiveResolution.strict_sequence_of_recursive_presentations S hS
      T h0 L R eA eB eC rA rB rC hel her hrl hrr sqA sqB sqC
      IA IB IC hIA hIB hIC ha hb hc
  have he := fun i => (hs i).1
  let sp i := Classical.choice ((InjectiveResolution.exists_presentations_of_compatible_resolutions
    S hS IA IB IC j q z haj haq he).1 i)
  let hM := HomologicalComplex.shortExact_of_degreewise_shortExact
    ((ShortComplex.mk j q z).map (F.mapHomologicalComplex (ComplexShape.up ℕ)))
    (fun i => ((sp i).map F).shortExact)
  have hm := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hM 0
  let : Mono (((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j).f 0) := hm.mono_f
  let : Mono (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by simp)
  have hjθ : (F.rightDerived 0).map S.f ≫ (IB.isoRightDerivedObj F 0).hom =
      (IA.isoRightDerivedObj F 0).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map j) 0 :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality S.f IA IB j
      (by simpa using HomologicalComplex.congr_hom haj 0) F 0
  have hmθ : Mono ((F.rightDerived 0).map S.f) := mono_of_mono_fac hjθ
  exact (AddCommGrpCat.mono_iff_injective _).mp hmθ

end CategoryTheory.Functor
