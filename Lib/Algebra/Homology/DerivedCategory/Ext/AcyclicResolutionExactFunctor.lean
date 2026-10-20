/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolution
public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1ExactFunctor

/-!
# Indexed acyclic resolutions and exact functors

An exact additive functor carries an indexed acyclic resolution to an indexed acyclic resolution.
The arbitrary-degree dimension-shifting comparison commutes with the corresponding endpoint Ext
comparison.  This is the indexed form of the standard functoriality of acyclic resolutions.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext.AcyclicResolution

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  (G : Functor C D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Apply an exact additive functor termwise to an indexed acyclic resolution. -/
def map (R : AcyclicResolution (C := C)) : AcyclicResolution (C := D) where
  Z n := G.obj (R.Z n)
  X n := G.obj (R.X n)
  i n := G.map (R.i n)
  p n := G.map (R.p n)
  zero n := (G.map_comp _ _).symm.trans
    ((congrArg G.map (R.zero n)).trans (G.map_zero _ _))
  shortExact n := (R.shortExact n).map_of_exact G

omit [HasExt C] [HasExt D] in
@[simp]
theorem map_Z (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.map G).Z n = G.obj (R.Z n) := rfl

omit [HasExt C] [HasExt D] in
@[simp]
theorem map_X (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.map G).X n = G.obj (R.X n) := rfl

omit [HasExt C] [HasExt D] in
@[simp]
theorem map_i (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.map G).i n = G.map (R.i n) := rfl

omit [HasExt C] [HasExt D] in
@[simp]
theorem map_p (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.map G).p n = G.map (R.p n) := rfl

omit [HasExt C] [HasExt D] in
/-- The mapped indexed differential is the image of the original differential. -/
theorem map_d (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.map G).d n = G.map (R.d n) := by
  change G.map (R.p n) ≫ G.map (R.i (n + 1)) =
    G.map (R.p n ≫ R.i (n + 1))
  exact (G.map_comp _ _).symm

variable {V : C} {P : D} (eta : P ⟶ G.obj V)

/-- The endpoint Ext comparison, bundled as a morphism of additive groups. -/
abbrev comparisonHom (F : C) (n : ℕ) :
    (extFunctorObj V n).obj F ⟶ (extFunctorObj P n).obj (G.obj F) :=
  AcyclicResolutionH1.comparisonHom G eta F n

/-- The endpoint comparison applied termwise to the evaluated resolution complexes. -/
def evaluatedComplexMap (R : AcyclicResolution (C := C)) :
    R.evaluatedComplex V ⟶ (R.map G).evaluatedComplex P :=
  CochainComplex.ofHom (fun n ↦ comparisonHom G eta (R.X n) 0) (fun n ↦ by
    rw [R.evaluatedComplex_d, (R.map G).evaluatedComplex_d, map_d]
    symm
    ext e
    exact ExactFunctorComparison.map_naturality G eta (R.d n) e)

/-- Surjective endpoint comparisons transfer positive-degree acyclicity to the mapped
resolution. -/
theorem isAcyclicFor_map_of_surjective (R : AcyclicResolution (C := C))
    (hR : R.IsAcyclicFor V)
    (hsurj : ∀ (i q : ℕ), 0 < q →
      Function.Surjective (ExactFunctorComparison.map G eta (R.X i) q)) :
    (R.map G).IsAcyclicFor P := by
  intro i q hq
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a', rfl⟩ := hsurj i q hq a
  obtain ⟨b', rfl⟩ := hsurj i q hq b
  exact congrArg (ExactFunctorComparison.map G eta (R.X i) q)
    (@Subsingleton.elim _ (hR i q hq) a' b')

set_option backward.isDefEq.respectTransparency false in
private theorem connectingIso_inv_naturality
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext V S.X₂ n)] [Subsingleton (Ext V S.X₂ (n + 1))]
    [Subsingleton (Ext P (S.map G).X₂ n)]
    [Subsingleton (Ext P (S.map G).X₂ (n + 1))] :
    comparisonHom G eta S.X₁ (n + 1) ≫
        (connectingIso P (hS.map_of_exact G) n).inv =
      (connectingIso V hS n).inv ≫ comparisonHom G eta S.X₃ n := by
  let a := comparisonHom G eta S.X₁ (n + 1)
  let b := comparisonHom G eta S.X₃ n
  let dV := connectingIso V hS n
  let dP := connectingIso P (hS.map_of_exact G) n
  have hhom : b ≫ dP.hom = dV.hom ≫ a := by
    ext e
    change connecting P (hS.map_of_exact G) n
        (ExactFunctorComparison.map G eta S.X₃ n e) =
      ExactFunctorComparison.map G eta S.X₁ (n + 1)
        (connecting V hS n e)
    exact (ExactFunctorComparison.map_connecting G eta hS e).symm
  apply (cancel_mono dP.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hhom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of every iterated dimension shift under an exact additive functor. -/
@[reassoc]
theorem shiftIso_naturality (R : AcyclicResolution (C := C))
    (hR : R.IsAcyclicFor V) (hG : (R.map G).IsAcyclicFor P) (n : ℕ) :
    comparisonHom G eta (R.Z 0) (n + 1) ≫
        ((R.map G).shiftIso P hG n).hom =
      (R.shiftIso V hR n).hom ≫ comparisonHom G eta (R.Z n) 1 := by
  induction n generalizing R with
  | zero =>
      rw [R.shiftIso_zero, (R.map G).shiftIso_zero]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
      let _ : Subsingleton (Ext V (R.X 0) (n + 1)) :=
        hR 0 (n + 1) (Nat.succ_pos n)
      let _ : Subsingleton (Ext V (R.X 0) ((n + 1) + 1)) :=
        hR 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      let _ : Subsingleton (Ext P ((R.map G).X 0) (n + 1)) :=
        hG 0 (n + 1) (Nat.succ_pos n)
      let _ : Subsingleton (Ext P ((R.map G).X 0) ((n + 1) + 1)) :=
        hG 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      let _ : Subsingleton (Ext P ((R.step 0).map G).X₂ (n + 1)) :=
        hG 0 (n + 1) (Nat.succ_pos n)
      let _ : Subsingleton (Ext P ((R.step 0).map G).X₂ ((n + 1) + 1)) :=
        hG 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      let a := comparisonHom G eta (R.Z 0) ((n + 1) + 1)
      let b := comparisonHom G eta (R.Z 1) (n + 1)
      let c := comparisonHom G eta (R.Z (n + 1)) 1
      let dV := (connectingIso V (R.shortExact 0) (n + 1)).inv
      let dP := (connectingIso P ((R.shortExact 0).map_of_exact G) (n + 1)).inv
      let rTail := (R.tail.shiftIso V (R.isAcyclicFor_tail V hR) n).hom
      let gTail := ((R.map G).tail.shiftIso P
        ((R.map G).isAcyclicFor_tail P hG) n).hom
      change a ≫ (dP ≫ gTail) = (dV ≫ rTail) ≫ c
      have hd : a ≫ dP = dV ≫ b :=
        connectingIso_inv_naturality G eta (R.shortExact 0) (n + 1)
      have ht : b ≫ gTail = rTail ≫ c := by
        exact ih R.tail (R.isAcyclicFor_tail V hR)
          ((R.map G).isAcyclicFor_tail P hG)
      calc
        a ≫ (dP ≫ gTail) = (a ≫ dP) ≫ gTail :=
          (Category.assoc _ _ _).symm
        _ = (dV ≫ b) ≫ gTail := congrArg (fun k ↦ k ≫ gTail) hd
        _ = dV ≫ (b ≫ gTail) := Category.assoc _ _ _
        _ = dV ≫ (rTail ≫ c) := congrArg (fun k ↦ dV ≫ k) ht
        _ = (dV ≫ rTail) ≫ c := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The exact-functor image of a truncation and the truncation of the indexed image have the
same objects and canonically equivalent differentials. -/
def truncComparison (R : AcyclicResolution (C := C)) (n : ℕ) :
    AcyclicResolutionH1.Hom ((R.trunc n).map G) ((R.map G).trunc n) where
  augmentation := 𝟙 _
  complex :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp only [AcyclicResolutionH1.map, AcyclicResolution.trunc]
        rw [Category.id_comp, Category.comp_id]
        exact map_d G R n
      comm₂₃ := by
        dsimp only [AcyclicResolutionH1.map, AcyclicResolution.trunc]
        rw [Category.id_comp, Category.comp_id]
        exact map_d G R (n + 1) }
  comm := by
    dsimp only [AcyclicResolutionH1.map, AcyclicResolution.trunc]
    rw [Category.id_comp, Category.comp_id]
    rfl

/-- The endpoint comparison on the local degree-zero Ext window, followed by the canonical
truncation comparison. -/
def truncExtZeroMap (R : AcyclicResolution (C := C)) (n : ℕ) :
    (R.trunc n).extZeroComplex V ⟶ ((R.map G).trunc n).extZeroComplex P :=
  AcyclicResolutionH1.extZeroMap G eta (R.trunc n) ≫
    (truncComparison G R n).extZeroMap P

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the final degree-one step after an arbitrary number of dimension shifts. -/
theorem truncExtOneIso_naturality (R : AcyclicResolution (C := C))
    (n : ℕ)
    [Subsingleton (Ext V (R.trunc n).complex.X₁ 1)]
    [Subsingleton (Ext P ((R.trunc n).map G).complex.X₁ 1)]
    [Subsingleton (Ext P ((R.map G).trunc n).complex.X₁ 1)] :
    comparisonHom G eta (R.Z n) 1 ≫
        (((R.map G).trunc n).extOneIso P).hom =
      ((R.trunc n).extOneIso V).hom ≫
        ShortComplex.homologyMap (truncExtZeroMap G eta R n) := by
  let m := AcyclicResolutionH1.extZeroMap G eta (R.trunc n)
  let k := (truncComparison G R n).extZeroMap P
  let q := (extFunctorObj P 1).map (truncComparison G R n).augmentation
  have h₁ := AcyclicResolutionH1.extOneIso_naturality G eta (R.trunc n)
  have h₂ := (truncComparison G R n).extOneIso_naturality P
  have h₁' : comparisonHom G eta (R.Z n) 1 ≫
        (((R.trunc n).map G).extOneIso P).hom =
      ((R.trunc n).extOneIso V).hom ≫ ShortComplex.homologyMap m := by
    simpa only [AcyclicResolution.trunc_F] using h₁
  have hq : comparisonHom G eta (R.Z n) 1 ≫ q =
      comparisonHom G eta (R.Z n) 1 := by
    have hqid : q = 𝟙 ((extFunctorObj P 1).obj (G.obj (R.Z n))) := by
      dsimp only [q, truncComparison]
      exact (extFunctorObj P 1).map_id (G.obj (R.Z n))
    rw [hqid, Category.comp_id]
  calc
    comparisonHom G eta (R.Z n) 1 ≫
        (((R.map G).trunc n).extOneIso P).hom =
      (comparisonHom G eta (R.Z n) 1 ≫ q) ≫
        (((R.map G).trunc n).extOneIso P).hom :=
      congrArg (fun z ↦ z ≫ (((R.map G).trunc n).extOneIso P).hom) hq.symm
    _ = comparisonHom G eta (R.Z n) 1 ≫
        (q ≫ (((R.map G).trunc n).extOneIso P).hom) :=
      Category.assoc _ _ _
    _ = comparisonHom G eta (R.Z n) 1 ≫
        ((((R.trunc n).map G).extOneIso P).hom ≫
          ShortComplex.homologyMap k) :=
      congrArg (fun z ↦ comparisonHom G eta (R.Z n) 1 ≫ z) h₂
    _ = (comparisonHom G eta (R.Z n) 1 ≫
        (((R.trunc n).map G).extOneIso P).hom) ≫
          ShortComplex.homologyMap k := (Category.assoc _ _ _).symm
    _ = (((R.trunc n).extOneIso V).hom ≫
        ShortComplex.homologyMap m) ≫ ShortComplex.homologyMap k :=
      congrArg (fun q ↦ q ≫ ShortComplex.homologyMap k) h₁'
    _ = ((R.trunc n).extOneIso V).hom ≫
        (ShortComplex.homologyMap m ≫ ShortComplex.homologyMap k) :=
      Category.assoc _ _ _
    _ = ((R.trunc n).extOneIso V).hom ≫
        ShortComplex.homologyMap (m ≫ k) :=
      congrArg (fun q ↦ ((R.trunc n).extOneIso V).hom ≫ q)
        (ShortComplex.homologyMap_comp m k).symm

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the local all-degree comparison under an exact additive functor. -/
@[reassoc]
theorem localExtIso_naturality (R : AcyclicResolution (C := C))
    (hR : R.IsAcyclicFor V) (hG : (R.map G).IsAcyclicFor P) (n : ℕ) :
    comparisonHom G eta (R.Z 0) (n + 1) ≫
        ((R.map G).localExtIso P hG n).hom =
      (R.localExtIso V hR n).hom ≫
        ShortComplex.homologyMap (truncExtZeroMap G eta R n) := by
  let _ : Subsingleton (Ext V (R.trunc n).complex.X₁ 1) :=
    hR n 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P ((R.trunc n).map G).complex.X₁ 1) :=
    hG n 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P ((R.map G).trunc n).complex.X₁ 1) :=
    hG n 1 Nat.zero_lt_one
  let a := comparisonHom G eta (R.Z 0) (n + 1)
  let b := comparisonHom G eta (R.Z n) 1
  let rShift := (R.shiftIso V hR n).hom
  let gShift := ((R.map G).shiftIso P hG n).hom
  let rOne := ((R.trunc n).extOneIso V).hom
  let gOne := (((R.map G).trunc n).extOneIso P).hom
  let m := ShortComplex.homologyMap (truncExtZeroMap G eta R n)
  change a ≫ (gShift ≫ gOne) = (rShift ≫ rOne) ≫ m
  have hs : a ≫ gShift = rShift ≫ b :=
    shiftIso_naturality G eta R hR hG n
  have ho : b ≫ gOne = rOne ≫ m :=
    truncExtOneIso_naturality G eta R n
  calc
    a ≫ (gShift ≫ gOne) = (a ≫ gShift) ≫ gOne :=
      (Category.assoc _ _ _).symm
    _ = (rShift ≫ b) ≫ gOne := congrArg (fun q ↦ q ≫ gOne) hs
    _ = rShift ≫ (b ≫ gOne) := Category.assoc _ _ _
    _ = rShift ≫ (rOne ≫ m) := congrArg (fun q ↦ rShift ≫ q) ho
    _ = (rShift ≫ rOne) ≫ m := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The local degree-zero Ext comparison agrees with the corresponding window of the termwise
evaluated-complex comparison. -/
@[reassoc]
theorem truncExtZeroMap_evaluatedLocalIso (R : AcyclicResolution (C := C)) (n : ℕ) :
    truncExtZeroMap G eta R n ≫ ((R.map G).evaluatedLocalIso P n).hom =
      (R.evaluatedLocalIso V n).hom ≫
        (HomologicalComplex.shortComplexFunctor' AddCommGrpCat
          (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map
            (evaluatedComplexMap G eta R) := by
  apply ShortComplex.hom_ext
  · change comparisonHom G eta (R.X n) 0 ≫
        (extFunctorObj P 0).map (𝟙 _) = comparisonHom G eta (R.X n) 0
    rw [Functor.map_id, Category.comp_id]
  · change comparisonHom G eta (R.X (n + 1)) 0 ≫
        (extFunctorObj P 0).map (𝟙 _) = comparisonHom G eta (R.X (n + 1)) 0
    rw [Functor.map_id, Category.comp_id]
  · change comparisonHom G eta (R.X (n + 2)) 0 ≫
        (extFunctorObj P 0).map (𝟙 _) = comparisonHom G eta (R.X (n + 2)) 0
    rw [Functor.map_id, Category.comp_id]

/-- Naturality after passing from the local degree-zero Ext window to its literal homology. -/
@[reassoc]
theorem truncExtZeroHomology_naturality (R : AcyclicResolution (C := C)) (n : ℕ) :
    ShortComplex.homologyMap (truncExtZeroMap G eta R n) ≫
        (ShortComplex.homologyMapIso ((R.map G).evaluatedLocalIso P n)).hom =
      (ShortComplex.homologyMapIso (R.evaluatedLocalIso V n)).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
            (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map
              (evaluatedComplexMap G eta R)) := by
  let H := ShortComplex.homologyFunctor AddCommGrpCat
  change H.map (truncExtZeroMap G eta R n) ≫
      H.map ((R.map G).evaluatedLocalIso P n).hom =
    H.map (R.evaluatedLocalIso V n).hom ≫
      H.map ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
        (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map
          (evaluatedComplexMap G eta R))
  simpa only [Functor.map_comp] using congrArg H.map
    (truncExtZeroMap_evaluatedLocalIso G eta R n)

/-- Naturality of the inverse local-window identification for the termwise endpoint comparison. -/
@[reassoc]
theorem evaluatedWindowIso_inv_naturality
    (R : AcyclicResolution (C := C)) (n : ℕ) :
    ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
            (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map
              (evaluatedComplexMap G eta R)) ≫
        (((R.map G).evaluatedComplex P).homologyIsoSc'
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv =
      ((R.evaluatedComplex V).homologyIsoSc'
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv ≫
        HomologicalComplex.homologyMap (evaluatedComplexMap G eta R) (n + 1) := by
  let m := evaluatedComplexMap G eta R
  have hhom :
      HomologicalComplex.homologyMap m (n + 1) ≫
          (((R.map G).evaluatedComplex P).homologyIsoSc'
            n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom =
        ((R.evaluatedComplex V).homologyIsoSc'
            n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap
            ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
              (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map m) := by
    let H := ShortComplex.homologyFunctor AddCommGrpCat
    change H.map
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat
            (ComplexShape.up ℕ) (n + 1)).map m) ≫
        H.map ((HomologicalComplex.natIsoSc' AddCommGrpCat
          (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)
            (by simp) (by simp)).hom.app ((R.map G).evaluatedComplex P)) =
      H.map ((HomologicalComplex.natIsoSc' AddCommGrpCat
          (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)
            (by simp) (by simp)).hom.app (R.evaluatedComplex V)) ≫
        H.map ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
          (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map m)
    simpa only [Functor.map_comp] using congrArg H.map
      ((HomologicalComplex.natIsoSc' AddCommGrpCat
        (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)
          (by simp) (by simp)).hom.naturality m)
  let q := ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
      (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map m)
  let g := HomologicalComplex.homologyMap m (n + 1)
  let jR := (R.evaluatedComplex V).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)
  let jG := ((R.map G).evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)
  change q ≫ jG.inv = jR.inv ≫ g
  have hhom' : g ≫ jG.hom = jR.hom ≫ q := hhom
  apply (cancel_mono jG.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hhom', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem compThreeNaturality {E : Type*} [Category E]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : E}
    (a : A₀ ⟶ B₀) (s₁ : B₀ ⟶ B₁) (s₂ : B₁ ⟶ B₂) (s₃ : B₂ ⟶ B₃)
    (r₁ : A₀ ⟶ A₁) (b : A₁ ⟶ B₁) (r₂ : A₁ ⟶ A₂) (c : A₂ ⟶ B₂)
    (r₃ : A₂ ⟶ A₃) (d : A₃ ⟶ B₃)
    (h₁ : a ≫ s₁ = r₁ ≫ b) (h₂ : b ≫ s₂ = r₂ ≫ c)
    (h₃ : c ≫ s₃ = r₃ ≫ d) :
    a ≫ ((s₁ ≫ s₂) ≫ s₃) = ((r₁ ≫ r₂) ≫ r₃) ≫ d := by
  calc
    a ≫ ((s₁ ≫ s₂) ≫ s₃) = (((a ≫ s₁) ≫ s₂) ≫ s₃) := by
      simp only [Category.assoc]
    _ = (((r₁ ≫ b) ≫ s₂) ≫ s₃) := by rw [h₁]
    _ = ((r₁ ≫ (b ≫ s₂)) ≫ s₃) :=
      congrArg (fun k ↦ k ≫ s₃) (Category.assoc _ _ _)
    _ = ((r₁ ≫ (r₂ ≫ c)) ≫ s₃) := by rw [h₂]
    _ = (((r₁ ≫ r₂) ≫ c) ≫ s₃) :=
      congrArg (fun k ↦ k ≫ s₃) (Category.assoc _ _ _).symm
    _ = ((r₁ ≫ r₂) ≫ (c ≫ s₃)) := Category.assoc _ _ _
    _ = ((r₁ ≫ r₂) ≫ (r₃ ≫ d)) := by rw [h₃]
    _ = (((r₁ ≫ r₂) ≫ r₃) ≫ d) :=
      (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the all-positive-degree acyclic-resolution comparison under an exact additive
functor. -/
@[reassoc]
theorem extIsoHomology_naturality (R : AcyclicResolution (C := C))
    (hR : R.IsAcyclicFor V) (hG : (R.map G).IsAcyclicFor P) (n : ℕ) :
    comparisonHom G eta (R.Z 0) (n + 1) ≫
        ((R.map G).extIsoHomology P hG n).hom =
      (R.extIsoHomology V hR n).hom ≫
        HomologicalComplex.homologyMap (evaluatedComplexMap G eta R) (n + 1) := by
  let a := comparisonHom G eta (R.Z 0) (n + 1)
  let lR := (R.localExtIso V hR n).hom
  let lG := ((R.map G).localExtIso P hG n).hom
  let m := ShortComplex.homologyMap (truncExtZeroMap G eta R n)
  let eR := (ShortComplex.homologyMapIso (R.evaluatedLocalIso V n)).hom
  let eG := (ShortComplex.homologyMapIso ((R.map G).evaluatedLocalIso P n)).hom
  let q := ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat
      (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map
        (evaluatedComplexMap G eta R))
  let jR := ((R.evaluatedComplex V).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv
  let jG := (((R.map G).evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv
  let d := HomologicalComplex.homologyMap (evaluatedComplexMap G eta R) (n + 1)
  change a ≫ ((lG ≫ eG) ≫ jG) = ((lR ≫ eR) ≫ jR) ≫ d
  exact compThreeNaturality a lG eG jG lR m eR q jR d
    (localExtIso_naturality G eta R hR hG n)
    (truncExtZeroHomology_naturality G eta R n)
    (evaluatedWindowIso_inv_naturality G eta R n)

end CategoryTheory.Abelian.Ext.AcyclicResolution
