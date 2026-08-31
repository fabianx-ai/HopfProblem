/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1

/-!
# Naturality of the degree-one acyclic-resolution comparison

The canonical comparison from `Ext¹` to the homology of a degree-zero `Ext` complex commutes
with every map of exact augmented length-two resolutions.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Connecting maps commute with maps of short exact sequences. -/
theorem connecting_naturality (P : C) {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ)
    (x : Ext P S.X₃ n) :
    connecting P hT n ((mk₀ φ.τ₃).postcomp P (add_zero n) x) =
      (mk₀ φ.τ₁).postcomp P (add_zero (n + 1)) (connecting P hS n x) := by
  change (x.comp (mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl =
    (x.comp hS.extClass rfl).comp (mk₀ φ.τ₁) (add_zero (n + 1))
  rw [comp_assoc_of_second_deg_zero, comp_assoc_of_third_deg_zero,
    hS.extClass_naturality hT φ]

namespace AcyclicResolutionH1

variable {R S : AcyclicResolutionH1 (C := C)}

/-- A commuting map of exact augmented length-two resolutions. -/
structure Hom (R S : AcyclicResolutionH1 (C := C)) where
  augmentation : R.F ⟶ S.F
  complex : R.complex ⟶ S.complex
  comm : augmentation ≫ S.ι = R.ι ≫ complex.τ₁

namespace Hom

variable (φ : Hom R S)

/-- The induced map on the intermediate kernels. -/
def cyclesMap : R.cycles ⟶ S.cycles :=
  kernel.map R.complex.g S.complex.g φ.complex.τ₂ φ.complex.τ₃
    φ.complex.comm₂₃.symm

omit [HasExt C] in
@[reassoc (attr := simp)]
theorem cyclesMap_ι :
    φ.cyclesMap ≫ kernel.ι S.complex.g = kernel.ι R.complex.g ≫ φ.complex.τ₂ :=
  kernel.lift_ι _ _ _

omit [HasExt C] in
theorem toCycles_naturality :
    R.toCycles ≫ φ.cyclesMap = φ.complex.τ₁ ≫ S.toCycles := by
  apply (cancel_mono (kernel.ι S.complex.g)).mp
  simp only [Category.assoc, cyclesMap_ι, toCycles_ι, toCycles_ι_assoc]
  exact φ.complex.comm₁₂.symm

/-- The induced map of the first short exact sequences. -/
def firstMap : R.first ⟶ S.first where
  τ₁ := φ.augmentation
  τ₂ := φ.complex.τ₁
  τ₃ := φ.cyclesMap
  comm₁₂ := φ.comm
  comm₂₃ := φ.toCycles_naturality.symm

/-- Applying `Ext⁰(P,-)` to the given map of complexes. -/
def extZeroMap (P : C) : R.extZeroComplex P ⟶ S.extZeroComplex P :=
  (extFunctorObj P 0).mapShortComplex.map φ.complex

/-- Naturality of the first connecting map. -/
@[reassoc]
theorem connectingOne_naturality (P : C) :
    (extFunctorObj P 0).map φ.cyclesMap ≫
        AddCommGrpCat.ofHom (connecting P S.first_shortExact 0) =
      AddCommGrpCat.ofHom (connecting P R.first_shortExact 0) ≫
        (extFunctorObj P 1).map φ.augmentation := by
  ext x
  exact connecting_naturality P R.first_shortExact S.first_shortExact φ.firstMap 0 x

end Hom

variable (R : AcyclicResolutionH1 (C := C)) (P : C)

/-- The actual kernel inclusion supplies cycles in the degree-zero Ext complex. -/
def extCycleMap : AddCommGrpCat.of (Ext P R.cycles 0) ⟶ (R.extZeroComplex P).cycles :=
  (R.extZeroComplex P).liftCycles ((extFunctorObj P 0).map (kernel.ι R.complex.g))
    (by
      change (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
          (extFunctorObj P 0).map R.complex.g = 0
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero])

@[reassoc]
theorem extCycleMap_i :
    R.extCycleMap P ≫ (R.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) :=
  (R.extZeroComplex P).liftCycles_i _ _

theorem extOneHomologyData_cyclesIso_inv
    [Subsingleton (Ext P R.complex.X₁ 1)] :
    (R.extOneHomologyData P).cyclesIso.inv = R.extCycleMap P := by
  apply (cancel_mono (R.extZeroComplex P).iCycles).mp
  exact (R.extOneHomologyData P).cyclesIso_inv_comp_iCycles.trans
    (R.extCycleMap_i P).symm

/-- Formula for the comparison on a connecting representative. -/
theorem extOneIso_connecting_cycle
    [Subsingleton (Ext P R.complex.X₁ 1)] :
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 0) ≫ (R.extOneIso P).hom =
      R.extCycleMap P ≫ (R.extZeroComplex P).homologyπ := by
  exact (R.extOneHomologyData P).π_comp_homologyIso_inv.trans
    (congrArg (fun f => f ≫ (R.extZeroComplex P).homologyπ)
      (R.extOneHomologyData_cyclesIso_inv P))

namespace Hom

variable {R S : AcyclicResolutionH1 (C := C)} (φ : Hom R S) (P : C)

theorem extCycleMap_naturality :
    (extFunctorObj P 0).map φ.cyclesMap ≫ S.extCycleMap P =
      R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P) := by
  apply (cancel_mono (S.extZeroComplex P).iCycles).mp
  change ((extFunctorObj P 0).map φ.cyclesMap ≫ S.extCycleMap P) ≫
      (S.extZeroComplex P).iCycles =
    (R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P)) ≫
      (S.extZeroComplex P).iCycles
  have hmap : (extFunctorObj P 0).map φ.cyclesMap ≫
        (extFunctorObj P 0).map (kernel.ι S.complex.g) =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
        (extFunctorObj P 0).map φ.complex.τ₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.cyclesMap_ι]
  have hleft : ((extFunctorObj P 0).map φ.cyclesMap ≫ S.extCycleMap P) ≫
        (S.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map φ.cyclesMap ≫
        (extFunctorObj P 0).map (kernel.ι S.complex.g) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => (extFunctorObj P 0).map φ.cyclesMap ≫ k)
        (S.extCycleMap_i P))
  have hright : (R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P)) ≫
        (S.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
        (extFunctorObj P 0).map φ.complex.τ₂ := by
    simp only [Category.assoc, ShortComplex.cyclesMap_i, extCycleMap_i_assoc]
    rfl
  exact hleft.trans (hmap.trans hright.symm)

end Hom

/-- A comparison defined on surjective representatives is natural when both squares commute. -/
theorem comparison_naturality_of_epi {D : Type*} [Category D]
    {K L H H' V W : D}
    (c : K ⟶ H) (c' : L ⟶ H') (e : H ⟶ V) (e' : H' ⟶ W)
    (q : K ⟶ V) (q' : L ⟶ W) (k : K ⟶ L) (h : H ⟶ H') (v : V ⟶ W)
    [Epi c] (hc : k ≫ c' = c ≫ h) (he : c ≫ e = q)
    (he' : c' ≫ e' = q') (hq : k ≫ q' = q ≫ v) : h ≫ e' = e ≫ v := by
  apply (cancel_epi c).mp
  rw [← Category.assoc, ← hc, Category.assoc, he', hq, ← he, Category.assoc]

namespace Hom

variable {R S : AcyclicResolutionH1 (C := C)} (φ : Hom R S) (P : C)

/-- Naturality of the canonical degree-one acyclic-resolution comparison. -/
@[reassoc]
theorem extOneIso_naturality
    [Subsingleton (Ext P R.complex.X₁ 1)] [Subsingleton (Ext P S.complex.X₁ 1)] :
    (extFunctorObj P 1).map φ.augmentation ≫ (S.extOneIso P).hom =
      (R.extOneIso P).hom ≫ ShortComplex.homologyMap (φ.extZeroMap P) := by
  have : Epi (AddCommGrpCat.ofHom (connecting P R.first_shortExact 0)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (connecting_surjective P R.first_shortExact 0)
  refine comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (connecting P R.first_shortExact 0))
    (AddCommGrpCat.ofHom (connecting P S.first_shortExact 0))
    (R.extOneIso P).hom (S.extOneIso P).hom
    (R.extCycleMap P ≫ (R.extZeroComplex P).homologyπ)
    (S.extCycleMap P ≫ (S.extZeroComplex P).homologyπ)
    ((extFunctorObj P 0).map φ.cyclesMap) ((extFunctorObj P 1).map φ.augmentation)
    (ShortComplex.homologyMap (φ.extZeroMap P))
    (φ.connectingOne_naturality P) (R.extOneIso_connecting_cycle P)
    (S.extOneIso_connecting_cycle P) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (S.extZeroComplex P).homologyπ)
      (φ.extCycleMap_naturality P)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => R.extCycleMap P ≫ k)
            (ShortComplex.homologyπ_naturality (φ.extZeroMap P)).symm).trans
              (Category.assoc _ _ _).symm)))

end Hom

end AcyclicResolutionH1

end CategoryTheory.Abelian.Ext
