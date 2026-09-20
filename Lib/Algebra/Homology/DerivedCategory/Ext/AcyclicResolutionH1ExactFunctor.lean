/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1Naturality
public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorComparison

/-!
# Degree-one acyclic resolutions and exact functors

The canonical degree-one acyclic-resolution comparison commutes with the endpoint Ext map of an
exact additive functor.  This is the H¹-only form of the standard functoriality argument.

## References

* [R. Hartshorne, *Algebraic geometry*][hartshorne77], Chapter III, Proposition 1.2A
  (an acyclic resolution computes the derived functors).
* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §2.4.
* [A. Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck57], §2 (an exact
  functor preserving injectives commutes with `Ext`).

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext.AcyclicResolutionH1

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  (G : Functor C D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Apply an exact additive functor to an augmented length-two resolution. -/
def map (R : AcyclicResolutionH1 (C := C)) : AcyclicResolutionH1 (C := D) where
  F := G.obj R.F
  complex := R.complex.map G
  ι := G.map R.ι
  zero := (G.map_comp _ _).symm.trans ((congrArg G.map R.zero).trans (G.map_zero _ _))
  initial_exact := R.initial_exact.map G
  exact := R.exact.map G
  mono_ι := inferInstanceAs (Mono (G.map R.ι))

variable {V : C} {P : D} (eta : P ⟶ G.obj V)

/-- The endpoint Ext comparison, bundled as a morphism of additive groups. -/
def comparisonHom (F : C) (n : ℕ) :
    (extFunctorObj V n).obj F ⟶ (extFunctorObj P n).obj (G.obj F) :=
  AddCommGrpCat.ofHom (ExactFunctorComparison.map G eta F n)

private theorem comparisonHom_naturality_aux {F K : C} (g : F ⟶ K) (n : ℕ) :
    (extFunctorObj V n).map g ≫ comparisonHom G eta K n =
      comparisonHom G eta F n ≫ (extFunctorObj P n).map (G.map g) := by
  ext e
  exact ExactFunctorComparison.map_naturality G eta g e

/-- The termwise endpoint comparison on the degree-zero Ext complexes. -/
def extZeroMap (R : AcyclicResolutionH1 (C := C)) :
    R.extZeroComplex V ⟶ (R.map G).extZeroComplex P where
  τ₁ := comparisonHom G eta R.complex.X₁ 0
  τ₂ := comparisonHom G eta R.complex.X₂ 0
  τ₃ := comparisonHom G eta R.complex.X₃ 0
  comm₁₂ := by
    symm
    ext e
    exact ExactFunctorComparison.map_naturality G eta R.complex.f e
  comm₂₃ := by
    symm
    ext e
    exact ExactFunctorComparison.map_naturality G eta R.complex.g e

/-- Exactness gives the comparison between the image of the original cycles and the cycles of
the image resolution. -/
private def cyclesComparison (R : AcyclicResolutionH1 (C := C)) :
    G.obj R.cycles ⟶ (R.map G).cycles :=
  kernelComparison R.complex.g G

omit [HasExt C] [HasExt D] in
private theorem cyclesComparison_ι (R : AcyclicResolutionH1 (C := C)) :
    cyclesComparison G R ≫ kernel.ι (R.map G).complex.g =
      G.map (kernel.ι R.complex.g) :=
  kernelComparison_comp_ι R.complex.g G

omit [HasExt C] [HasExt D] in
private theorem map_toCycles_cyclesComparison (R : AcyclicResolutionH1 (C := C)) :
    G.map R.toCycles ≫ cyclesComparison G R = (R.map G).toCycles := by
  apply (cancel_mono (kernel.ι (R.map G).complex.g)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => G.map R.toCycles ≫ k) (cyclesComparison_ι G R)).trans
      ((G.map_comp _ _).symm.trans
        ((congrArg G.map R.toCycles_ι).trans (R.map G).toCycles_ι.symm)))

/-- The mapped first short exact sequence maps to the first sequence of the mapped resolution. -/
private def firstMap (R : AcyclicResolutionH1 (C := C)) :
    R.first.map G ⟶ (R.map G).first where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := cyclesComparison G R
  comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (map_toCycles_cyclesComparison G R).symm

/-- Comparison on the intermediate cycles. -/
private def cyclesExtComparison (R : AcyclicResolutionH1 (C := C)) (n : ℕ) :
    (extFunctorObj V n).obj R.cycles ⟶
      (extFunctorObj P n).obj (R.map G).cycles :=
  comparisonHom G eta R.cycles n ≫ (extFunctorObj P n).map (cyclesComparison G R)

private theorem cyclesExtComparison_ι (R : AcyclicResolutionH1 (C := C)) (n : ℕ) :
    cyclesExtComparison G eta R n ≫
        (extFunctorObj P n).map (kernel.ι (R.map G).complex.g) =
      (extFunctorObj V n).map (kernel.ι R.complex.g) ≫
        comparisonHom G eta R.complex.X₂ n := by
  change (comparisonHom G eta R.cycles n ≫
      (extFunctorObj P n).map (cyclesComparison G R)) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => comparisonHom G eta R.cycles n ≫ k)
      ((extFunctorObj P n).map_comp (cyclesComparison G R)
        (kernel.ι (R.map G).complex.g)).symm).trans
      ((congrArg (fun k => comparisonHom G eta R.cycles n ≫
        (extFunctorObj P n).map k) (cyclesComparison_ι G R)).trans
          (comparisonHom_naturality_aux G eta (kernel.ι R.complex.g) n).symm))

set_option maxHeartbeats 800000 in
private theorem connecting_naturality (R : AcyclicResolutionH1 (C := C)) :
    cyclesExtComparison G eta R 0 ≫
        AddCommGrpCat.ofHom (CategoryTheory.Abelian.Ext.connecting P (R.map G).first_shortExact 0) =
      AddCommGrpCat.ofHom (CategoryTheory.Abelian.Ext.connecting V R.first_shortExact 0) ≫
        comparisonHom G eta R.F 1 := by
  ext e
  let _ : Mono R.first.f := R.first_shortExact.mono_f
  let _ : Epi R.first.g := R.first_shortExact.epi_g
  have hmapExact : (R.first.map G).ShortExact := R.first_shortExact.map G
  have hmap := ExactFunctorComparison.map_connecting G eta R.first_shortExact e
  have hfirst := CategoryTheory.Abelian.Ext.connecting_naturality P
    hmapExact (R.map G).first_shortExact (firstMap G R) 0
    (ExactFunctorComparison.map G eta R.cycles 0 e)
  simp only [firstMap] at hfirst
  change CategoryTheory.Abelian.Ext.connecting P (R.map G).first_shortExact 0
      ((ExactFunctorComparison.map G eta R.cycles 0 e).comp
        (Ext.mk₀ (cyclesComparison G R)) (add_zero 0)) =
    (CategoryTheory.Abelian.Ext.connecting P hmapExact 0
      (ExactFunctorComparison.map G eta R.cycles 0 e)).comp
      (Ext.mk₀ (𝟙 (G.obj R.F))) (add_zero 1)
      at hfirst
  have hfirst' := hfirst.trans
    (Ext.comp_mk₀_id
      (CategoryTheory.Abelian.Ext.connecting P hmapExact 0
        (ExactFunctorComparison.map G eta R.cycles 0 e)))
  change CategoryTheory.Abelian.Ext.connecting P (R.map G).first_shortExact 0
      ((ExactFunctorComparison.map G eta R.cycles 0 e).comp
        (Ext.mk₀ (cyclesComparison G R)) (add_zero 0)) =
    ExactFunctorComparison.map G eta R.F 1
      (CategoryTheory.Abelian.Ext.connecting V R.first_shortExact 0 e)
  exact hfirst'.trans hmap.symm

private theorem extCycleMap_naturality (R : AcyclicResolutionH1 (C := C)) :
    cyclesExtComparison G eta R 0 ≫ (R.map G).extCycleMap P =
      R.extCycleMap V ≫ ShortComplex.cyclesMap (extZeroMap G eta R) := by
  apply (cancel_mono ((R.map G).extZeroComplex P).iCycles).mp
  have hleft :
      (cyclesExtComparison G eta R 0 ≫ (R.map G).extCycleMap P) ≫
          ((R.map G).extZeroComplex P).iCycles =
        cyclesExtComparison G eta R 0 ≫
          (extFunctorObj P 0).map (kernel.ι (R.map G).complex.g) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => cyclesExtComparison G eta R 0 ≫ k)
        ((R.map G).extCycleMap_i P))
  have hright :
      (R.extCycleMap V ≫ ShortComplex.cyclesMap (extZeroMap G eta R)) ≫
          ((R.map G).extZeroComplex P).iCycles =
        (extFunctorObj V 0).map (kernel.ι R.complex.g) ≫
          comparisonHom G eta R.complex.X₂ 0 := by
    simp only [Category.assoc, ShortComplex.cyclesMap_i,
      AcyclicResolutionH1.extCycleMap_i_assoc]
    rfl
  exact hleft.trans ((cyclesExtComparison_ι G eta R 0).trans hright.symm)

/-- Naturality of the H¹ acyclic-resolution comparison under an exact additive functor. -/
@[reassoc]
theorem extOneIso_naturality (R : AcyclicResolutionH1 (C := C))
    [Subsingleton (Ext V R.complex.X₁ 1)]
    [Subsingleton (Ext P (R.map G).complex.X₁ 1)] :
    comparisonHom G eta R.F 1 ≫ ((R.map G).extOneIso P).hom =
      (R.extOneIso V).hom ≫ ShortComplex.homologyMap (extZeroMap G eta R) := by
  have : Epi (AddCommGrpCat.ofHom
      (CategoryTheory.Abelian.Ext.connecting V R.first_shortExact 0)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (CategoryTheory.Abelian.Ext.connecting_surjective V R.first_shortExact 0)
  refine CategoryTheory.Abelian.Ext.AcyclicResolutionH1.comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (CategoryTheory.Abelian.Ext.connecting V R.first_shortExact 0))
    (AddCommGrpCat.ofHom
      (CategoryTheory.Abelian.Ext.connecting P (R.map G).first_shortExact 0))
    (R.extOneIso V).hom ((R.map G).extOneIso P).hom
    (R.extCycleMap V ≫ (R.extZeroComplex V).homologyπ)
    ((R.map G).extCycleMap P ≫ ((R.map G).extZeroComplex P).homologyπ)
    (cyclesExtComparison G eta R 0) (comparisonHom G eta R.F 1)
    (ShortComplex.homologyMap (extZeroMap G eta R))
    (connecting_naturality G eta R) (R.extOneIso_connecting_cycle V)
    ((R.map G).extOneIso_connecting_cycle P) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ((R.map G).extZeroComplex P).homologyπ)
      (extCycleMap_naturality G eta R)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => R.extCycleMap V ≫ k)
            (ShortComplex.homologyπ_naturality (extZeroMap G eta R)).symm).trans
              (Category.assoc _ _ _).symm)))

end CategoryTheory.Abelian.Ext.AcyclicResolutionH1
