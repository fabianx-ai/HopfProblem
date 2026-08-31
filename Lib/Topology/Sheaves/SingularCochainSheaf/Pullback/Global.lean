/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnit
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Sheaf

/-!
# Naturality of the global singular-cochain sheafification unit

Evaluation of sheafified cochain pullback on the top open is the literal pullback on global
sections.  The global sheafification-unit comparison commutes with native singular pullback.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

theorem preimageMap_inclusion (U : Opens Y) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp (preimageMap f U) =
      f.hom.comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C((Opens.map f).obj U, X)) := by
  ext x
  rfl

/-- Evaluation on the top open gives the map on literal global sheafified cochains. -/
def globalSheafPullback : globalCochainComplex Y A ⟶ globalCochainComplex X A where
  f n := (cochainPullback f A n).hom.app (op ⊤)
  comm' i j _ :=
    NatTrans.congr_app
      (congrArg (fun θ : sheaf Y A i ⟶
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj (sheaf X A j) => θ.hom)
        (cochainPullback_d f A i j)) (op ⊤)

@[simp]
theorem globalSheafPullback_f (n : ℕ) :
    (globalSheafPullback f A).f n = (cochainPullback f A n).hom.app (op ⊤) := rfl

/-- The native global cochain unit commutes with continuous-map pullback. -/
theorem globalCochainUnit_pullback (n : ℕ) :
    (AlgebraicTopology.SingularCochains.pullback A f.hom).f n ≫
        globalCochainUnit X A n =
      globalCochainUnit Y A n ≫ (globalSheafPullback f A).f n := by
  let iX : C((⊤ : Opens X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iY : C((⊤ : Opens Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hspace : iY.comp (preimageMap f ⊤) = f.hom.comp iX :=
    preimageMap_inclusion f ⊤
  have hcochain :
      AlgebraicTopology.SingularCochains.pullback A f.hom ≫
          AlgebraicTopology.SingularCochains.pullback A iX =
        AlgebraicTopology.SingularCochains.pullback A iY ≫
          AlgebraicTopology.SingularCochains.pullback A (preimageMap f ⊤) := by
    exact (AlgebraicTopology.SingularCochains.pullback_comp A iX f.hom).symm.trans
      ((congrArg (AlgebraicTopology.SingularCochains.pullback A) hspace.symm).trans
        (AlgebraicTopology.SingularCochains.pullback_comp A (preimageMap f ⊤) iY))
  have hunit := NatTrans.congr_app (unit_cochainPullback f A n) (op ⊤)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  have hc := ConcreteCategory.congr_hom (congrArg (fun k => k.f n) hcochain) φ
  have hu := ConcreteCategory.congr_hom hunit
    ((AlgebraicTopology.SingularCochains.pullback A iY).f n φ)
  change (unit X A n).app (op ⊤)
      ((AlgebraicTopology.SingularCochains.pullback A iX).f n
        ((AlgebraicTopology.SingularCochains.pullback A f.hom).f n φ)) =
    (cochainPullback f A n).hom.app (op ⊤)
      ((unit Y A n).app (op ⊤)
        ((AlgebraicTopology.SingularCochains.pullback A iY).f n φ))
  exact (congrArg (fun z => (unit X A n).app (op ⊤) z) hc).trans hu.symm

/-- The full native-to-sheafified global cochain map is natural. -/
theorem globalCochainComparison_naturality :
    AlgebraicTopology.SingularCochains.pullback A f.hom ≫
        globalCochainComparison X A =
      globalCochainComparison Y A ≫ globalSheafPullback f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact globalCochainUnit_pullback f A n

/-- Naturality after passing to degree-`n` homology. -/
theorem globalCochainComparison_homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.SingularCochains.pullback A f.hom) n ≫
      HomologicalComplex.homologyMap (globalCochainComparison X A) n =
    HomologicalComplex.homologyMap (globalCochainComparison Y A) n ≫
      HomologicalComplex.homologyMap (globalSheafPullback f A) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n)
      (globalCochainComparison_naturality f A)).trans
        (HomologicalComplex.homologyMap_comp _ _ n))

end TopCat.SingularCochainSheaf
