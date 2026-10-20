/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Global

/-!
# Naturality of the degree-one singular–sheaf comparison

When the comparison `S^•(·; A) → Γ(·, 𝒮^•)` is an isomorphism on degree-one cohomology, a map of
constant-sheaf cohomology groups that is compatible with the global-section comparison is
compatible with the comparison `H¹(X; A_X) ≅ H¹_sing(X; A)` (Bredon, *Sheaf Theory* III.1;
Warner, *Foundations of Differentiable Manifolds and Lie Groups* 5.32).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

private theorem compare_naturality {C : Type*} [Category C]
    {H H' S S' G G' : C}
    (e : H ⟶ S) (e' : H' ⟶ S') (u : S ⟶ G) (u' : S' ⟶ G') [Mono u']
    (r : H ⟶ G) (r' : H' ⟶ G') (a : H ⟶ H') (b : S ⟶ S') (c : G ⟶ G')
    (he : e ≫ u = r) (he' : e' ≫ u' = r')
    (hr : a ≫ r' = r ≫ c) (hu : b ≫ u' = u ≫ c) :
    a ≫ e' = e ≫ b := by
  apply (cancel_mono u').mp
  calc
    (a ≫ e') ≫ u' = a ≫ r' := by rw [Category.assoc, he']
    _ = r ≫ c := hr
    _ = (e ≫ u) ≫ c := by rw [he]
    _ = e ≫ (b ≫ u') := by rw [Category.assoc, hu]
    _ = (e ≫ b) ≫ u' := (Category.assoc _ _ _).symm

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- A map of degree-one constant-sheaf cohomology groups compatible with the global-section
comparison is compatible with the comparison `H¹(·; A_·) ≅ H¹_sing(·; A)`. -/
theorem h1Comparison_naturality_of_global
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)]
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison Y A) 1)]
    (a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf Y A) 1) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf X A) 1))
    (h : a ≫ (constantSheafGlobalH1Iso X A hX).hom =
      (constantSheafGlobalH1Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) 1) :
    a ≫ (h1Comparison X A hX).hom =
      (h1Comparison Y A hY).hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.SingularCochains.pullback A f.hom) 1 := by
  exact compare_naturality
    (h1Comparison Y A hY).hom (h1Comparison X A hX).hom
    (HomologicalComplex.homologyMap (globalCochainComparison Y A) 1)
    (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)
    (constantSheafGlobalH1Iso Y A hY).hom
    (constantSheafGlobalH1Iso X A hX).hom a
    (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A f.hom) 1)
    (HomologicalComplex.homologyMap (globalSheafPullback f A) 1)
    (h1Comparison_global Y A hY) (h1Comparison_global X A hX) h
    (globalCochainComparison_homology_naturality f A 1)

end TopCat.SingularCochainSheaf
