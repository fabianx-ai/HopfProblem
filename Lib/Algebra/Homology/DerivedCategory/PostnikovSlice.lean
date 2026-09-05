/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Single-degree objects and Postnikov slices in a derived category

For the canonical t-structure on a derived category, this file identifies an object concentrated
in one degree with the corresponding single homology object.  It then identifies the homology of
the Postnikov slice `τ_[n,n+1) K` with `Hⁿ(K)` and obtains an object-level isomorphism

` τ_[n,n+1) K ≅ Hⁿ(K)[-n] `.

The single-object isomorphism uses classical choice from Mathlib's existence theorem and is
normalized to induce the identity on degree-`n` homology.  The downstream naturality owner proves
that this normalization makes the comparison natural on single-degree objects.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A derived object concentrated in degree `n` is isomorphic to the single object on its
degree-`n` homology.  Its normalization and naturality are proved in the downstream naturality
owner. -/
def isoSingleFunctorHomology (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K) := by
  let Y := (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose
  let e : K ≅ (singleFunctor C n).obj Y :=
    (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose_spec.some
  let hY : (homologyFunctor C n).obj K ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app Y
  exact e ≪≫ (singleFunctor C n).mapIso hY.symm

/-- Truncating above degree `n` does not change degree-`n` homology. -/
lemma isIso_homologyFunctor_map_truncLTι (K : DerivedCategory C) (n : ℤ) :
    IsIso ((homologyFunctor C n).map ((TStructure.t.truncLTι (n + 1)).app K)) := by
  let T := (TStructure.t.triangleLTGE (n + 1)).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished (n + 1) K
  have hepi : Epi ((homologyFunctor C n).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n).2
      (IsZero.eq_of_tgt
        (isZero_of_isGE T.obj₃ (n + 1) n (by omega)) _ _)
  have hmono : Mono ((homologyFunctor C n).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n (by omega)).2
      (IsZero.eq_of_src
        (isZero_of_isGE T.obj₃ (n + 1) (n - 1) (by omega)) _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C n).map T.mor₁)

/-- Truncating below degree `n` does not change degree-`n` homology. -/
lemma isIso_homologyFunctor_map_truncGEπ (K : DerivedCategory C) (n : ℤ) :
    IsIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app K)) := by
  let T := (TStructure.t.triangleLTGE n).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished n K
  have hepi : Epi ((homologyFunctor C n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) (by omega)).2
      (IsZero.eq_of_tgt
        (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)) _ _)
  have hmono : Mono ((homologyFunctor C n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2
      (IsZero.eq_of_src
        (isZero_of_isLE T.obj₁ (n - 1) n (by omega)) _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C n).map T.mor₂)

/-- The degree-`n` homology of the Postnikov slice `τ_[n,n+1) K` is the degree-`n`
homology of `K`. -/
def postnikovSliceHomologyIso (K : DerivedCategory C) (n : ℤ) :
    (homologyFunctor C n).obj
        ((TStructure.t.truncGE n).obj ((TStructure.t.truncLT (n + 1)).obj K)) ≅
      (homologyFunctor C n).obj K := by
  letI := isIso_homologyFunctor_map_truncGEπ
    ((TStructure.t.truncLT (n + 1)).obj K) n
  letI := isIso_homologyFunctor_map_truncLTι K n
  exact (asIso ((homologyFunctor C n).map
      ((TStructure.t.truncGEπ n).app ((TStructure.t.truncLT (n + 1)).obj K)))).symm ≪≫
    asIso ((homologyFunctor C n).map ((TStructure.t.truncLTι (n + 1)).app K))

/-- The Postnikov slice `τ_[n,n+1) K` is isomorphic to the single object on `Hⁿ(K)`.
Naturality of this complete slice adapter is treated separately. -/
def postnikovSliceIso (K : DerivedCategory C) (n : ℤ) :
    (TStructure.t.truncGE n).obj ((TStructure.t.truncLT (n + 1)).obj K) ≅
      (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
  isoSingleFunctorHomology
      ((TStructure.t.truncGE n).obj ((TStructure.t.truncLT (n + 1)).obj K)) n ≪≫
    (singleFunctor C n).mapIso (postnikovSliceHomologyIso K n)

end DerivedCategory
