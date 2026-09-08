/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Constant integer sheaves and global sections

The constant integer sheaf represents global sections of abelian sheaves on an
arbitrary topological space. This additive natural representation is literal
evaluation on the sheafification-unit image of the integer generator. Its inverse
and uniqueness are recorded on every open. Both reconstruction identities are the
standard additive-equivalence inverse laws.

This is the constant-sheaf/global-sections adjunction and its generator computation;
it makes no derived-functor or geometric realization assertion.
-/

public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat.ConstantSheaf

variable (X : TopCat.{u})
variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The constant integer sheaf represents global sections of every abelian sheaf.
The constant-sheaf adjunction identifies its morphisms with homomorphisms from the lifted
integer group to global sections. Evaluation at the integer generator gives this additive
equivalence; its inverse extends integer multiples of the restrictions of a global section. -/
def homGlobalSectionsAddEquiv : (((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) ≃+ (((sheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).obj F := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  let _ : (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X)))).Additive := ⟨by intros; rfl⟩
  let _ : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    adj.left_adjoint_additive
  exact (adj.homAddEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The representing equivalence evaluates the original sheaf morphism on the global
integer generator. This generator is the image of `1` under the sheafification unit;
no sheaf condition on the constant presheaf is assumed. -/
theorem homGlobalSectionsAddEquiv_apply (f : ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) :
    homGlobalSectionsAddEquiv X F f = f.hom.app (op (⊤ : Opens X))
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of
          (ULift.{u} ℤ)))).app (op (⊤ : Opens X)) (ULift.up 1)) := by
  unfold homGlobalSectionsAddEquiv
  rfl

/-- A global section defines a morphism on the constant presheaf by taking integer
multiples and restricting to each open. The inverse representing morphism is exactly
its extension to the associated sheaf. -/
theorem homGlobalSectionsAddEquiv_symm_hom (s : (((sheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).obj F) :
    ((homGlobalSectionsAddEquiv X F).symm s).hom =
      sheafifyLift (Opens.grothendieckTopology X)
        (((constantPresheafAdj AddCommGrpCat.{u}
          (show IsTerminal (⊤ : Opens X) from isTerminalTop)).homEquiv (AddCommGrpCat.of (ULift.{u}
              ℤ)) F.obj).symm
            ((AddCommGrpCat.uliftZMultiplesAddEquiv ((((sheafSections (Opens.grothendieckTopology X)
                AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).obj F)).symm s)) F.property := by
  change (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)).homEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F).symm _).hom = _
  dsimp only [constantSheafAdj, constantSheaf, sheafSections]
  rw [Adjunction.comp_homEquiv]
  rfl

/-- On every open, the inverse morphism sends a local constant integer to that integer
times the restriction of the global section. The sheafification unit followed by the
extension recovers the constant-presheaf morphism, giving this component formula. -/
theorem homGlobalSectionsAddEquiv_symm_unit_app (s : (((sheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).obj F) (U : Opens X) (n : ℤ) :
    ((homGlobalSectionsAddEquiv X F).symm s).hom.app (op U)
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of
          (ULift.{u} ℤ)))).app (op U) (ULift.up n)) =
        n • F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  rw [homGlobalSectionsAddEquiv_symm_hom]
  let η := ((constantPresheafAdj AddCommGrpCat.{u}
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)).homEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F.obj).symm
        ((AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op (⊤ : Opens X)))).symm s)
  have h := congrArg (fun k => k.app (op U) (ULift.up n))
    (toSheafify_sheafifyLift (Opens.grothendieckTopology X) η F.property)
  exact h.trans (map_zsmul (F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom n s)

/-- The section-generated extension is unique: any morphism with the prescribed values
on all constant local integers agrees with it. These values identify the morphisms after
the sheafification unit, and uniqueness of extension gives equality on the associated sheaf. -/
theorem homGlobalSectionsAddEquiv_symm_unique (s : (((sheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).obj F) (f : ((constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F)
    (h : ∀ (U : Opens X) (n : ℤ), f.hom.app (op U)
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of
          (ULift.{u} ℤ)))).app (op U) (ULift.up n)) =
        n • F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op s) :
    f = (homGlobalSectionsAddEquiv X F).symm s := by
  apply CategoryTheory.Sheaf.hom_ext
  rw [homGlobalSectionsAddEquiv_symm_hom]
  apply sheafifyLift_unique
  ext U ⟨n⟩
  exact (h U.unop n).trans
    (map_zsmul (F.obj.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom n s).symm

/-- The global-section representation is natural in the coefficient sheaf. Postcomposing
and then evaluating the global integer generator equals applying the coefficient map on
global sections after evaluation. -/
theorem homGlobalSectionsAddEquiv_naturality
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F)
        (g : F ⟶ G) :
    homGlobalSectionsAddEquiv X G (f ≫ g) =
      g.hom.app (op (⊤ : Opens X)) (homGlobalSectionsAddEquiv X F f) := by
  rw [homGlobalSectionsAddEquiv_apply, homGlobalSectionsAddEquiv_apply]
  rfl

end TopCat.ConstantSheaf
