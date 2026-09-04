/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Stalks

/-!
# Lifting one sheaf section from stalkwise lifts

A section which belongs locally to the image of a sheaf morphism belongs globally to the image
when the morphism is stalkwise injective.  This is the one-section form of the familiar fact that
compatible local lifts glue uniquely.  Unlike a stalkwise-surjectivity criterion, it asks for
local lifts only of the displayed section.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {X : TopCat.{v}}
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [HasLimits C] [HasColimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

/-- If a section has a preimage in every stalk and the stalk maps are injective, its local
preimages glue to a global preimage. -/
theorem exists_preimage_of_stalkwise_mem_range
    {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (t : ToType (G.obj.obj (op U)))
    (hinj : ∀ x ∈ U, Function.Injective
      ((Presheaf.stalkFunctor C x).map f.hom))
    (hrange : ∀ (x : X) (hx : x ∈ U), G.presheaf.germ U x hx t ∈
      Set.range ((Presheaf.stalkFunctor C x).map f.hom)) :
    ∃ s : ToType (F.obj.obj (op U)), f.hom.app (op U) s = t := by
  have hlocal : ∀ x : U,
      ∃ (V : Opens X) (_ : x.1 ∈ V) (iVU : V ⟶ U)
        (s : ToType (F.obj.obj (op V))),
        f.hom.app (op V) s = G.presheaf.map iVU.op t := by
    intro x
    obtain ⟨s₀, hs₀⟩ := hrange x.1 x.2
    obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.presheaf.exists_germ_eq s₀
    rw [← hs₁, Presheaf.stalkFunctor_map_germ_apply] at hs₀
    obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ :=
      G.presheaf.germ_eq x.1 hxV₁ x.2 (f.hom.app (op V₁) s₁) t hs₀
    refine ⟨V₂, hxV₂, iV₂U, F.presheaf.map iV₂V₁.op s₁, ?_⟩
    rw [← ConcreteCategory.comp_apply, f.hom.naturality,
      ConcreteCategory.comp_apply, heq]
  choose V mV iVU sf heq using hlocal
  have V_cover : U ≤ iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V sf := by
    intro x y
    apply TopCat.Presheaf.section_ext F
    intro z hz
    apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
    rw [Presheaf.stalkFunctor_map_germ_apply,
      Presheaf.stalkFunctor_map_germ_apply]
    simp_rw [← ConcreteCategory.comp_apply, f.hom.naturality,
      ConcreteCategory.comp_apply, heq, ← ConcreteCategory.comp_apply,
      ← G.presheaf.map_comp]
    rfl
  obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf hcompat
  refine ⟨s, ?_⟩
  apply G.eq_of_locally_eq' V U iVU V_cover
  intro x
  rw [← ConcreteCategory.comp_apply, ← f.hom.naturality,
    ConcreteCategory.comp_apply, s_spec, heq]

end TopCat.Sheaf
