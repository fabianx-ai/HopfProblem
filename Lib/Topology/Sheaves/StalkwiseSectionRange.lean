/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalkwise range criterion for sections of a mono

For a monomorphism of sheaves of abelian groups, a section lies in the image over an open set
exactly when each of its germs lies in the image of the corresponding map of stalks (Hartshorne,
*Algebraic Geometry* II Ex. 1.2; cf. Iversen, *Cohomology of Sheaves*).  The reverse implication
chooses local representatives of the stalk preimages and glues them; monicity supplies
compatibility and uniqueness on overlaps.

## Main results

* `TopCat.Presheaf.app_exists_preimage_iff_stalkwise_exists_preimage`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

universe u

variable {X : TopCat.{u}}
variable {F G : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- A section of the target of a monomorphism of sheaves of abelian groups has a preimage over an
open set if and only if its germ at every point of that open set has a preimage under the map of
stalks. -/
theorem app_exists_preimage_iff_stalkwise_exists_preimage
    (f : F ⟶ G) [Mono f] (U : Opens X)
    (t : ToType (G.presheaf.obj (op U))) :
    (∃ s : ToType (F.presheaf.obj (op U)), f.hom.app (op U) s = t) ↔
      ∀ (x : X) (hx : x ∈ U),
        ∃ sx : ToType (F.presheaf.stalk x),
          ((stalkFunctor AddCommGrpCat x).map f.hom) sx =
            G.presheaf.germ U x hx t := by
  constructor
  · rintro ⟨s, rfl⟩ x hx
    refine ⟨F.presheaf.germ U x hx s, ?_⟩
    exact stalkFunctor_map_germ_apply U x hx f.hom s
  · intro h
    have hinj : ∀ (x : X) (_hx : x ∈ U),
        Function.Injective ((stalkFunctor AddCommGrpCat x).map f.hom) := by
      intro x _hx
      let _ : Mono ((stalkFunctor AddCommGrpCat x).map f.hom) :=
        stalk_mono_of_mono f x
      exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
        inferInstance
    have hlocal : ∀ (x : X) (hx : x ∈ U),
        ∃ (V : Opens X) (_ : x ∈ V) (iVU : V ⟶ U)
          (s : ToType (F.presheaf.obj (op V))),
            f.hom.app (op V) s = G.presheaf.map iVU.op t := by
      intro x hx
      obtain ⟨sx, hsx⟩ := h x hx
      obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq sx
      rw [stalkFunctor_map_germ_apply] at hsx
      obtain ⟨W, hxW, iWV, iWU, heq⟩ :=
        G.presheaf.germ_eq x hxV hx _ _ hsx
      refine ⟨W, hxW, iWU, F.presheaf.map iWV.op s, ?_⟩
      rw [← ConcreteCategory.comp_apply, f.hom.naturality,
        ConcreteCategory.comp_apply]
      exact heq
    choose V mV iVU sf heq using fun x : U => hlocal x.1 x.2
    have V_cover : U ≤ iSup V := by
      intro x hxU
      simp only [Opens.mem_iSup]
      exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
    suffices IsCompatible F.obj V sf by
      obtain ⟨s, s_spec, -⟩ :=
        F.existsUnique_gluing' V U iVU V_cover sf this
      refine ⟨s, ?_⟩
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← ConcreteCategory.comp_apply, ← f.hom.naturality,
        ConcreteCategory.comp_apply, s_spec, heq]
    intro x y
    apply section_ext F (V x ⊓ V y)
    intro z hz
    apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
    simp_rw [← ConcreteCategory.comp_apply, f.hom.naturality,
      ConcreteCategory.comp_apply, heq, ← ConcreteCategory.comp_apply,
      ← G.1.map_comp]
    rfl

end TopCat.Presheaf
