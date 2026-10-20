/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.DependentFunctionSheaf
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The Godement flasque envelope

For an additive sheaf `F` on a topological space, its Godement envelope has, over an open `U`,
all dependent functions assigning to `x : U` an element of the stalk `Fₓ`.  The germ map embeds
`F` into this flasque sheaf.  This is the first, topology-independent step in the canonical
Godement resolution.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SheafCohomology.Godement

universe u

variable {X : TopCat.{u}}

/-- The fibre of the Godement envelope at `x` is the stalk of `F` at `x`. -/
abbrev stalkFiber (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) : AddCommGrpCat.{u} :=
  F.presheaf.stalk x

/-- The flasque sheaf of arbitrary functions from points to the corresponding stalks of `F`. -/
def envelope (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.DependentFunctionSheaf.sheaf X (stalkFiber F)

/-- The presheaf morphism sending a section to its family of germs. -/
def germEmbeddingPresheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ (envelope F).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ U.unop x.1 x.2 s
      map_zero' := by
        funext x
        exact map_zero _
      map_add' := by
        intro s t
        funext x
        exact map_add _ _ _ }
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    ext s
    funext x
    exact F.presheaf.germ_res_apply' i x.1 x.2 s

/-- The Godement germ embedding of a sheaf into its flasque envelope. -/
def germEmbedding (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F ⟶ envelope F :=
  ObjectProperty.homMk (germEmbeddingPresheaf F)

@[simp]
theorem germEmbedding_app_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ) (s : F.presheaf.obj U) (x : U.unop) :
    (germEmbedding F).hom.app U s x = F.presheaf.germ U.unop x.1 x.2 s := rfl

/-- A section is determined by its image in the Godement envelope. -/
theorem germEmbedding_app_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ) :
    Function.Injective ((germEmbedding F).hom.app U) := by
  intro s t hst
  apply TopCat.Presheaf.section_ext F U.unop s t
  intro x hx
  exact congrFun hst ⟨x, hx⟩

/-- The germ map into the Godement envelope is a monomorphism of sheaves. -/
instance germEmbedding_mono (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Mono (germEmbedding F) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  exact germEmbedding_app_injective F U

/-- The Godement envelope is flasque. -/
instance envelope_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (envelope F).IsFlasque := by
  change (TopCat.DependentFunctionSheaf.sheaf X (stalkFiber F)).IsFlasque
  infer_instance

end TopCat.SheafCohomology.Godement
