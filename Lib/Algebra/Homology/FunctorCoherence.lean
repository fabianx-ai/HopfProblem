/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.Functor

/-!
# Coherence of homology under exact functors

The canonical comparison between homology before and after applying a homology-preserving
functor is compatible with composition of functors and with natural transformations.

These are generic categorical coherence identities. They neither construct a derived functor nor
identify any geometric cohomology theory or spectral-sequence differential.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section Composition

variable {C D E : Type*}
variable [Category C] [Category D] [Category E]
variable [Abelian C] [Abelian D] [Abelian E]
variable (F : Functor C D) (G : Functor D E) [F.Additive] [G.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology comparison for a composite of homology-preserving functors is the
composite of the two individual comparisons. -/
theorem ShortComplex.mapHomologyIso_comp
    (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] [(S.map (F ⋙ G)).HasHomology]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    S.mapHomologyIso (F ⋙ G) =
      (S.map F).mapHomologyIso G ≪≫ G.mapIso (S.mapHomologyIso F) := by
  let h := S.homologyData.left
  let hF := h.map F
  let hComp := h.map (F ⋙ G)
  let hTwice : (S.map (F ⋙ G)).LeftHomologyData := hF.map G
  have hi : hComp.i = hTwice.i := by
    dsimp only [hComp, hTwice, hF, h]
    rfl
  have hcycles : hComp.cyclesIso.hom = hTwice.cyclesIso.hom := by
    rw [← cancel_mono hComp.i]
    rw [hComp.cyclesIso_hom_comp_i, hi, hTwice.cyclesIso_hom_comp_i]
  have hhomology : hComp.homologyIso.hom = hTwice.homologyIso.hom := by
    rw [← cancel_epi (S.map (F ⋙ G)).homologyπ,
      hComp.homologyπ_comp_homologyIso_hom,
      hTwice.homologyπ_comp_homologyIso_hom, hcycles]
    dsimp only [hComp, hTwice, hF, h]
    simp only [ShortComplex.LeftHomologyData.map_π]
    rfl
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq hF G]
  apply Iso.ext
  dsimp [ShortComplex.mapHomologyIso]
  rw [hhomology]
  change hTwice.homologyIso.hom =
    (hTwice.homologyIso.hom ≫ G.map hF.homologyIso.inv) ≫
      G.map hF.homologyIso.hom
  rw [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id]
  exact (Category.comp_id hTwice.homologyIso.hom).symm

end Composition

section Naturality

variable {C D : Type*}
variable [Category C] [Category D] [Abelian C] [Abelian D]
variable {F G : Functor C D} [F.Additive] [G.Additive]
variable [F.PreservesHomology] [G.PreservesHomology]

/-- Taking homology commutes with a natural transformation between homology-preserving
functors, compatibly with the canonical comparison isomorphisms. -/
theorem ShortComplex.mapHomologyIso_hom_naturality_natTrans
    (S : ShortComplex C) (τ : F ⟶ G) :
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫
      (S.mapHomologyIso G).hom =
    (S.mapHomologyIso F).hom ≫ τ.app S.homology := by
  have h := ShortComplex.homologyMap_mapNatTrans S τ
  exact (congrArg
    (fun a => a ≫ (S.mapHomologyIso G).hom) h).trans (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end Naturality

end CategoryTheory
