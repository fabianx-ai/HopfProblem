/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Homology-sequence maps under extension of a complex

Extending a homological complex along an embedding identifies its cycles and opcycles in every
degree in the image of the embedding.  This file proves that those identifications carry the
map from opcycles to cycles to the corresponding map of the original complex.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace HomologicalComplex

universe v u

variable {ι ι' : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The cycles and opcycles identifications for an extended homological complex intertwine the
canonical map from opcycles in one degree to cycles in another. -/
@[reassoc]
lemma extend_opcyclesToCycles (K : HomologicalComplex C c) (e : c.Embedding c')
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j')
    [K.HasHomology i] [K.HasHomology j]
    [(K.extend e).HasHomology i'] [(K.extend e).HasHomology j'] :
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj).hom =
      (K.extendOpcyclesIso e hi).hom ≫ K.opcyclesToCycles i j := by
  apply (cancel_mono (K.iCycles j)).1
  apply (cancel_epi ((K.extend e).pOpcycles i')).1
  simp only [Category.assoc, extendCyclesIso_hom_iCycles,
    pOpcycles_extendOpcyclesIso_hom_assoc,
    pOpcycles_opcyclesToCycles_iCycles_assoc]
  rw [K.extend_d_eq e hi hj]
  simp

end HomologicalComplex
