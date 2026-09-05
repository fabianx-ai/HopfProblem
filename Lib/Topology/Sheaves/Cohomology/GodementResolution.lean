/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.AcyclicResolution
public import Lib.Topology.Sheaves.Cohomology.FlasqueAcyclic
public import Lib.Topology.Sheaves.Cohomology.GodementEnvelope

/-!
# The canonical Godement resolution

Iterating the cokernel of the germ embedding produces short exact sequences

`0 ⟶ Zⁿ ⟶ Cⁿ ⟶ Zⁿ⁺¹ ⟶ 0`,

where every `Cⁿ` is a flasque dependent-function sheaf.  This file packages those sequences
as the indexed acyclic-resolution API used by the sheaf-cohomology comparison.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace TopCat.SheafCohomology.Godement

universe u

variable {X : TopCat.{u}}

/-- Successive cokernels in the Godement resolution. -/
def remainder (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ℕ → TopCat.Sheaf AddCommGrpCat.{u} X
  | 0 => F
  | n + 1 => cokernel (germEmbedding (remainder F n))

@[simp]
theorem remainder_zero (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    remainder F 0 = F := rfl

@[simp]
theorem remainder_succ (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    remainder F (n + 1) = cokernel (germEmbedding (remainder F n)) := rfl

/-- The canonical indexed Godement resolution of an additive sheaf. -/
def resolution (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Ext.AcyclicResolution (C := TopCat.Sheaf AddCommGrpCat.{u} X) where
  Z := remainder F
  X n := envelope (remainder F n)
  i n := germEmbedding (remainder F n)
  p n := cokernel.π (germEmbedding (remainder F n))
  zero n := cokernel.condition (germEmbedding (remainder F n))
  shortExact n := by
    let f := germEmbedding (remainder F n)
    change (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact
    exact { exact := ShortComplex.exact_cokernel f }

@[simp]
theorem resolution_Z (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (resolution F).Z n = remainder F n := rfl

@[simp]
theorem resolution_X (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (resolution F).X n = envelope (remainder F n) := rfl

@[simp]
theorem resolution_i (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (resolution F).i n = germEmbedding (remainder F n) := rfl

@[simp]
theorem resolution_p (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (resolution F).p n = cokernel.π (germEmbedding (remainder F n)) := rfl

/-- Every term of the canonical Godement resolution is flasque. -/
instance resolution_term_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((resolution F).X n).IsFlasque := by
  change (envelope (remainder F n)).IsFlasque
  infer_instance

section Small

variable {X : TopCat.{0}}

/-- The canonical Godement resolution is acyclic for global sections. -/
theorem resolution_isAcyclic (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    TopCat.SheafCohomology.AcyclicResolution.IsAcyclic (resolution F) := by
  intro i q hq
  exact TopCat.SheafCohomology.subsingleton_h_of_isFlasque
    ((resolution F).X i) q hq

/-- Native positive-degree sheaf cohomology is computed by the global Godement complex. -/
def cohomologyIsoGlobalHomology (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} F (n + 1)) ≅
      (TopCat.SheafCohomology.AcyclicResolution.globalComplex (resolution F)).homology
        (n + 1) :=
  TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology
    (resolution F) (resolution_isAcyclic F) n

end Small

end TopCat.SheafCohomology.Godement
