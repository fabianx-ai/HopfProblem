/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.OpenCover

/-!
# Ordered indices and intersections for normalized Čech cochains

This file supplies the index, intersection, and face scaffolding for the strictly-increasing
fixed-open-cover Čech model in textbook section CD-04. A degree-`n` index is an order embedding
`Fin (n + 1) ↪o ι`, which is exactly a tuple `i₀ < ... < iₙ`. Its associated open is the
intersection of those cover members. Deleting a vertex gives a face, and the inclusion of the
full intersection into a face intersection gives the restriction direction used by Čech
cofaces.

Only this scaffolding is constructed here. In particular, this file does not identify the
ordered model with Mathlib's all-tuples `CategoryTheory.cechComplexFunctor`, and it introduces
no refinement maps, direct limits, or comparison with derived sheaf cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory

universe u v

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} [LinearOrder ι]

/-- CD-04's strictly increasing degree-`n` index tuple `i₀ < ... < iₙ`. -/
abbrev OrderedSimplex (ι : Type v) [LinearOrder ι] (n : ℕ) : Type v :=
  Fin (n + 1) ↪o ι

namespace OrderedSimplex

variable {n : ℕ}

/-- CD-04's `k`th face, obtained by deleting the `k`th entry of an ordered tuple. -/
def face (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    OrderedSimplex ι n :=
  (Fin.succAboveOrderEmb k).trans σ

/-- CD-04's deletion face evaluates by skipping the deleted position. -/
@[simp]
theorem face_apply (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2))
    (j : Fin (n + 1)) :
    σ.face k j = σ (k.succAbove j) :=
  rfl

/-- CD-04's face coherence: deleting two entries in either order gives the same ordered tuple,
with the second pair of positions adjusted by `predAbove` and `succAbove`. -/
theorem face_face_swap (σ : OrderedSimplex ι (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 3)) :
    (σ.face j).face i =
      (σ.face (j.succAbove i)).face (i.predAbove j) := by
  ext k
  exact congrFun (Fin.removeNth_removeNth_eq_swap (fun a => σ a) i j) k

/-- CD-04's open `U_{i₀} ∩ ... ∩ U_{iₙ}` associated to an ordered index tuple. -/
def intersection (U : ι → TopologicalSpace.Opens X) (σ : OrderedSimplex ι n) :
    TopologicalSpace.Opens X :=
  ⨅ j, U (σ j)

/-- CD-04's ordered open intersection has the expected underlying set. -/
@[simp]
theorem coe_intersection (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) :
    ((σ.intersection U : TopologicalSpace.Opens X) : Set X) =
      ⋂ j, (U (σ j) : Set X) :=
  TopologicalSpace.Opens.coe_iInf _

/-- CD-04's pointwise membership criterion for an ordered open intersection. -/
@[simp]
theorem mem_intersection_iff (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) (x : X) :
    x ∈ σ.intersection U ↔ ∀ j, x ∈ U (σ j) := by
  change x ∈ ((σ.intersection U : TopologicalSpace.Opens X) : Set X) ↔ _
  rw [coe_intersection]
  exact Set.mem_iInter

/-- CD-04's ordered intersection is contained in each indexed cover member. -/
theorem intersection_le (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) (j : Fin (n + 1)) :
    σ.intersection U ≤ U (σ j) :=
  iInf_le _ j

/-- CD-04's full intersection is contained in every face intersection. -/
theorem intersection_le_face (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    σ.intersection U ≤ (σ.face k).intersection U := by
  apply le_iInf
  intro j
  exact σ.intersection_le U (k.succAbove j)

/-- CD-04's inclusion from a full ordered intersection to a face intersection. After applying a
presheaf contravariantly, this is the restriction map occurring in the `k`th Čech coface. -/
def faceHom (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    σ.intersection U ⟶ (σ.face k).intersection U :=
  CategoryTheory.homOfLE (σ.intersection_le_face U k)

end OrderedSimplex

end TopologicalSpace.OpenCover
