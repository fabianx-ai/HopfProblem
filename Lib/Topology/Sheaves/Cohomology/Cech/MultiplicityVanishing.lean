/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.CohomologySystem
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Fixed-cover Cech vanishing from multiplicity

If an indexed open family has multiplicity at most
`n + 1` and `n < a`, then the intersection attached to every strictly increasing `(a + 1)`-tuple
of indices is empty. A sheaf valued in a category with zero morphisms takes the empty open to a
zero object. Thus every factor, and hence the product defining the normalized degree-`a` Cech
cochain object, is zero. Its degree-`a` fixed-cover cohomology is consequently zero.

The guarded presheaf lemma below assumes explicitly that the presheaf takes the empty open to a
zero object. No comparison with direct-limit Cech cohomology or derived sheaf cohomology is made.

Reference: Godement, *Topologie algébrique et théorie des faisceaux*, II.5.12 (the Čech cochains
of a cover of multiplicity at most `n + 1` vanish in degrees above `n`).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} [LinearOrder ι]

namespace OrderedSimplex

/-- A multiplicity bound makes every ordered intersection in a degree above the bound empty. -/
theorem intersection_eq_bot_of_multiplicityLE {n a : ℕ}
    {U : ι → TopologicalSpace.Opens X} (hU : MultiplicityLE U (n + 1))
    (ha : n < a) (σ : OrderedSimplex ι a) :
    σ.intersection U = ⊥ := by
  apply le_antisymm
  · intro x hx
    exfalso
    have hcard := hU x (Finset.univ.map σ.toEmbedding) (by
      intro i
      obtain ⟨j, -, hji⟩ := Finset.mem_map.mp i.property
      rw [← hji]
      exact (σ.mem_intersection_iff U x).mp hx j)
    have hbound : a + 1 ≤ n + 1 := by
      simpa using hcard
    omega
  · exact bot_le

end OrderedSimplex

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [Preadditive A] [HasZeroObject A]
  [HasProducts.{v} A]

/-- If a presheaf takes the empty open to zero, multiplicity at most `n + 1` makes its
normalized degree-`a` Cech cochain object zero for every `a > n`. -/
theorem object_isZero_of_multiplicityLE (P : TopCat.Presheaf A X)
    (hP : IsZero (P.obj (op (⊥ : TopologicalSpace.Opens X)))) {n a : ℕ}
    {U : ι → TopologicalSpace.Opens X} (hU : MultiplicityLE U (n + 1))
    (ha : n < a) :
    IsZero (object P U a) := by
  apply (productIsProduct _).isZero_pt
  apply Functor.isZero
  rintro ⟨σ⟩
  change IsZero (P.obj (op (σ.intersection U)))
  rw [σ.intersection_eq_bot_of_multiplicityLE hU ha]
  exact hP

/-- For a sheaf, multiplicity at most `n + 1` makes the normalized degree-`a` Cech cochain
object zero for every `a > n`. The sheaf condition supplies the empty-open hypothesis. -/
theorem normalizedCechCochain_isZero_of_multiplicityLE (F : TopCat.Sheaf A X)
    {n a : ℕ} {U : ι → TopologicalSpace.Opens X}
    (hU : MultiplicityLE U (n + 1)) (ha : n < a) :
    IsZero (object F.presheaf U a) := by
  apply object_isZero_of_multiplicityLE F.presheaf F.isTerminalOfEmpty.isZero hU ha

variable [CategoryWithHomology A]

/-- A low-multiplicity cover has zero normalized fixed-cover Cech cohomology in every degree
above the multiplicity bound. -/
theorem homology_isZero_of_multiplicityLE (F : TopCat.Sheaf A X)
    {n a : ℕ} {U : ι → TopologicalSpace.Opens X}
    (hU : MultiplicityLE U (n + 1)) (ha : n < a) :
    IsZero ((complex F.presheaf U).homology a) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  exact normalizedCechCochain_isZero_of_multiplicityLE F hU ha

end OrderedCech

namespace SetOpenCover

variable {X : TopCat.{u}}
variable {A : Type v} [Category.{w} A] [Preadditive A] [HasZeroObject A]
  [HasProducts.{u} A] [CategoryWithHomology A]

/-- The normalized fixed-cover Cech cohomology of a set-valued cover vanishes above its
multiplicity bound. -/
theorem normalizedCechCohomology_isZero_of_multiplicityLE
    (F : TopCat.Sheaf A X) (U : SetOpenCover X) {n a : ℕ}
    (hU : MultiplicityLE U.family (n + 1)) (ha : n < a) :
    IsZero (normalizedCechCohomology F.presheaf U a) :=
  OrderedCech.homology_isZero_of_multiplicityLE F hU ha

/-- For an abelian-group-valued sheaf, the fixed-cover vanishing says that the underlying
normalized Cech cohomology group is a subsingleton. -/
theorem normalizedCechCohomology_subsingleton_of_multiplicityLE
    [HasProducts.{u} AddCommGrpCat.{v}]
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (U : SetOpenCover X) {n a : ℕ}
    (hU : MultiplicityLE U.family (n + 1)) (ha : n < a) :
    Subsingleton
      (normalizedCechCohomology (A := AddCommGrpCat.{v}) F.presheaf U a) :=
  AddCommGrpCat.subsingleton_of_isZero
    (normalizedCechCohomology_isZero_of_multiplicityLE
      (A := AddCommGrpCat.{v}) F U hU ha)

end SetOpenCover

end TopologicalSpace.OpenCover
