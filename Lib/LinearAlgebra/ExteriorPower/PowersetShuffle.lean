/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module


public import Mathlib.Order.Hom.PowersetCard

/-!
# Ordered values of powerset shuffles

These lemmas expose how the permutation used to multiply ordered exterior basis vectors acts on
the left and right blocks. They make small shuffle-sign certificates kernel-reducible without a
native evaluation oracle.
-/

@[expose] public section

namespace Set.powersetCard

theorem orderIsoOfFin_permOfDisjoint_castAdd {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val) (i : Fin m) :
    (orderIsoOfFin (disjUnion h) (permOfDisjoint h (Fin.castAdd n i))).val =
      (orderIsoOfFin s i).val := by
  unfold permOfDisjoint disjUnion
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd]
  have hsum :
      (↑((orderIsoOfFin s).sumCongr (orderIsoOfFin t)) :
          (Fin m ⊕ Fin n) ≃ (s.val ⊕ t.val)) (Sum.inl i) =
        Sum.inl (orderIsoOfFin s i) := rfl
  rw [hsum, Equiv.Finset.disjUnionEquiv_inl]
  exact congrArg Subtype.val ((orderIsoOfFin (disjUnion h)).apply_symm_apply _)

theorem orderIsoOfFin_permOfDisjoint_natAdd {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val) (i : Fin n) :
    (orderIsoOfFin (disjUnion h) (permOfDisjoint h (Fin.natAdd m i))).val =
      (orderIsoOfFin t i).val := by
  unfold permOfDisjoint disjUnion
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd]
  have hsum :
      (↑((orderIsoOfFin s).sumCongr (orderIsoOfFin t)) :
          (Fin m ⊕ Fin n) ≃ (s.val ⊕ t.val)) (Sum.inr i) =
        Sum.inr (orderIsoOfFin t i) := rfl
  rw [hsum, Equiv.Finset.disjUnionEquiv_inr]
  exact congrArg Subtype.val ((orderIsoOfFin (disjUnion h)).apply_symm_apply _)

/-- Identify a powerset shuffle by checking its ordered values separately on the two blocks. -/
theorem permOfDisjoint_eq {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val)
    (e : Equiv.Perm (Fin (m + n)))
    (hleft : ∀ i : Fin m,
      (orderIsoOfFin (disjUnion h) (e (Fin.castAdd n i))).val = (orderIsoOfFin s i).val)
    (hright : ∀ i : Fin n,
      (orderIsoOfFin (disjUnion h) (e (Fin.natAdd m i))).val = (orderIsoOfFin t i).val) :
    permOfDisjoint h = e := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := m) (n := n) ?_ ?_ i
  · intro j
    apply (orderIsoOfFin (disjUnion h)).injective
    apply Subtype.ext
    exact (orderIsoOfFin_permOfDisjoint_castAdd h j).trans (hleft j).symm
  · intro j
    apply (orderIsoOfFin (disjUnion h)).injective
    apply Subtype.ext
    exact (orderIsoOfFin_permOfDisjoint_natAdd h j).trans (hright j).symm

/-- Identify a powerset shuffle from explicit ordered enumerations of the two blocks and their
union. -/
theorem permOfDisjoint_eq_of_orderEmbOfFin {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val)
    (fs : Fin m → I) (ft : Fin n → I) (fu : Fin (m + n) → I)
    (hs : fs = s.val.orderEmbOfFin s.prop)
    (ht : ft = t.val.orderEmbOfFin t.prop)
    (hu : fu = (disjUnion h).val.orderEmbOfFin (disjUnion h).prop)
    (e : Equiv.Perm (Fin (m + n)))
    (hleft : ∀ i : Fin m, fu (e (Fin.castAdd n i)) = fs i)
    (hright : ∀ i : Fin n, fu (e (Fin.natAdd m i)) = ft i) :
    permOfDisjoint h = e := by
  apply permOfDisjoint_eq h e
  · intro i
    change (disjUnion h).val.orderEmbOfFin (disjUnion h).prop (e (Fin.castAdd n i)) =
      s.val.orderEmbOfFin s.prop i
    rw [← hu, ← hs]
    exact hleft i
  · intro i
    change (disjUnion h).val.orderEmbOfFin (disjUnion h).prop (e (Fin.natAdd m i)) =
      t.val.orderEmbOfFin t.prop i
    rw [← hu, ← ht]
    exact hright i

end Set.powersetCard
