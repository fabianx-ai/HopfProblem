/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Inserting the last index into a permutation

A permutation `E` of `Fin (n + 1)` is determined by the position `r = E.symm (Fin.last n)`
of the last index together with the permutation of `Fin n` induced on the remaining
indices. `Hurewicz.NativeSubdivision.insertPermutation e r` is the forward map of this
bijection and `Hurewicz.NativeSubdivision.deletePermutation` its inverse;
`Hurewicz.NativeSubdivision.insertPermutationEquiv n : Perm (Fin n) × Fin (n + 1) ≃ Perm (Fin (n + 1))`
packages both, and `Hurewicz.NativeSubdivision.sum_insertPermutation` reindexes a sum over
`Perm (Fin (n + 1))` as a double sum over `Perm (Fin n)` and the insertion position.

This is the recursion `S_{n+1} = S_n × (n + 1)` on the Kuhn chambers of the cube: a
chamber of the `(n + 1)`-cube is a chamber of the `n`-cube together with the slot of
the new coordinate in the order (cf. the proof of Hatcher, Theorem 4.32).

## Main definitions

* `Hurewicz.NativeSubdivision.insertPermutation`, `Hurewicz.NativeSubdivision.deletePermutation`
* `Hurewicz.NativeSubdivision.insertPermutationEquiv`

## Main results

* `Hurewicz.NativeSubdivision.insertPermutation_deletePermutation`
* `Hurewicz.NativeSubdivision.sum_insertPermutation`
-/

open Set Function

noncomputable section

/-! ### Inserting the last index -/

/-- The permutation of `Fin (n+1)` obtained by inserting the last index into `e`:
the `insertPermutationEquiv` bijection's forward map. -/
def Hurewicz.NativeSubdivision.insertPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans (e.optionCongr.trans finSuccEquivLast.symm)

/-- `insertPermutation e` applied at `e`'s insertion position gives the last index. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertPermutation_apply_at {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : insertPermutation e r r = Fin.last n := by
  simp [insertPermutation]

/-- `insertPermutation e` applied off the insertion position gives the `e`-value. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertPermutation_apply_succAbove {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r (r.succAbove j) = (e j).castSucc := by simp [insertPermutation]

/-- The inverse of `insertPermutation e` sends the last index to the insertion
position. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertPermutation_symm_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : (insertPermutation e r).symm (Fin.last n) = r := by
  apply (insertPermutation e r).injective
  simp

/-- The pair `(insertion position, e)` determines `insertPermutation e`. -/
theorem Hurewicz.NativeSubdivision.insertPermutation_pair_injective {n : ℕ} :
    Function.Injective
      (fun er : Equiv.Perm (Fin n) × Fin (n + 1) => insertPermutation er.1 er.2) := by
  rintro ⟨e, r⟩ ⟨f, s⟩ h
  have hrs : r = s := by
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E.symm (Fin.last n)) h
  subst s
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Fin.castSucc_injective n
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E (r.succAbove j)) h
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e, r)) hef

/-- Removing `none` from an `Option`-valued equivalence fixing `none`. -/
theorem Hurewicz.NativeSubdivision.optionCongr_removeNone_of_none {α β : Type*}
    (e : Option α ≃ Option β) (h : e Option.none = Option.none) : e.removeNone.optionCongr = e := by
  apply Equiv.ext
  intro a
  cases a with
  | none => simpa using h.symm
  | some a =>
    change Option.some (e.removeNone a) = e (Option.some a)
    cases ha : e (Option.some a) with
    | none =>
      have : Option.some a = Option.none := e.injective (ha.trans h.symm)
      cases this
    | some b => simpa only [ha] using e.removeNone_some ⟨b, ha⟩

/-- The `Option`-indexed permutation obtained from `E : Perm (Fin (n+1))` by
deleting the last index, as an `Option`-equivalence. -/
def Hurewicz.NativeSubdivision.deletePermutationOption {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Option (Fin n)) :=
  (finSuccEquiv' (E.symm (Fin.last n))).symm.trans (E.trans finSuccEquivLast)

/-- `deletePermutationOption E` fixes `none`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.deletePermutationOption_none {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : deletePermutationOption E Option.none = Option.none := by
  simp [deletePermutationOption]

/-- The `Fin n` permutation obtained from `E : Perm (Fin (n+1))` by deleting the
last index. -/
def Hurewicz.NativeSubdivision.deletePermutation {n : ℕ} (E : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  (deletePermutationOption E).removeNone

/-- `deletePermutation E` applied at `i` gives the `castSucc`-reduced value of `E`. -/
theorem Hurewicz.NativeSubdivision.deletePermutation_castSucc {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (deletePermutation E j).castSucc = E ((E.symm (Fin.last n)).succAbove j) := by
  have h :=
    congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (Option.some j))
      (optionCongr_removeNone_of_none (deletePermutationOption E)
        (deletePermutationOption_none E))
  have h' := congrArg finSuccEquivLast.symm h
  simpa only [deletePermutation, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquivLast_symm_some, deletePermutationOption, Equiv.trans_apply,
    finSuccEquiv'_symm_some, Equiv.symm_apply_apply] using h'

/-- Insertion and deletion are inverse operations on permutations. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertPermutation_deletePermutation {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) :
    insertPermutation (deletePermutation E) (E.symm (Fin.last n)) = E := by
  ext i
  refine Fin.succAboveCases (E.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [insertPermutation_apply_succAbove, deletePermutation_castSucc]

/-- The equivalence between `Perm (Fin (n+1))` and pairs `(insertion position,
Perm (Fin n))`. -/
def Hurewicz.NativeSubdivision.insertPermutationEquiv (n : ℕ) :
    (Equiv.Perm (Fin n) × Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1))
    where
  toFun er := insertPermutation er.1 er.2
  invFun E := (deletePermutation E, E.symm (Fin.last n))
  left_inv
    er :=
    insertPermutation_pair_injective
      (insertPermutation_deletePermutation (insertPermutation er.1 er.2))
  right_inv := insertPermutation_deletePermutation

/-- Sums over `Perm (Fin (n+1))` reindex through `insertPermutationEquiv` as sums
over positions and `Perm (Fin n)`. -/
theorem Hurewicz.NativeSubdivision.sum_insertPermutation {n : ℕ} {A : Type*}
    [AddCommMonoid A] (F : Equiv.Perm (Fin (n + 1)) → A) :
    ∑ E, F E = ∑ e : Equiv.Perm (Fin n), ∑ r : Fin (n + 1), F (insertPermutation e r) := by
  rw [← (insertPermutationEquiv n).sum_comp F, Fintype.sum_prod_type]
  rfl
