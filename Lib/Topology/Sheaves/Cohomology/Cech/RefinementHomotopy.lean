/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.Refinement
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Prism homotopies between Čech refinement maps

This file continues textbook section CD-04 by constructing the standard prism homotopy between
the normalized Čech cochain maps induced by two choices of refinement function.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s

namespace TopologicalSpace.OpenCover

namespace IndexTuple

variable {ι : Type v} {κ : Type w}
variable {n : ℕ}

/-- The `k`th prism tuple joining two index tuples.  It lists the first tuple through
position `k`, then the second tuple from position `k` onward, repeating the pivot vertex. -/
def prism (f g : Fin (n + 1) → ι) (k : Fin (n + 1)) : Fin (n + 2) → ι :=
  fun j ↦
    if h : j.val ≤ k.val then
      f ⟨j.val, Nat.lt_of_le_of_lt h k.isLt⟩
    else
      g ⟨j.val - 1, by omega⟩

/-- The first face of the first prism tuple is the second endpoint tuple. -/
@[simp]
theorem face_prism_zero_zero (f g : Fin (n + 1) → ι) :
    IndexTuple.face (prism f g 0) 0 = g := by
  funext j
  simp [IndexTuple.face, prism]

/-- The last face of the last prism tuple is the first endpoint tuple. -/
@[simp]
theorem face_prism_last_last (f g : Fin (n + 1) → ι) :
    IndexTuple.face (prism f g (Fin.last n)) (Fin.last (n + 1)) = f := by
  funext j
  simp only [IndexTuple.face, Function.comp_apply, Fin.succAbove_last_apply, prism,
    Fin.val_castSucc, Fin.val_last]
  split_ifs <;> grind (splits := 20) [Fin.ext_iff]

/-- A face before the prism pivot commutes with the prism construction, with the pivot shifted
down by one. -/
theorem face_prism_succ_of_le (f g : Fin (n + 2) → ι)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    IndexTuple.face (prism f g j.succ) i.castSucc =
      prism (IndexTuple.face f i) (IndexTuple.face g i) j := by
  funext a
  simp only [IndexTuple.face, Function.comp_apply, prism, Fin.succAbove, Fin.val_succ]
  split_ifs <;> grind (splits := 20) [Fin.ext_iff]

/-- The two faces straddling adjacent prism pivots agree. -/
theorem face_prism_succ_eq_face_prism_castSucc (f g : Fin (n + 2) → ι)
    (j : Fin (n + 1)) :
    IndexTuple.face (prism f g j.succ) j.castSucc.succ =
      IndexTuple.face (prism f g j.castSucc) j.castSucc.succ := by
  funext a
  simp only [IndexTuple.face, Function.comp_apply, prism, Fin.succAbove, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> grind (splits := 20) [Fin.ext_iff]

/-- A face after the prism pivot commutes with the prism construction. -/
theorem face_prism_castSucc_of_lt (f g : Fin (n + 2) → ι)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    IndexTuple.face (prism f g j.castSucc) i.succ =
      prism (IndexTuple.face f i) (IndexTuple.face g i) j := by
  funext a
  simp only [IndexTuple.face, Function.comp_apply, prism, Fin.succAbove, Fin.val_castSucc]
  split_ifs <;> grind (splits := 20) [Fin.ext_iff]

variable {X : Type u} [TopologicalSpace X]

/-- A tuple is subordinate to an open when that open is contained in every member indexed by
the tuple. -/
def Subordinate (U : ι → TopologicalSpace.Opens X) (W : TopologicalSpace.Opens X)
    (f : Fin (n + 1) → ι) : Prop :=
  ∀ j, W ≤ U (f j)

/-- A subordinate open is contained in the intersection indexed by the tuple. -/
theorem Subordinate.intersection_le {U : ι → TopologicalSpace.Opens X}
    {W : TopologicalSpace.Opens X} {f : Fin (n + 1) → ι} (h : Subordinate U W f) :
    W ≤ intersection U f := by
  exact le_iInf h

/-- Subordination is preserved when an entry is deleted. -/
theorem Subordinate.face {U : ι → TopologicalSpace.Opens X}
    {W : TopologicalSpace.Opens X} {f : Fin (n + 2) → ι} (h : Subordinate U W f)
    (k : Fin (n + 2)) :
    Subordinate U W (face f k) := by
  intro j
  exact h (k.succAbove j)

/-- The prism joining two subordinate tuples is subordinate to the same open. -/
theorem Subordinate.prism {U : ι → TopologicalSpace.Opens X}
    {W : TopologicalSpace.Opens X} {f g : Fin (n + 1) → ι}
    (hf : Subordinate U W f) (hg : Subordinate U W g) (k : Fin (n + 1)) :
    Subordinate U W (prism f g k) := by
  intro j
  rw [IndexTuple.prism]
  split_ifs with h
  · exact hf ⟨j.val, Nat.lt_of_le_of_lt h k.isLt⟩
  · exact hg ⟨j.val - 1, by omega⟩

end IndexTuple

namespace Refinement

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} {κ : Type w}
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- The coarse tuple selected from an ordered fine simplex by a refinement is subordinate to
the fine simplex intersection. -/
theorem orderedSubordinate [LinearOrder κ] (r : Refinement V U) {n : ℕ}
    (sigma : OrderedSimplex κ n) :
    IndexTuple.Subordinate U (sigma.intersection V) (r.index ∘ sigma) := by
  intro j
  exact (iInf_le _ j).trans (r.le (sigma j))

end Refinement

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [Preadditive A] [HasProducts.{v} A]

/-- Alternating evaluation of a normalized Čech cochain, followed by restriction to a
subordinate open. -/
noncomputable def restrictedAlternatingEvaluation (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    (f : Fin (n + 1) → ι) (h : IndexTuple.Subordinate U W f) :
    object P U n ⟶ P.obj (op W) :=
  alternatingEvaluation P U n f ≫
    P.map (CategoryTheory.homOfLE h.intersection_le).op

/-- Restricted alternating evaluation depends on the tuple, not on the proof of
subordination. -/
theorem restrictedAlternatingEvaluation_congr (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    {f g : Fin (n + 1) → ι} (hfg : f = g)
    (hf : IndexTuple.Subordinate U W f) (hg : IndexTuple.Subordinate U W g) :
    restrictedAlternatingEvaluation P U n W f hf =
      restrictedAlternatingEvaluation P U n W g hg := by
  subst g
  rfl

/-- Restricting an alternating evaluation in two stages agrees with direct restriction. -/
@[reassoc]
theorem restrictedAlternatingEvaluation_comp_map (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    {W Z : TopologicalSpace.Opens X} (hZW : Z ≤ W)
    (f : Fin (n + 1) → ι) (hf : IndexTuple.Subordinate U W f) :
    restrictedAlternatingEvaluation P U n W f hf ≫
        P.map (CategoryTheory.homOfLE hZW).op =
      restrictedAlternatingEvaluation P U n Z f (fun j ↦ hZW.trans (hf j)) := by
  simp only [restrictedAlternatingEvaluation, Category.assoc, ← P.map_comp]
  congr 1

/-- The arbitrary-tuple coboundary formula after restriction to a subordinate open. -/
theorem differential_comp_restrictedAlternatingEvaluation (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    (f : Fin (n + 2) → ι) (hf : IndexTuple.Subordinate U W f) :
    differential P U n ≫ restrictedAlternatingEvaluation P U (n + 1) W f hf =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        restrictedAlternatingEvaluation P U n W (IndexTuple.face f k) (hf.face k) := by
  simp only [restrictedAlternatingEvaluation, ← Category.assoc]
  rw [differential_comp_alternatingEvaluation]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc, ← P.map_comp]
  apply Finset.sum_congr rfl
  intro k _
  congr 1

/-- The degree-`n` prism operator between two tuples subordinate to a common open. -/
noncomputable def prismComponent (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    (f g : Fin (n + 1) → ι) (hf : IndexTuple.Subordinate U W f)
    (hg : IndexTuple.Subordinate U W g) :
    object P U (n + 1) ⟶ P.obj (op W) :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
    restrictedAlternatingEvaluation P U (n + 1) W (IndexTuple.prism f g k)
      (hf.prism hg k)

/-- Restriction of a prism component agrees with forming it over the smaller open. -/
@[reassoc]
theorem prismComponent_comp_map (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    {W Z : TopologicalSpace.Opens X} (hZW : Z ≤ W)
    (f g : Fin (n + 1) → ι) (hf : IndexTuple.Subordinate U W f)
    (hg : IndexTuple.Subordinate U W g) :
    prismComponent P U n W f g hf hg ≫ P.map (CategoryTheory.homOfLE hZW).op =
      prismComponent P U n Z f g (fun j ↦ hZW.trans (hf j))
        (fun j ↦ hZW.trans (hg j)) := by
  simp only [prismComponent, Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [restrictedAlternatingEvaluation_comp_map]

/-- A prism component depends on its endpoint tuples, not on their presentations or the
subordination proofs. -/
theorem prismComponent_congr (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    {f f' g g' : Fin (n + 1) → ι} (hff' : f = f') (hgg' : g = g')
    (hf : IndexTuple.Subordinate U W f) (hg : IndexTuple.Subordinate U W g)
    (hf' : IndexTuple.Subordinate U W f') (hg' : IndexTuple.Subordinate U W g') :
    prismComponent P U n W f g hf hg = prismComponent P U n W f' g' hf' hg' := by
  subst f'
  subst g'
  rfl

/-- In degree zero, the coboundary of the prism is the difference of its endpoints. -/
theorem differential_comp_prismComponent_zero (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (W : TopologicalSpace.Opens X)
    (f g : Fin 1 → ι) (hf : IndexTuple.Subordinate U W f)
    (hg : IndexTuple.Subordinate U W g) :
    differential P U 0 ≫ prismComponent P U 0 W f g hf hg =
      restrictedAlternatingEvaluation P U 0 W g hg -
        restrictedAlternatingEvaluation P U 0 W f hf := by
  rw [prismComponent, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  rw [differential_comp_restrictedAlternatingEvaluation]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    IndexTuple.face_prism_zero_zero]
  have hlast : IndexTuple.face (IndexTuple.prism f g 0) 1 = f := by
    simpa using IndexTuple.face_prism_last_last f g
  rw [restrictedAlternatingEvaluation_congr P U 0 W hlast
    ((hf.prism hg 0).face 1) hf]
  abel

/-- In positive degree, the two boundary sums of the prism cancel in pairs, leaving the
difference of the endpoint evaluations. -/
theorem differential_comp_prismComponent_succ (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (W : TopologicalSpace.Opens X)
    (f g : Fin (n + 2) → ι) (hf : IndexTuple.Subordinate U W f)
    (hg : IndexTuple.Subordinate U W g) :
    differential P U (n + 1) ≫ prismComponent P U (n + 1) W f g hf hg +
        ∑ l : Fin (n + 2), (-1 : ℤ) ^ (l : ℕ) •
          prismComponent P U n W (IndexTuple.face f l) (IndexTuple.face g l)
            (hf.face l) (hg.face l) =
      restrictedAlternatingEvaluation P U (n + 1) W g hg -
        restrictedAlternatingEvaluation P U (n + 1) W f hf := by
  simp only [prismComponent, Preadditive.comp_sum, Preadditive.comp_zsmul]
  simp_rw [differential_comp_restrictedAlternatingEvaluation]
  simp only [Finset.smul_sum, smul_smul, ← pow_add]
  let alpha (x : Fin (n + 2) × Fin (n + 1)) :=
    (-1 : ℤ) ^ ((x.1 + x.2 : ℕ)) •
      restrictedAlternatingEvaluation P U (n + 1) W
        (IndexTuple.prism (IndexTuple.face f x.1) (IndexTuple.face g x.1) x.2)
        ((hf.face x.1).prism (hg.face x.1) x.2)
  let beta (x : Fin (n + 2) × Fin (n + 3)) :=
    (-1 : ℤ) ^ ((x.1 + x.2 : ℕ)) •
      restrictedAlternatingEvaluation P U (n + 1) W
        (IndexTuple.face (IndexTuple.prism f g x.1) x.2)
        ((hf.prism hg x.1).face x.2)
  change (∑ k, ∑ l, beta (k, l)) + (∑ l, ∑ k, alpha (l, k)) = _
  rw [← Finset.sum_product .univ .univ beta, ← Finset.sum_product .univ .univ alpha]
  rw [Finset.univ_product_univ, Finset.univ_product_univ]
  let S : Finset (Fin (n + 2) × Fin (n + 1)) := {x | x.2.castSucc < x.1}
  let gamma1 (x : Fin (n + 2) × Fin (n + 1)) := (x.2.succ, x.1.castSucc)
  let gamma2 (x : Fin (n + 2) × Fin (n + 1)) := (x.2.castSucc, x.1.succ)
  let gamma3 (i : Fin (n + 1)) := (i.succ, i.castSucc.succ)
  let gamma4 (i : Fin (n + 1)) := (i.castSucc, i.castSucc.succ)
  have hgamma1 : Function.Injective gamma1 := fun _ _ ↦ by aesop
  have hgamma2 : Function.Injective gamma2 := fun _ _ ↦ by aesop
  have hgamma3 : Function.Injective gamma3 := fun _ _ ↦ by aesop
  have hgamma4 : Function.Injective gamma4 := fun _ _ ↦ by aesop
  have endpoint_zero :
      restrictedAlternatingEvaluation P U (n + 1) W g hg = beta (0, 0) := by
    simp [beta]
  have endpoint_last :
      restrictedAlternatingEvaluation P U (n + 1) W f hf =
        -beta (Fin.last _, Fin.last _) := by
    dsimp [beta]
    simp only [IndexTuple.face_prism_last_last]
    have hsign : (-1 : ℤ) ^ ((n + 1) + (n + 2)) = -1 := by
      rw [show (n + 1) + (n + 2) = 2 * (n + 1) + 1 by omega, pow_add, pow_mul]
      simp
    rw [hsign, neg_one_zsmul, neg_neg]
  have cancel_before :
      ∑ x ∈ Sᶜ, alpha x = -∑ y ∈ Finset.image gamma1 Sᶜ, beta y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hgamma1.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    have hle : x.1 ≤ x.2.castSucc := by simpa [S] using hx
    dsimp [alpha, beta, gamma1]
    rw [restrictedAlternatingEvaluation_congr P U (n + 1) W
      (IndexTuple.face_prism_succ_of_le f g x.1 x.2 hle).symm
      ((hf.face x.1).prism (hg.face x.1) x.2)
      ((hf.prism hg x.2.succ).face x.1.castSucc)]
    simp only [pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  have cancel_after :
      ∑ x ∈ S, alpha x = -∑ y ∈ Finset.image gamma2 S, beta y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hgamma2.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    have hlt : x.2.castSucc < x.1 := by simpa [S] using hx
    dsimp [alpha, beta, gamma2]
    rw [restrictedAlternatingEvaluation_congr P U (n + 1) W
      (IndexTuple.face_prism_castSucc_of_lt f g x.1 x.2 hlt).symm
      ((hf.face x.1).prism (hg.face x.1) x.2)
      ((hf.prism hg x.2.castSucc).face x.1.succ)]
    simp only [pow_add, pow_one, mul_neg, mul_one, neg_smul, neg_neg]
    rw [mul_comm]
  have cancel_diagonal :
      ∑ i, beta (gamma4 i) = -∑ i, beta (gamma3 i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    dsimp [beta, gamma3, gamma4]
    rw [restrictedAlternatingEvaluation_congr P U (n + 1) W
      (IndexTuple.face_prism_succ_eq_face_prism_castSucc f g i).symm
      ((hf.prism hg i.castSucc).face i.castSucc.succ)
      ((hf.prism hg i.succ).face i.castSucc.succ)]
    simp only [pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
  have disjoint_sides :
      Disjoint (Finset.image gamma1 Sᶜ) (Finset.image gamma2 S) := by
    rw [Finset.disjoint_iff_ne]
    grind [Finset.mem_compl]
  have disjoint_diagonals :
      Disjoint (Finset.image gamma3 .univ) (Finset.image gamma4 .univ) := by
    rw [Finset.disjoint_iff_ne]
    grind
  have disjoint_diagonal_endpoints :
      Disjoint (Finset.disjUnion _ _ disjoint_diagonals)
        {(0, 0), (Fin.last _, Fin.last _)} := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_insert, forall_eq_or_imp, Prod.forall]
    rintro ⟨a, _⟩ ⟨b, _⟩
    simp
    grind
  have disjoint_sides_rest :
      Disjoint (Finset.disjUnion _ _ disjoint_sides)
        (Finset.disjUnion _ _ disjoint_diagonal_endpoints) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.disjUnion_eq_union,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.exists, ne_eq, Finset.mem_insert, Finset.mem_singleton, Prod.forall,
      Prod.mk.injEq, not_and, S, gamma1, gamma2, gamma3, gamma4]
    rintro ⟨a, _⟩ ⟨b, _⟩
      (⟨⟨j, _⟩, ⟨k, _⟩, h1, h2, h3⟩ | ⟨⟨j, _⟩, ⟨k, _⟩, h1, h2, h3⟩) _ _
      ((⟨⟨i, _⟩, h4, h5⟩ | ⟨⟨i, _⟩, h4, h5⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
        simp [Fin.ext_iff] at h1 h2 h3 ⊢ <;> grind
  have complement_sides :
      (Finset.disjUnion _ _ disjoint_sides)ᶜ =
        Finset.disjUnion _ _ disjoint_diagonal_endpoints :=
    Finset.compl_eq_of_disjoint_of_card_add_eq disjoint_sides_rest (by
      rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion,
        Finset.card_image_of_injective _ hgamma1,
        Finset.card_image_of_injective _ hgamma2,
        Finset.card_image_of_injective _ hgamma3,
        Finset.card_image_of_injective _ hgamma4]
      simp
      lia)
  rw [endpoint_zero, endpoint_last, sub_neg_eq_add,
    ← S.sum_add_sum_compl, cancel_after, cancel_before,
    ← (Finset.disjUnion _ _ disjoint_sides).sum_add_sum_compl,
    Finset.sum_disjUnion, complement_sides,
    Finset.sum_disjUnion, Finset.sum_disjUnion,
    Finset.sum_image hgamma3.injOn, Finset.sum_image hgamma4.injOn,
    Finset.sum_insert (by simp), Finset.sum_singleton, cancel_diagonal]
  abel

section RefinementHomotopy

variable {κ : Type s} [LinearOrder κ] [HasProducts.{s} A]
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- The degree-`n` prism operator associated to two refinement functions. -/
noncomputable def refinementPrismDegree (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (n : ℕ) : object P U (n + 1) ⟶ object P V n :=
  Limits.Pi.lift fun sigma ↦
    prismComponent P U n (sigma.intersection V) (r.index ∘ sigma) (q.index ∘ sigma)
      (r.orderedSubordinate sigma) (q.orderedSubordinate sigma)

/-- Component formula for the degreewise prism operator. -/
@[reassoc (attr := simp)]
theorem refinementPrismDegree_π (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (n : ℕ) (sigma : OrderedSimplex κ n) :
    refinementPrismDegree P r q n ≫ π P V n sigma =
      prismComponent P U n (sigma.intersection V) (r.index ∘ sigma) (q.index ∘ sigma)
        (r.orderedSubordinate sigma) (q.orderedSubordinate sigma) :=
  Limits.Pi.lift_π _ _

private theorem refinementPrism_face (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (n : ℕ) (sigma : OrderedSimplex κ (n + 1))
    (l : Fin (n + 2)) :
    refinementPrismDegree P r q n ≫ π P V n (sigma.face l) ≫
        P.map (sigma.faceHom V l).op =
      prismComponent P U n (sigma.intersection V)
        (IndexTuple.face (r.index ∘ sigma) l) (IndexTuple.face (q.index ∘ sigma) l)
        ((r.orderedSubordinate sigma).face l) ((q.orderedSubordinate sigma).face l) := by
  rw [refinementPrismDegree_π_assoc]
  dsimp only [OrderedSimplex.faceHom]
  rw [prismComponent_comp_map]
  apply prismComponent_congr <;> rfl

/-- The degree-zero refinement prism identity. -/
theorem differential_comp_refinementPrismDegree_zero (P : TopCat.Presheaf A X)
    (r q : Refinement V U) :
    differential P U 0 ≫ refinementPrismDegree P r q 0 =
      refinementMapDegree P q 0 - refinementMapDegree P r 0 := by
  apply Limits.Pi.hom_ext
  intro sigma
  simp only [Preadditive.sub_comp, Category.assoc]
  change differential P U 0 ≫ (refinementPrismDegree P r q 0 ≫ π P V 0 sigma) =
    (refinementMapDegree P q 0 ≫ π P V 0 sigma) -
      (refinementMapDegree P r 0 ≫ π P V 0 sigma)
  rw [refinementPrismDegree_π, refinementMapDegree_π, refinementMapDegree_π]
  exact differential_comp_prismComponent_zero P U (sigma.intersection V)
    (r.index ∘ sigma) (q.index ∘ sigma)
      (r.orderedSubordinate sigma) (q.orderedSubordinate sigma)

/-- The positive-degree refinement prism identity. -/
theorem differential_comp_refinementPrismDegree_succ (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (n : ℕ) :
    differential P U (n + 1) ≫ refinementPrismDegree P r q (n + 1) +
        refinementPrismDegree P r q n ≫ differential P V n =
      refinementMapDegree P q (n + 1) - refinementMapDegree P r (n + 1) := by
  apply Limits.Pi.hom_ext
  intro sigma
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc]
  change differential P U (n + 1) ≫
          (refinementPrismDegree P r q (n + 1) ≫ π P V (n + 1) sigma) +
      refinementPrismDegree P r q n ≫ (differential P V n ≫ π P V (n + 1) sigma) =
    (refinementMapDegree P q (n + 1) ≫ π P V (n + 1) sigma) -
      (refinementMapDegree P r (n + 1) ≫ π P V (n + 1) sigma)
  rw [refinementPrismDegree_π, refinementMapDegree_π, refinementMapDegree_π,
    differential_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, refinementPrism_face]
  exact differential_comp_prismComponent_succ P U n (sigma.intersection V)
    (r.index ∘ sigma) (q.index ∘ sigma)
      (r.orderedSubordinate sigma) (q.orderedSubordinate sigma)

/-- The sparse family of degree-lowering maps underlying the refinement homotopy. -/
noncomputable def refinementPrismHom (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (i j : ℕ) :
    (complex P U).X i ⟶ (complex P V).X j :=
  if h : j + 1 = i then
    eqToHom (by rw [complex_X, ← h]) ≫ refinementPrismDegree P r q j ≫
      eqToHom (by rw [complex_X])
  else
    0

/-- On adjacent degrees, the sparse homotopy family is the prism operator. -/
@[simp]
theorem refinementPrismHom_succ (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (n : ℕ) :
    refinementPrismHom P r q (n + 1) n = refinementPrismDegree P r q n := by
  simp [refinementPrismHom]

/-- Away from adjacent degrees, the sparse homotopy family vanishes. -/
theorem refinementPrismHom_zero (P : TopCat.Presheaf A X)
    (r q : Refinement V U) (i j : ℕ) (hij : ¬(ComplexShape.up ℕ).Rel j i) :
    refinementPrismHom P r q i j = 0 := by
  rw [refinementPrismHom, dif_neg]
  exact hij

/-- Two choices of refinement function for the same fine and coarse covers induce homotopic
morphisms of normalized ordered Čech cochain complexes. -/
noncomputable def refinementMapHomotopy (P : TopCat.Presheaf A X)
    (r q : Refinement V U) :
    Homotopy (refinementMap (U := U) (V := V) P r)
      (refinementMap (U := U) (V := V) P q) where
  hom i j := refinementPrismHom (U := U) (V := V) P q r i j
  zero i j hij := refinementPrismHom_zero (U := U) (V := V) P q r i j hij
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex]
        simp only [refinementMap_f, complex_d, refinementPrismHom_succ]
        rw [differential_comp_refinementPrismDegree_zero P q r]
        abel
    | succ n =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        simp only [refinementMap_f, complex_d, refinementPrismHom_succ]
        rw [differential_comp_refinementPrismDegree_succ P q r n]
        abel

/-- Refinement maps obtained from different refinement functions induce the same map on Čech
cohomology. -/
theorem refinementMap_homologyMap_eq [CategoryWithHomology A]
    (P : TopCat.Presheaf A X) (r q : Refinement V U) (n : ℕ) :
    HomologicalComplex.homologyMap (refinementMap (U := U) (V := V) P r) n =
      HomologicalComplex.homologyMap (refinementMap (U := U) (V := V) P q) n :=
  (refinementMapHomotopy P r q).homologyMap_eq n

end RefinementHomotopy

end OrderedCech

end TopologicalSpace.OpenCover
