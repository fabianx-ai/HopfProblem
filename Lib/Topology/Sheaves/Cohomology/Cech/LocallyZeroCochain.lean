/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.ShrinkableRefinement
public import Lib.Topology.Sheaves.Cohomology.Cech.CohomologySystem
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Locally zero presheaf cochains

A presheaf of abelian groups is locally zero when each section restricts to zero on some
neighborhood of every point of its domain.  On a paracompact Hausdorff space, if the value of
such a presheaf on the empty open is zero as a separate hypothesis, then every normalized Cech
cochain becomes literally zero after passage to a suitable set-valued open refinement.

This is the step which makes a locally zero cochain die after refinement in the construction of
the long exact Cech sequence.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.10
* G. E. Bredon, *Sheaf Theory*, III.4
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

universe u v

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- A presheaf of abelian groups is locally zero if every section vanishes after restriction to
some open neighborhood of each point of its domain.  This condition is intentionally independent
of the presheaf's value on the empty open. -/
def IsLocallyZero (P : TopCat.Presheaf AddCommGrpCat.{v} X) : Prop :=
  ∀ (U : Opens X) (s : P.obj (op U)) (x : X), x ∈ U →
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      P.map (homOfLE hVU).op s = 0

end TopCat.Presheaf

namespace TopologicalSpace.OpenCover

variable {X : TopCat.{u}}

private structure LocalKillingData
    {I : Type u} [LinearOrder I]
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X)
    (U : I → Opens X) (S : Shrinking U) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P U q) (x : X) where
  index : I
  openSet : Opens X
  mem_openSet : x ∈ openSet
  le_shrinking : openSet ≤ S.family index
  contains : ∀ i, x ∈ U i → openSet ≤ U i
  avoids : ∀ i, x ∉ U i →
    Disjoint (openSet : Set X) (S.family i : Set X)
  kills : ∀ (σ : OrderedSimplex I q) (hWσ : openSet ≤ σ.intersection U),
    x ∈ σ.intersection U →
      P.map (homOfLE hWσ).op (OrderedCech.π P U q σ a) = 0

private theorem exists_localKillingData
    {I : Type u} [LinearOrder I]
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X)
    (hP : P.IsLocallyZero)
    (U : I → Opens X)
    (hUfin : LocallyFinite fun i ↦ (U i : Set X))
    (S : Shrinking U) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P U q) (x : X) :
    Nonempty (LocalKillingData P U S q a x) := by
  obtain ⟨t, htx, htfinite⟩ := hUfin x
  let N : Opens X := ⟨interior t, isOpen_interior⟩
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.mpr htx
  let F : Set I := {i | ((U i : Set X) ∩ (N : Set X)).Nonempty}
  have hFfinite : F.Finite := htfinite.subset fun i hi ↦
    hi.mono (inter_subset_inter_right _ interior_subset)
  let _ : Finite F := Set.finite_coe_iff.mpr hFfinite
  obtain ⟨φ, hxVφ⟩ := S.isOpenCover.exists_mem x

  let R : Set (OrderedSimplex I q) := {σ | x ∈ σ.intersection U}
  let encode : R → (Fin (q + 1) → F) := fun σ j ↦
    ⟨σ.1 j, ⟨x, (OrderedSimplex.mem_intersection_iff U σ.1 x).mp σ.2 j, hxN⟩⟩
  have hencode : Function.Injective encode := by
    intro σ τ hστ
    apply Subtype.ext
    ext j
    exact congrArg Subtype.val (congrFun hστ j)
  let _ : Finite R := Finite.of_injective encode hencode

  choose Z hZle hxZ hZzero using fun σ : R ↦
    hP (σ.1.intersection U) (OrderedCech.π P U q σ.1 a) x σ.2
  let containing : Opens X :=
    ⨅ i : {i : F | x ∈ U i.1}, U i.1
  let avoiding : Opens X :=
    ⨅ i : {i : F | x ∉ U i.1},
      ⟨(closure (S.family i.1 : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  let zeroing : Opens X := ⨅ σ : R, Z σ
  -- The first factor is the reviewed `N_x`; in particular `W ≤ N` definitionally follows.
  let W : Opens X :=
    N ⊓ S.family φ ⊓ containing ⊓ avoiding ⊓ zeroing

  have hxContaining : x ∈ containing := by
    dsimp only [containing]
    change x ∈ ((↑(⨅ i : {i : F | x ∈ U i.1}, U i.1)) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i ↦ i.2
  have hxAvoiding : x ∈ avoiding := by
    dsimp only [avoiding]
    change x ∈ ((↑(⨅ i : {i : F | x ∉ U i.1},
      (⟨(closure (S.family i.1 : Set X))ᶜ,
        isClosed_closure.isOpen_compl⟩ : Opens X))) : Set X)
    rw [Opens.coe_iInf]
    apply Set.mem_iInter.mpr
    intro i
    exact fun hxi ↦ i.2 (S.closure_subset i.1 hxi)
  have hxZeroing : x ∈ zeroing := by
    dsimp only [zeroing]
    change x ∈ ((↑(⨅ σ : R, Z σ)) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxZ
  have hxW : x ∈ W := by
    exact ⟨⟨⟨⟨hxN, hxVφ⟩, hxContaining⟩, hxAvoiding⟩, hxZeroing⟩
  have hWN : W ≤ N := by
    simp only [W]
    exact (((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_left)
  have hWVφ : W ≤ S.family φ := by
    simp only [W]
    exact (((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_right)
  have hWcontaining : W ≤ containing := by
    simp only [W]
    exact ((inf_le_left.trans inf_le_left).trans inf_le_right)
  have hWavoiding : W ≤ avoiding := by
    simp only [W]
    exact (inf_le_left.trans inf_le_right)
  have hWzeroing : W ≤ zeroing := by
    simp only [W]
    exact inf_le_right

  refine ⟨{
    index := φ
    openSet := W
    mem_openSet := hxW
    le_shrinking := hWVφ
    contains := ?_
    avoids := ?_
    kills := ?_
  }⟩
  · intro i hxi
    have hiF : i ∈ F := ⟨x, hxi, hxN⟩
    let i' : {i : F | x ∈ U i.1} := ⟨⟨i, hiF⟩, hxi⟩
    exact hWcontaining.trans (iInf_le _ i')
  · intro i hxi
    by_cases hiF : i ∈ F
    · let i' : {i : F | x ∉ U i.1} := ⟨⟨i, hiF⟩, hxi⟩
      have hWcompl : W ≤
          ⟨(closure (S.family i : Set X))ᶜ, isClosed_closure.isOpen_compl⟩ :=
        hWavoiding.trans (iInf_le _ i')
      apply Set.disjoint_left.mpr
      intro y hyW hyV
      exact hWcompl hyW (subset_closure hyV)
    · apply Set.disjoint_left.mpr
      intro y hyW hyV
      apply hiF
      exact ⟨y, S.refinement.le i hyV, hWN hyW⟩
  · intro σ hWσ hxσ
    let σ' : R := ⟨σ, hxσ⟩
    have hWZ : W ≤ Z σ' := hWzeroing.trans (iInf_le _ σ')
    have hmaps :
        (homOfLE hWσ).op = (homOfLE (hZle σ')).op ≫ (homOfLE hWZ).op := by
      subsingleton
    rw [hmaps, P.map_comp]
    simp only [ConcreteCategory.comp_apply]
    rw [hZzero σ']
    exact map_zero _

private theorem refinementMapDegree_comp_apply
    {I J K : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X)
    {U : I → Opens X} {V : J → Opens X} {W : K → Opens X}
    (r : Refinement V U) (s : Refinement W V) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P U q) :
    OrderedCech.refinementMapDegree P (r.comp s) q a =
      OrderedCech.refinementMapDegree P s q
        (OrderedCech.refinementMapDegree P r q a) := by
  have h := congrArg (fun f ↦ f.f q) (OrderedCech.refinementMap_comp P r s)
  simpa only [OrderedCech.refinementMap_f, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h a

private theorem exists_pointIndexed_refinement_pullback_eq_zero
    {I : Type u} [LinearOrder I] [LinearOrder X]
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X)
    (hP : P.IsLocallyZero) (hPempty : IsZero (P.obj (op (⊥ : Opens X))))
    (U : I → Opens X) (hUfin : LocallyFinite fun i ↦ (U i : Set X))
    (S : Shrinking U) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P U q) :
    ∃ (W : X → Opens X) (_hW : TopologicalSpace.IsOpenCover W)
      (r : Refinement W U), OrderedCech.refinementMapDegree P r q a = 0 := by
  let D : ∀ x : X, LocalKillingData P U S q a x := fun x ↦
    Classical.choice (exists_localKillingData P hP U hUfin S q a x)
  let W : X → Opens X := fun x ↦ (D x).openSet
  have hW : TopologicalSpace.IsOpenCover W := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro x _
    apply Opens.mem_iSup.mpr
    exact ⟨x, (D x).mem_openSet⟩
  let r : Refinement W U := {
    index := fun x ↦ (D x).index
    le := fun x ↦ (D x).le_shrinking.trans (S.refinement.le (D x).index)
  }
  refine ⟨W, hW, r, ?_⟩
  apply (Limits.Concrete.productEquiv
    (fun τ : OrderedSimplex X q ↦ P.obj (op (τ.intersection W)))).injective
  funext τ
  simp only [Limits.Concrete.productEquiv_apply_apply]
  rw [map_zero]
  change OrderedCech.π P W q τ
      (OrderedCech.refinementMapDegree P r q a) = 0
  rw [← ConcreteCategory.comp_apply, OrderedCech.refinementMapDegree_π]
  by_cases hrepeat : ¬ Function.Injective (r.index ∘ τ)
  · rw [OrderedCech.alternatingEvaluation_of_not_injective P U q _ hrepeat]
    simp
  · have hf : Function.Injective (r.index ∘ τ) := not_not.mp hrepeat
    by_cases hT : ((τ.intersection W : Opens X) : Set X).Nonempty
    · obtain ⟨z, hz⟩ := hT
      let x₀ : X := τ 0
      have hx₀U : ∀ j, x₀ ∈ U (r.index (τ j)) := by
        intro j
        by_contra hx
        have hdisjoint := (D x₀).avoids (r.index (τ j)) hx
        apply (Set.disjoint_left.mp hdisjoint)
        · exact (OrderedSimplex.mem_intersection_iff W τ z).mp hz 0
        · exact (D (τ j)).le_shrinking
            ((OrderedSimplex.mem_intersection_iff W τ z).mp hz j)
      let σ : OrderedSimplex I q :=
        IndexTuple.sortedSimplex (r.index ∘ τ) hf
      have hx₀σ : x₀ ∈ σ.intersection U := by
        rw [OrderedSimplex.mem_intersection_iff]
        intro j
        exact hx₀U (Tuple.sort (r.index ∘ τ) j)
      have hWx₀σ : W x₀ ≤ σ.intersection U := by
        apply le_iInf
        intro j
        exact (D x₀).contains _ (hx₀U (Tuple.sort (r.index ∘ τ) j))
      have hTx₀ : τ.intersection W ≤ W x₀ :=
        τ.intersection_le W 0
      have hkill :
          P.map (homOfLE hWx₀σ).op (OrderedCech.π P U q σ a) = 0 :=
        (D x₀).kills σ hWx₀σ hx₀σ
      have hmaps :
          eqToHom (congrArg op
              (IndexTuple.sortedSimplex_intersection U (r.index ∘ τ) hf)) ≫
              (r.orderedIntersectionHom τ).op =
            (homOfLE hWx₀σ).op ≫ (homOfLE hTx₀).op := by
        subsingleton
      rw [OrderedCech.alternatingEvaluation_of_injective P U q _ hf]
      rw [Preadditive.zsmul_comp]
      simp only [Category.assoc]
      rw [← P.map_comp, hmaps, P.map_comp]
      change (Equiv.Perm.sign (Tuple.sort (r.index ∘ τ)) : ℤ) •
        P.map (homOfLE hTx₀).op
          (P.map (homOfLE hWx₀σ).op (OrderedCech.π P U q σ a)) = 0
      rw [hkill, map_zero, smul_zero]
    · have hTbot : τ.intersection W = ⊥ := by
        apply SetLike.coe_injective
        exact Set.not_nonempty_iff_eq_empty.mp hT
      have hzero : IsZero (P.obj (op (τ.intersection W))) := by
        rw [hTbot]
        exact hPempty
      have hzeroMap :
          OrderedCech.alternatingEvaluation P U q (r.index ∘ τ) ≫
              P.map (r.orderedIntersectionHom τ).op = 0 :=
        hzero.eq_zero_of_tgt _
      rw [hzeroMap]
      rfl

namespace SetOpenCover

/-- Every normalized cochain with values in a locally zero presheaf which is separately zero on
the empty open becomes literally zero on a set-valued open refinement.  The returned refinement
retains the chosen assignment needed for the cochain pullback. -/
theorem exists_refinement_pullback_eq_zero_of_isLocallyZero_of_isZero_empty
    [ParacompactSpace X] [T2Space X]
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X)
    (hP : P.IsLocallyZero) (hPempty : IsZero (P.obj (op (⊥ : Opens X))))
    (A : SetOpenCover X) (q : ℕ)
    (a : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P A.family q) :
    ∃ (W : SetOpenCover X) (r : Refinement W.family A.family),
      OrderedCech.refinementMapDegree P r q a = 0 := by
  -- The proof uses a locally finite refinement `U` and a shrinking `V`.  At each point `x`,
  -- local finiteness supplies an open neighborhood `N_x` and a finite incidence set `F_x`.  The
  -- constructed open `W_x` has `N_x` as an explicit intersection factor, hence `W_x ⊆ N_x`.  For
  -- indices inside `F_x` it uses the relevant cover member or the complement of the closure of
  -- its shrinking; for indices outside `F_x` the containment `W_x ⊆ N_x` gives the required
  -- avoidance.  Finally it intersects the finitely many local-vanishing neighborhoods for the
  -- relevant ordered simplices.
  --
  -- For a fine simplex, repeated target indices vanish by normalized alternation.  With distinct
  -- targets and nonempty fine intersection, the avoidance property reduces the component to one
  -- of the chosen local restrictions.  With distinct targets and empty fine intersection, the
  -- separate empty-open `IsZero` hypothesis applies.  The point-indexed family is then replaced
  -- by its range, retaining a chosen refinement assignment into the original cover.
  obtain ⟨R⟩ := A.exists_isLocallyFinite_shrinkable_refinement
  let rAU : Refinement R.fine.family A.family := refinementOfLE R.refines
  let b : OrderedCech.object (A := AddCommGrpCat.{max u v}) (X := X) P R.fine.family q :=
    OrderedCech.refinementMapDegree P rAU q a
  let _ : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨W, hW, rWU, hb⟩ :=
    exists_pointIndexed_refinement_pullback_eq_zero
      P hP hPempty R.fine.family R.locallyFinite R.shrinking q b
  let Wset : SetOpenCover X := rangeCover W hW
  let rSetW : Refinement Wset.family W :=
    rangeCoverRefinement W hW (Refinement.refl W)
  let rSetA : Refinement Wset.family A.family := (rAU.comp rWU).comp rSetW
  refine ⟨Wset, rSetA, ?_⟩
  calc
    OrderedCech.refinementMapDegree P rSetA q a =
        OrderedCech.refinementMapDegree P rSetW q
          (OrderedCech.refinementMapDegree P (rAU.comp rWU) q a) :=
      refinementMapDegree_comp_apply P (rAU.comp rWU) rSetW q a
    _ = OrderedCech.refinementMapDegree P rSetW q
          (OrderedCech.refinementMapDegree P rWU q
            (OrderedCech.refinementMapDegree P rAU q a)) := by
      rw [refinementMapDegree_comp_apply P rAU rWU q a]
    _ = 0 := by
      change OrderedCech.refinementMapDegree P rSetW q
        (OrderedCech.refinementMapDegree P rWU q b) = 0
      rw [hb]
      exact map_zero _

end SetOpenCover

end TopologicalSpace.OpenCover
