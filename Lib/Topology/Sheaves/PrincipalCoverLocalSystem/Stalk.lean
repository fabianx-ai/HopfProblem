/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.PrincipalCoverLocalSystem
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of principal-cover local systems

The stalk of the local system associated with a principal `G`-cover `p : E → X` and a `G`-module
`M` is `M` at every point: a choice of lift `e ∈ p⁻¹(x)` identifies the stalk at `x` with the
coefficient group by evaluating germs of equivariant sections at `e` (Whitehead, *Elements of
Homotopy Theory*, VI.1).  Changing the lift by a deck transformation `g` changes the
identification by the action of `g` on `M`.

## Main results

* `stalkEvaluation`: evaluation of a germ at a chosen lift.
* `stalkEvaluation_bijective`, `stalkIsoCoefficientAtLift`: it is an isomorphism `L_x ≅ M`.
* `stalkEvaluation_germ_smul`: changing the lift acts by the deck group on `M`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

namespace PrincipalCoverLocalSystem

universe uG u

variable {G : Type uG} {E X M : Type u}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E] [AddCommGroup M] [DistribMulAction G M]

private def sliceBaseOpen (p : E → X) (hp : IsQuotientCoveringMap p G)
    (O : Set E) (hO : IsOpen O) : Opens X :=
  ⟨p '' O, hp.isOpenQuotientMap.isOpenMap O hO⟩

private theorem exists_sliceCoordinate (p : E → X) (hp : IsQuotientCoveringMap p G)
    (O : Set E) (hO : IsOpen O)
    (z : LiftedOpen p (sliceBaseOpen p hp O hO)) :
    ∃ g : G, g • z.1 ∈ O := by
  obtain ⟨u, huO, hu⟩ := z.2
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hu
  change g • z.1 = u at hg
  refine ⟨g, ?_⟩
  rw [hg]
  exact huO

private noncomputable def sliceCoordinate (p : E → X) (hp : IsQuotientCoveringMap p G)
    (O : Set E) (hO : IsOpen O)
    (z : LiftedOpen p (sliceBaseOpen p hp O hO)) : G :=
  Classical.choose (exists_sliceCoordinate p hp O hO z)

private theorem sliceCoordinate_mem (p : E → X) (hp : IsQuotientCoveringMap p G)
    (O : Set E) (hO : IsOpen O)
    (z : LiftedOpen p (sliceBaseOpen p hp O hO)) :
    sliceCoordinate p hp O hO z • z.1 ∈ O :=
  Classical.choose_spec (exists_sliceCoordinate p hp O hO z)

private theorem sliceCoordinate_eq_iff (p : E → X) (hp : IsQuotientCoveringMap p G)
    (O : Set E) (hO : IsOpen O)
    (hdisj : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1)
    (z : LiftedOpen p (sliceBaseOpen p hp O hO)) (g : G) :
    sliceCoordinate p hp O hO z = g ↔ g • z.1 ∈ O := by
  constructor
  · rintro rfl
    exact sliceCoordinate_mem p hp O hO z
  · intro hgO
    let c := sliceCoordinate p hp O hO z
    have hcO : c • z.1 ∈ O := sliceCoordinate_mem p hp O hO z
    have hnonempty : (((g * c⁻¹) • ·) '' O ∩ O).Nonempty := by
      refine ⟨g • z.1, ?_, hgO⟩
      refine ⟨c • z.1, hcO, ?_⟩
      simp [mul_smul]
    have hgc : g * c⁻¹ = 1 := hdisj (g * c⁻¹) hnonempty
    exact (mul_inv_eq_one.mp hgc).symm

private theorem sliceCoordinate_liftedAction (p : E → X)
    (hp : IsQuotientCoveringMap p G) (O : Set E) (hO : IsOpen O)
    (hdisj : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1)
    (g : G) (z : LiftedOpen p (sliceBaseOpen p hp O hO)) :
    sliceCoordinate p hp O hO
        (liftedAction p hp (sliceBaseOpen p hp O hO) g z) =
      sliceCoordinate p hp O hO z * g⁻¹ := by
  apply (sliceCoordinate_eq_iff p hp O hO hdisj _ _).mpr
  simpa [liftedAction, mul_smul] using
    sliceCoordinate_mem p hp O hO z

private theorem sliceCoordinate_isLocallyConstant (p : E → X)
    (hp : IsQuotientCoveringMap p G) (O : Set E) (hO : IsOpen O)
    (hdisj : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1) :
    IsLocallyConstant
      (sliceCoordinate p hp O hO : LiftedOpen p (sliceBaseOpen p hp O hO) → G) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro g
  have heq :
      sliceCoordinate p hp O hO ⁻¹' ({g} : Set G) =
        {z : LiftedOpen p (sliceBaseOpen p hp O hO) | g • z.1 ∈ O} := by
    ext z
    exact sliceCoordinate_eq_iff p hp O hO hdisj z g
  rw [heq]
  exact hO.preimage ((hp.continuous_const_smul g).comp continuous_subtype_val)

private noncomputable def sliceSection (p : E → X)
    (hp : IsQuotientCoveringMap p G) (O : Set E) (hO : IsOpen O)
    (hdisj : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1) (m : M) :
    equivariantSections (M := M) p hp (sliceBaseOpen p hp O hO) :=
  ⟨⟨fun z ↦ (sliceCoordinate p hp O hO z)⁻¹ • m,
      (sliceCoordinate_isLocallyConstant p hp O hO hdisj).comp fun g ↦ g⁻¹ • m⟩,
    by
      intro g z
      simp [sliceCoordinate_liftedAction p hp O hO hdisj, mul_smul]⟩

@[simp]
private theorem sliceSection_at_base (p : E → X)
    (hp : IsQuotientCoveringMap p G) (O : Set E) (hO : IsOpen O)
    (hdisj : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1)
    (e : E) (heO : e ∈ O) (m : M) :
    (sliceSection p hp O hO hdisj m).1
        (⟨e, ⟨e, heO, rfl⟩⟩ : LiftedOpen p (sliceBaseOpen p hp O hO)) = m := by
  have hcoord :
      sliceCoordinate p hp O hO
          (⟨e, ⟨e, heO, rfl⟩⟩ : LiftedOpen p (sliceBaseOpen p hp O hO)) = 1 :=
    (sliceCoordinate_eq_iff p hp O hO hdisj _ 1).mpr (by simpa using heO)
  simp [sliceSection, hcoord]

/-- Evaluation of equivariant sections at a chosen lift `e`, as a cocone over the neighbourhoods
of `p e`. -/
def evaluationCocone (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E) :
    Cocone ((OpenNhds.inclusion (p e)).op ⋙ (sheaf (M := M) p hp).presheaf) where
  pt := AddCommGrpCat.of M
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ s.1 ⟨e, (unop U).2⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by
        intro U V i
        ext s
        rfl }

/-- Evaluation at a chosen lift `e`, as a map from the stalk of the local system at `p e` to the
coefficient group `M`. -/
def stalkEvaluation (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E) :
    (sheaf (M := M) p hp).presheaf.stalk (p e) ⟶ AddCommGrpCat.of M :=
  colimit.desc _ (evaluationCocone (M := M) p hp e)

/-- Evaluation at `e` of the germ of a section `s` is the value of `s` at `e`. -/
@[simp]
theorem stalkEvaluation_germ (p : E → X) (hp : IsQuotientCoveringMap p G)
    (e : E) (U : Opens X) (heU : p e ∈ U)
    (s : (sheaf (M := M) p hp).obj.obj (op U)) :
    stalkEvaluation (M := M) p hp e
        ((sheaf (M := M) p hp).presheaf.germ U (p e) heU s) =
      s.1 ⟨e, heU⟩ := by
  exact colimit.ι_desc_apply _ _ _

/-- Changing the chosen lift by a deck transformation `g` changes evaluation by the action of `g`
on `M`. -/
theorem stalkEvaluation_germ_smul (p : E → X) (hp : IsQuotientCoveringMap p G)
    (e : E) (g : G) (U : Opens X) (heU : p e ∈ U)
    (s : (sheaf (M := M) p hp).obj.obj (op U)) :
    stalkEvaluation (M := M) p hp (g • e)
        ((sheaf (M := M) p hp).presheaf.germ U (p (g • e))
          (by simpa only [hp.map_smul] using heU) s) =
      g • stalkEvaluation (M := M) p hp e
        ((sheaf (M := M) p hp).presheaf.germ U (p e) heU s) := by
  rw [stalkEvaluation_germ, stalkEvaluation_germ]
  exact s.2 g ⟨e, heU⟩

/-- Evaluation at a lift is surjective on the stalk: every coefficient extends over a sufficiently
small evenly covered neighborhood by equivariance. -/
theorem stalkEvaluation_surjective (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E) :
    Function.Surjective (stalkEvaluation (M := M) p hp e) := by
  intro m
  obtain ⟨D, hD, hdisj⟩ := hp.disjoint e
  let O : Set E := interior D
  have hO : IsOpen O := isOpen_interior
  have heO : e ∈ O := mem_interior_iff_mem_nhds.mpr hD
  have hdisjO : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1 := by
    intro g h
    apply hdisj g
    exact h.mono (Set.inter_subset_inter (Set.image_mono interior_subset) interior_subset)
  have heU : p e ∈ sliceBaseOpen p hp O hO := by
    change p e ∈ p '' O
    exact ⟨e, heO, rfl⟩
  let s := sliceSection p hp O hO hdisjO m
  refine ⟨(sheaf (M := M) p hp).presheaf.germ
    (sliceBaseOpen p hp O hO) (p e) heU s, ?_⟩
  calc
    stalkEvaluation (M := M) p hp e
        ((sheaf (M := M) p hp).presheaf.germ
          (sliceBaseOpen p hp O hO) (p e) heU s) =
        s.1 ⟨e, heU⟩ := stalkEvaluation_germ p hp e _ heU s
    _ = m := by
      simpa [s] using sliceSection_at_base p hp O hO hdisjO e heO m

private theorem exists_restriction_eq_of_eq_at_lift
    (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E)
    (U V : Opens X) (heU : p e ∈ U) (heV : p e ∈ V)
    (s : equivariantSections (M := M) p hp U)
    (t : equivariantSections (M := M) p hp V)
    (hvalue : s.1 ⟨e, heU⟩ = t.1 ⟨e, heV⟩) :
    ∃ (W : Opens X) (_heW : p e ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
      restrict (M := M) p hp iWU.le s = restrict (M := M) p hp iWV.le t := by
  let UV : Opens X := U ⊓ V
  let sUV := restrict (M := M) p hp (inf_le_left : UV ≤ U) s
  let tUV := restrict (M := M) p hp (inf_le_right : UV ≤ V) t
  let eUV : LiftedOpen p UV := ⟨e, ⟨heU, heV⟩⟩
  let pair : LiftedOpen p UV → M × M := fun z ↦ (sUV.1 z, tUV.1 z)
  have hpair : IsLocallyConstant pair :=
    sUV.1.isLocallyConstant.prodMk tUV.1.isLocallyConstant
  let A : Set (LiftedOpen p UV) := pair ⁻¹' {q | q.1 = q.2}
  have hA : IsOpen A := hpair _
  have heA : eUV ∈ A := by
    change s.1 ⟨e, heU⟩ = t.1 ⟨e, heV⟩
    exact hvalue
  have hUVopen : IsOpen (p ⁻¹' (UV : Set X)) := UV.isOpen.preimage hp.continuous
  have hvalOpen : IsOpenEmbedding (Subtype.val : LiftedOpen p UV → E) :=
    hUVopen.isOpenEmbedding_subtypeVal
  let O₀ : Set E := Subtype.val '' A
  have hO₀ : IsOpen O₀ := hvalOpen.isOpenMap A hA
  have heO₀ : e ∈ O₀ := ⟨eUV, heA, rfl⟩
  obtain ⟨D, hD, hdisj⟩ := hp.disjoint e
  let O : Set E := O₀ ∩ interior D
  have hO : IsOpen O := hO₀.inter isOpen_interior
  have heO : e ∈ O := ⟨heO₀, mem_interior_iff_mem_nhds.mpr hD⟩
  have hdisjO : ∀ g : G, ((g • ·) '' O ∩ O).Nonempty → g = 1 := by
    intro g h
    apply hdisj g
    exact h.mono (Set.inter_subset_inter
      (Set.image_mono (Set.inter_subset_right.trans interior_subset))
      (Set.inter_subset_right.trans interior_subset))
  let W := sliceBaseOpen p hp O hO
  have hWUV : W ≤ UV := by
    intro x hx
    change x ∈ U ⊓ V
    change x ∈ p '' O at hx
    obtain ⟨u, huO, rfl⟩ := hx
    obtain ⟨z, hzA, rfl⟩ := huO.1
    exact z.2
  have heW : p e ∈ W := by
    change p e ∈ p '' O
    exact ⟨e, heO, rfl⟩
  let iWU : W ⟶ U := homOfLE (hWUV.trans inf_le_left)
  let iWV : W ⟶ V := homOfLE (hWUV.trans inf_le_right)
  refine ⟨W, heW, iWU, iWV, ?_⟩
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  let zUV : LiftedOpen p UV := liftedInclusion p hWUV z
  obtain ⟨g, hgO⟩ := exists_sliceCoordinate p hp O hO z
  obtain ⟨a, haA, hae⟩ := hgO.1
  have haeq : a = liftedAction p hp UV g zUV := by
    apply Subtype.ext
    exact hae
  have hst : sUV.1 (liftedAction p hp UV g zUV) =
      tUV.1 (liftedAction p hp UV g zUV) := by
    rw [← haeq]
    exact haA
  change sUV.1 zUV = tUV.1 zUV
  apply smul_left_cancel g
  rw [← sUV.2 g zUV, ← tUV.2 g zUV]
  exact hst

/-- Evaluation at a lift is injective on the stalk: equivariant locally constant sections that
agree at one lift agree after shrinking the base to a disjoint slice. -/
theorem stalkEvaluation_injective (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E) :
    Function.Injective (stalkEvaluation (M := M) p hp e) := by
  intro a b hab
  let F := (sheaf (M := M) p hp).presheaf
  obtain ⟨U, heU, s, rfl⟩ := F.exists_germ_eq a
  obtain ⟨V, heV, t, rfl⟩ := F.exists_germ_eq b
  rw [stalkEvaluation_germ, stalkEvaluation_germ] at hab
  obtain ⟨W, heW, iWU, iWV, hres⟩ :=
    exists_restriction_eq_of_eq_at_lift p hp e U V heU heV s t hab
  exact F.germ_ext W heW iWU iWV hres

/-- Evaluation at a chosen lift is a bijection from the associated local-system stalk to the
coefficient group. -/
theorem stalkEvaluation_bijective (p : E → X) (hp : IsQuotientCoveringMap p G) (e : E) :
    Function.Bijective (stalkEvaluation (M := M) p hp e) :=
  ⟨stalkEvaluation_injective p hp e, stalkEvaluation_surjective p hp e⟩

/-- Evaluation at a lift is an isomorphism of additive commutative groups. -/
noncomputable instance stalkEvaluation_isIso (p : E → X)
    (hp : IsQuotientCoveringMap p G) (e : E) :
    IsIso (stalkEvaluation (M := M) p hp e) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (stalkEvaluation_bijective p hp e)

/-- A choice of lift `e` of `x` identifies the stalk of the local system at `x` with the
coefficient group `M` (Whitehead VI.1). -/
noncomputable def stalkIsoCoefficientAtLift (p : E → X)
    (hp : IsQuotientCoveringMap p G) (e : E) :
    (sheaf (M := M) p hp).presheaf.stalk (p e) ≅ AddCommGrpCat.of M :=
  asIso (stalkEvaluation (M := M) p hp e)

end PrincipalCoverLocalSystem
