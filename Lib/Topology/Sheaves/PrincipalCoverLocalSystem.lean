/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Local systems from principal covering actions

For a principal `G`-cover `p : E → X` and an additive commutative group `M` acted on
distributively by `G`, this file constructs the associated sheaf.  Its sections over `U` are
definitionally the equivariant locally constant functions on `p ⁻¹' U`.

When the total space of the cover is nonempty and preconnected, the global sections are
canonically equivalent to the subgroup of `G`-invariant coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology

namespace PrincipalCoverLocalSystem

universe uG u

variable {G : Type uG} {E X M : Type u}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E] [AddCommGroup M] [DistribMulAction G M]

/-- The inverse image of an open set under the principal covering map. -/
abbrev LiftedOpen (p : E → X) (U : Opens X) := {e : E // p e ∈ U}

/-- The deck action preserves the inverse image of every open set. -/
def liftedAction (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X)
    (g : G) (e : LiftedOpen p U) : LiftedOpen p U :=
  ⟨g • e.1, by simpa only [hp.map_smul] using e.2⟩

/-- Inclusion between inverse images of nested open sets. -/
def liftedInclusion (p : E → X) {U V : Opens X} (h : U ≤ V) :
    C(LiftedOpen p U, LiftedOpen p V) where
  toFun e := ⟨e.1, h e.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion between lifted opens is an open embedding. -/
private theorem liftedInclusion_isOpenEmbedding (p : E → X) (hp : IsQuotientCoveringMap p G)
    {U V : Opens X} (h : U ≤ V) : IsOpenEmbedding (liftedInclusion p h) := by
  have hV : IsOpenEmbedding (Subtype.val : LiftedOpen p V → E) :=
    (V.isOpen.preimage hp.continuous).isOpenEmbedding_subtypeVal
  apply (IsOpenEmbedding.of_comp_iff (liftedInclusion p h) hV).mp
  change IsOpenEmbedding (Subtype.val : LiftedOpen p U → E)
  exact (U.isOpen.preimage hp.continuous).isOpenEmbedding_subtypeVal

/-- Equivariant locally constant functions on the lifted open set. -/
def equivariantSections (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    AddSubgroup (LocallyConstant (LiftedOpen p U) M) where
  carrier s := ∀ (g : G) (e : LiftedOpen p U), s (liftedAction p hp U g e) = g • s e
  zero_mem' := by intro g e; simp
  add_mem' := by
    intro s t hs ht g e
    simp only [LocallyConstant.add_apply, hs g e, ht g e, smul_add]
  neg_mem' := by
    intro s hs g e
    simp only [LocallyConstant.neg_apply, hs g e, smul_neg]

@[simp]
theorem mem_equivariantSections (p : E → X) (hp : IsQuotientCoveringMap p G)
    (U : Opens X) (s : LocallyConstant (LiftedOpen p U) M) :
    s ∈ equivariantSections p hp U ↔
      ∀ (g : G) (e : LiftedOpen p U), s (liftedAction p hp U g e) = g • s e :=
  Iff.rfl

/-- Restriction of equivariant locally constant functions. -/
def restrict (p : E → X) (hp : IsQuotientCoveringMap p G) {U V : Opens X} (h : U ≤ V) :
    equivariantSections (M := M) p hp V →+ equivariantSections (M := M) p hp U where
  toFun s := ⟨LocallyConstant.comap (liftedInclusion p h) s.1, by
    intro g e
    change s.1 (liftedInclusion p h (liftedAction p hp U g e)) =
      g • s.1 (liftedInclusion p h e)
    have heq : liftedInclusion p h (liftedAction p hp U g e) =
        liftedAction p hp V g (liftedInclusion p h e) := Subtype.ext rfl
    exact (congrArg s.1 heq).trans (s.2 g (liftedInclusion p h e))⟩
  map_zero' := by
    apply Subtype.ext
    ext e
    rfl
  map_add' s t := by
    apply Subtype.ext
    ext e
    rfl

/-- The presheaf presented by equivariant locally constant functions. -/
def presheaf (p : E → X) (hp : IsQuotientCoveringMap p G) :
    TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of X) where
  obj U := AddCommGrpCat.of (equivariantSections (M := M) p hp (unop U))
  map i := AddCommGrpCat.ofHom (restrict (M := M) p hp i.unop.le)
  map_id U := by
    ext s e
    rfl
  map_comp i j := by
    ext s e
    rfl

@[simp]
theorem presheaf_map_apply (p : E → X) (hp : IsQuotientCoveringMap p G)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : (presheaf (M := M) p hp).obj U)
    (e : LiftedOpen p (unop V)) :
    ((presheaf (M := M) p hp).map i s).1 e =
      s.1 ⟨e.1, i.unop.le e.2⟩ :=
  rfl

/-- Equivariant locally constant functions satisfy the sheaf condition without further
sheafification. -/
theorem presheaf_isSheaf (p : E → X) (hp : IsQuotientCoveringMap p G) :
    (presheaf (M := M) p hp).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have compatible (i j : ι) (e : LiftedOpen p (U i ⊓ U j)) :
      (sf i).1 ⟨e.1, e.2.1⟩ = (sf j).1 ⟨e.1, e.2.2⟩ := by
    have h := congrArg (fun t => t.1 e) (hsf i j)
    change (sf i).1 ⟨e.1, e.2.1⟩ = (sf j).1 ⟨e.1, e.2.2⟩ at h
    exact h
  have compatibleAt (i j : ι) (x : E) (hi : p x ∈ U i) (hj : p x ∈ U j) :
      (sf i).1 ⟨x, hi⟩ = (sf j).1 ⟨x, hj⟩ := by
    have hc := compatible i j ⟨x, ⟨hi, hj⟩⟩
    convert hc using 1
  choose index index_spec using fun e : LiftedOpen p (iSup U) => Opens.mem_iSup.mp e.2
  let value : LiftedOpen p (iSup U) → M := fun e =>
    (sf (index e)).1 ⟨e.1, index_spec e⟩
  have value_isLocallyConstant : IsLocallyConstant value := by
    intro S
    have hfiber : value ⁻¹' S = ⋃ i, liftedInclusion p (le_iSup U i) '' ((sf i).1 ⁻¹' S) := by
      ext e
      constructor
      · intro he
        apply Set.mem_iUnion.mpr
        refine ⟨index e, ⟨⟨e.1, index_spec e⟩, he, Subtype.ext rfl⟩⟩
      · intro he
        obtain ⟨i, ei, hei, rfl⟩ := Set.mem_iUnion.mp he
        have hc := compatibleAt (index (liftedInclusion p (le_iSup U i) ei)) i ei.1
          (index_spec (liftedInclusion p (le_iSup U i) ei)) ei.2
        have hvalue : value (liftedInclusion p (le_iSup U i) ei) = (sf i).1 ei := by
          exact hc
        change value (liftedInclusion p (le_iSup U i) ei) ∈ S
        rw [hvalue]
        exact hei
    rw [hfiber]
    exact isOpen_iUnion fun i =>
      (liftedInclusion_isOpenEmbedding p hp (le_iSup U i)).isOpenMap _
        ((sf i).1.isLocallyConstant S)
  let sectionLC : LocallyConstant (LiftedOpen p (iSup U)) M :=
    ⟨value, value_isLocallyConstant⟩
  have section_equivariant : ∀ (g : G) (e : LiftedOpen p (iSup U)),
      sectionLC (liftedAction p hp (iSup U) g e) = g • sectionLC e := by
    intro g e
    let ge := liftedAction p hp (iSup U) g e
    have he_index : p (ge.1) ∈ U (index e) := by
      simpa only [ge, liftedAction, hp.map_smul] using index_spec e
    have hcompare : (sf (index ge)).1 ⟨ge.1, index_spec ge⟩ =
        (sf (index e)).1 ⟨ge.1, he_index⟩ :=
      compatibleAt (index ge) (index e) ge.1 (index_spec ge) he_index
    change value ge = g • value e
    rw [show value ge = (sf (index ge)).1 ⟨ge.1, index_spec ge⟩ from rfl,
      hcompare]
    have heq : (⟨ge.1, he_index⟩ : LiftedOpen p (U (index e))) =
        liftedAction p hp (U (index e)) g ⟨e.1, index_spec e⟩ := Subtype.ext rfl
    rw [heq, (sf (index e)).2 g ⟨e.1, index_spec e⟩]
  let s : equivariantSections (M := M) p hp (iSup U) :=
    ⟨sectionLC, section_equivariant⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    apply LocallyConstant.ext
    intro e
    have hc := compatibleAt (index (liftedInclusion p (le_iSup U i) e)) i e.1
      (index_spec (liftedInclusion p (le_iSup U i) e)) e.2
    change value (liftedInclusion p (le_iSup U i) e) = (sf i).1 e
    exact hc
  · intro t ht
    apply Subtype.ext
    apply LocallyConstant.ext
    intro e
    have h := congrArg (fun q => q.1 ⟨e.1, index_spec e⟩) (ht (index e))
    change t.1 e = (sf (index e)).1 ⟨e.1, index_spec e⟩ at h
    change t.1 e = value e
    exact h

/-- The associated local system, with sections definitionally represented by equivariant locally
constant functions on the principal cover. -/
def sheaf (p : E → X) (hp : IsQuotientCoveringMap p G) :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) :=
  ⟨presheaf (M := M) p hp, presheaf_isSheaf p hp⟩

/-! ## Global sections on a connected principal cover -/

/-- Coefficients fixed by the whole deck group. -/
abbrev invariantCoefficients : AddSubgroup M := FixedPoints.addSubgroup G M

/-- The lifted total open is canonically the original total space. -/
def liftedTopHomeomorph (p : E → X) : LiftedOpen p ⊤ ≃ₜ E where
  toFun e := e.1
  invFun e := ⟨e, trivial⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- On a connected total cover, global sections of the associated sheaf are canonically the
coefficients fixed by the deck group. -/
def globalSectionsEquivInvariantCoefficients (p : E → X)
    (hp : IsQuotientCoveringMap p G) [ConnectedSpace E] :
    ((sheaf (M := M) p hp).obj.obj (op (⊤ : Opens X)) : Type u) ≃+
      invariantCoefficients (G := G) (M := M) := by
  let e₀ : LiftedOpen p ⊤ := ⟨Classical.arbitrary E, trivial⟩
  letI : PreconnectedSpace (LiftedOpen p ⊤) :=
    (liftedTopHomeomorph p).symm.surjective.denseRange.preconnectedSpace
      (liftedTopHomeomorph p).symm.continuous
  refine
    { toFun := fun s => ⟨s.1 e₀, ?_⟩
      invFun := fun m => ⟨LocallyConstant.const _ m.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro g
    rw [← s.2 g e₀]
    exact s.1.apply_eq_of_preconnectedSpace _ _
  · intro g e
    change m.1 = g • m.1
    exact (m.2 g).symm
  · intro s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro e
    exact s.1.apply_eq_of_preconnectedSpace _ _
  · intro m
    apply Subtype.ext
    rfl
  · intro a b
    apply Subtype.ext
    rfl

/-- The global-sections equivalence is evaluation at any point of the connected total cover. -/
@[simp]
theorem globalSectionsEquivInvariantCoefficients_apply (p : E → X)
    (hp : IsQuotientCoveringMap p G) [ConnectedSpace E]
    (s : ((sheaf (M := M) p hp).obj.obj (op (⊤ : Opens X)) : Type u)) (e : E) :
    (globalSectionsEquivInvariantCoefficients p hp s : M) = s.1 ⟨e, trivial⟩ := by
  let hpre : PreconnectedSpace (LiftedOpen p ⊤) :=
    (liftedTopHomeomorph p).symm.surjective.denseRange.preconnectedSpace
      (liftedTopHomeomorph p).symm.continuous
  change s.1 ⟨Classical.arbitrary E, trivial⟩ = s.1 ⟨e, trivial⟩
  exact @LocallyConstant.apply_eq_of_preconnectedSpace _ _ _ hpre s.1 _ _

end PrincipalCoverLocalSystem
