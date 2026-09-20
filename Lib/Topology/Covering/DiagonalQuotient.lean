/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Diagonal quotients

  Diagonal quotients: the quotient of a space by an equivalence relation given as
  the orbit relation of a group action or a family of maps, its universal
  property, and the induced maps on fundamental groups (Hatcher, Algebraic
  Topology, Section 1.3).
-/



open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Fibres of locally trivial maps -/

/-- A local trivialization identifies the fibre over a point of the patch with `F`. -/
def DiagonalQuotient.fibreHomeomorphOfLocalTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] (f : E → B) (U : J → TopologicalSpace.Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val)
    (i : J) (b : B) (hb : b ∈ U i) : (f ⁻¹' { b }) ≃ₜ F := by
  let lift : (f ⁻¹' { b }) → (f ⁻¹' (U i : Set B)) := fun x =>
    ⟨x.val, by
      change f x.val ∈ U i
      rw [show f x.val = b from x.property]
      exact hb⟩
  let inv : F → (f ⁻¹' { b }) := fun t =>
    ⟨((h i).symm (⟨b, hb⟩, t)).val,
      by
      change f ((h i).symm (⟨b, hb⟩, t)).val = b
      rw [← hbase i]
      simp⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hpair (x : (f ⁻¹' { b })) : ((⟨b, hb⟩ : U i), (h i (lift x)).2) = h i (lift x) := by
    apply Prod.ext
    · apply Subtype.ext
      exact ((hbase i (lift x)).trans x.property).symm
    · rfl
  refine
    { toFun := fun x => (h i (lift x)).2
      invFun := inv
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := continuous_snd.comp ((h i).continuous.comp hlift)
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change ((h i).symm ((⟨b, hb⟩ : U i), (h i (lift x)).2)).val = x.val
    rw [hpair x, (h i).symm_apply_apply]
  · intro t
    change (h i (lift (inv t))).2 = t
    have hinv : lift (inv t) = (h i).symm (⟨b, hb⟩, t) := by
      apply Subtype.ext
      rfl
    rw [hinv, (h i).apply_symm_apply]
  · exact
      (continuous_subtype_val.comp
            ((h i).symm.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk
        _

/-- On a trivialization patch the map is the first projection. -/
theorem DiagonalQuotient.restrictPreimage_eq_fst_comp {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] (f : E → B) (U : J → TopologicalSpace.Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val)
    (i : J) : (U i : Set B).restrictPreimage f = Prod.fst ∘ h i := by
  funext x
  apply Subtype.ext
  exact (hbase i x).symm

/-- Over each patch a locally trivial map with compact fibre is proper. -/
theorem DiagonalQuotient.restrictPreimage_proper_of_localTrivializations {E B F J : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] [CompactSpace F] (f : E → B)
    (U : J → TopologicalSpace.Opens B) (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val) (i : J) :
    IsProperMap ((U i : Set B).restrictPreimage f) := by
  rw [restrictPreimage_eq_fst_comp f U h hbase i]
  exact isProperMap_fst_of_compactSpace.comp (h i).isProperMap

/-- A locally trivial map with compact fibre is proper. -/
theorem DiagonalQuotient.proper_of_localTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] [CompactSpace F] (f : E → B) (hf : Continuous f)
    (U : J → TopologicalSpace.Opens B) (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val) :
    IsProperMap f := by
  have hp := restrictPreimage_proper_of_localTrivializations f U h hbase
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf, hU.isClosedMap_iff_restrictPreimage.mpr (fun i => (hp i).isClosedMap), ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hU.exists_mem b
  have hc :=
    ((hp i).isCompact_preimage (isCompact_singleton (x := (⟨b, hi⟩ : U i)))).image
      continuous_subtype_val
  simpa only [Set.image_val_preimage_restrictPreimage, Set.image_singleton] using hc

/-- The total space of a locally trivial map over a Hausdorff base with Hausdorff fibre is Hausdorff. -/
theorem DiagonalQuotient.t2Space_of_localTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] [T2Space B] [T2Space F] (f : E → B)
    (hf : Continuous f) (U : J → TopologicalSpace.Opens B) (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (_hbase : ∀ i x, ((h i x).1 : B) = f x.val) :
    T2Space E := by
  constructor
  intro x y hxy
  by_cases hb : f x = f y
  · obtain ⟨i, hi⟩ := hU.exists_mem (f x)
    have hx : x ∈ f ⁻¹' (U i : Set B) := hi
    have hy : y ∈ f ⁻¹' (U i : Set B) := by
      change f y ∈ U i
      rw [← hb]
      exact hi
    let a : f ⁻¹' (U i : Set B) := ⟨x, hx⟩
    let b : f ⁻¹' (U i : Set B) := ⟨y, hy⟩
    have hab : a ≠ b := fun he => hxy (congrArg Subtype.val he)
    let : T2Space (f ⁻¹' (U i : Set B)) := (h i).symm.t2Space
    obtain ⟨V, W, hV, hW, ha, hb', hVW⟩ := t2_separation hab
    have hopen : IsOpen (f ⁻¹' (U i : Set B)) := (U i).isOpen.preimage hf
    refine
      ⟨Subtype.val '' V, Subtype.val '' W, hopen.isOpenMap_subtype_val _ hV,
        hopen.isOpenMap_subtype_val _ hW, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb'', hzb⟩
    have hab' : a' = b' := Subtype.ext (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hVW) ha' (hab'.symm ▸ hb'')
  · obtain ⟨V, W, hV, hW, hx, hy, hVW⟩ := t2_separation hb
    exact ⟨f ⁻¹' V, f ⁻¹' W, hV.preimage hf, hW.preimage hf, hx, hy, hVW.preimage f⟩

/-! ### The diagonal quotient -/

/-- The quotient of the base by the group action. -/
abbrev DiagonalQuotient.BaseSpace (G B : Type*) [Group G] [MulAction G B] :=
  MulAction.orbitRel.Quotient G B

/-- The quotient of `B × F` by the diagonal group action. -/
abbrev DiagonalQuotient.Space (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :=
  MulAction.orbitRel.Quotient G (B × F)

/-- The quotient map from the base to its orbit space. -/
def DiagonalQuotient.baseQuotient (G B : Type*) [Group G] [MulAction G B] : B → BaseSpace G B :=
  Quotient.mk (MulAction.orbitRel G B)

/-- The quotient map from `B × F` to the diagonal quotient. -/
def DiagonalQuotient.quotient (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :
    B × F → Space G B F :=
  Quotient.mk (MulAction.orbitRel G (B × F))

/-- The diagonal quotient map is surjective. -/
theorem DiagonalQuotient.quotient_surjective (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] : Function.Surjective (quotient G B F) :=
  Quotient.mk_surjective

/-- Two pairs have the same quotient exactly when a group element moves one to the other. -/
theorem DiagonalQuotient.quotient_eq_iff (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (x y : B × F) : quotient G B F x = quotient G B F y ↔ ∃ g : G, g • y = x :=
  Quotient.eq''

/-- The quotient map is invariant under the diagonal action. -/
@[simp]
theorem DiagonalQuotient.quotient_smul (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (g : G) (x : B × F) : quotient G B F (g • x) = quotient G B F x :=
  (quotient_eq_iff G B F _ _).mpr ⟨g, rfl⟩

/-- The projection of the diagonal quotient onto the base quotient. -/
def DiagonalQuotient.projection (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :
    Space G B F → BaseSpace G B :=
  Quotient.lift (fun x : B × F => baseQuotient G B x.1)
    (by
      rintro x y ⟨g, hg⟩
      exact Quotient.sound ⟨g, congrArg Prod.fst hg⟩)

/-- The inclusion of the fibre `F` over the class of `b`. -/
def DiagonalQuotient.fibreInclusion (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (b : B) (f : F) : Space G B F :=
  quotient G B F (b, f)

/-- The base quotient map is continuous. -/
theorem DiagonalQuotient.baseQuotient_continuous (G B : Type*) [Group G] [MulAction G B]
    [TopologicalSpace B] : Continuous (baseQuotient G B) :=
  continuous_quot_mk

/-- The diagonal quotient map is continuous. -/
theorem DiagonalQuotient.quotient_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] : Continuous (quotient G B F) :=
  continuous_quot_mk

/-- The diagonal quotient map is a quotient map. -/
theorem DiagonalQuotient.quotient_isQuotientMap (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] :
    Topology.IsQuotientMap (quotient G B F) :=
  isQuotientMap_quotient_mk'

/-- The projection to the base quotient is continuous. -/
theorem DiagonalQuotient.projection_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] : Continuous (projection G B F) :=
  (quotient_isQuotientMap G B F).continuous_iff.mpr
    ((baseQuotient_continuous G B).comp continuous_fst)

/-- The fibre inclusion is continuous. -/
theorem DiagonalQuotient.fibreInclusion_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) :
    Continuous (fibreInclusion G B F b) :=
  (quotient_continuous G B F).comp (continuous_const.prodMk continuous_id)

/-! ### Local trivializations over covering patches -/

/-- A local inverse of the base quotient covering near the class of `b`. -/
def DiagonalQuotient.baseLocalInverse {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    OpenPartialHomeomorph (BaseSpace G B) B :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt b

/-- The base local inverse is a right inverse of the quotient map. -/
theorem DiagonalQuotient.baseQuotient_localInverse {G : Type*} {B : Type*} [Group G]
    [MulAction G B] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    {x : BaseSpace G B} (hx : x ∈ (baseLocalInverse hq b).source) :
    baseQuotient G B (baseLocalInverse hq b x) = x :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hx

/-- The open patch of the base quotient covered by the local inverse at `b`. -/
def DiagonalQuotient.patch {G : Type*} {B : Type*} [Group G] [MulAction G B] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    TopologicalSpace.Opens (BaseSpace G B) :=
  ⟨(baseLocalInverse hq b).source, (baseLocalInverse hq b).open_source⟩

/-- The class of `b` lies in its own patch. -/
theorem DiagonalQuotient.baseQuotient_mem_patch {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    baseQuotient G B b ∈ patch hq b :=
  hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The local-inverse patches cover the base quotient. -/
theorem DiagonalQuotient.patch_cover {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) :
    TopologicalSpace.IsOpenCover (patch hq) := by
  apply TopologicalSpace.IsOpenCover.of_sets (fun b => (baseLocalInverse hq b).open_source)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨b, rfl⟩ := hq.surjective x
  exact Set.mem_iUnion.mpr ⟨b, baseQuotient_mem_patch hq b⟩

/-- The fibre inclusion is injective. -/
theorem DiagonalQuotient.fibreInclusion_injective {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Function.Injective (fibreInclusion G B F b) := by
  let := hq.isCancelSMul
  intro x y hxy
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hb : g • b = b := congrArg Prod.fst hg
  have hg1 : g = 1 := IsCancelSMul.right_cancel _ _ b (hb.trans (one_smul G b).symm)
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

/-- The diagonal quotient of a quotient covering is again a quotient covering. -/
theorem DiagonalQuotient.quotientCoveringMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsQuotientCoveringMap (quotient G B F) G
    where
  toIsQuotientMap := quotient_isQuotientMap G B F
  continuous_const_smul
    g := (hq.continuous_const_smul g).prodMap (ContinuousConstSMul.continuous_const_smul g)
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint
    x := by
    obtain ⟨U, hU, hd⟩ := hq.disjoint x.1
    refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
    exact hd g ⟨g • w.1, ⟨w.1, hw, rfl⟩, hz⟩

/-- The diagonal quotient map is a covering map. -/
theorem DiagonalQuotient.quotient_isCoveringMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsCoveringMap (quotient G B F) :=
  (quotientCoveringMap (F := F) hq).isCoveringMap

/-- The diagonal quotient map is an open quotient map. -/
theorem DiagonalQuotient.quotient_isOpenQuotientMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsOpenQuotientMap (quotient G B F) := by
  let := hq.toContinuousConstSMul
  exact MulAction.isOpenQuotientMap_quotientMk

/-- The trivializing map on a patch, sending `(class, f)` to the orbit of `(lift, f)`. -/
def DiagonalQuotient.patchMap {G : Type*} {B : Type*} {F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (x : patch hq b × F) : Space G B F :=
  quotient G B F (baseLocalInverse hq b x.1, x.2)

/-- The patch map projects to its first component. -/
@[simp]
theorem DiagonalQuotient.projection_patchMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (x : patch hq b × F) :
    projection G B F (patchMap hq b x) = (x.1 : BaseSpace G B) :=
  baseQuotient_localInverse hq b x.1.property

/-- The patch trivialization is injective. -/
theorem DiagonalQuotient.patchMap_injective {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Function.Injective (patchMap (F := F) hq b) := by
  let := hq.isCancelSMul
  intro x y hxy
  have hbase : x.1 = y.1 :=
    Subtype.ext (by simpa only [projection_patchMap] using congrArg (projection G B F) hxy)
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hgbase : g • baseLocalInverse hq b y.1 = baseLocalInverse hq b y.1 := by
    have he := congrArg Prod.fst hg
    change g • baseLocalInverse hq b y.1 = baseLocalInverse hq b x.1 at he
    simpa only [hbase] using he
  have hg1 : g = 1 :=
    IsCancelSMul.right_cancel _ _ (baseLocalInverse hq b y.1)
      (hgbase.trans (one_smul G (baseLocalInverse hq b y.1)).symm)
  apply Prod.ext hbase
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

/-- The patch trivialization is continuous. -/
theorem DiagonalQuotient.patchMap_continuous {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Continuous (patchMap (F := F) hq b) :=
  (quotient_continuous G B F).comp
    ((baseLocalInverse hq b).isOpenEmbedding_restrict.continuous.prodMap continuous_id)

/-- The patch trivialization is an open embedding. -/
theorem DiagonalQuotient.patchMap_openEmbedding {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    Topology.IsOpenEmbedding (patchMap (F := F) hq b) :=
  .of_continuous_injective_isOpenMap (patchMap_continuous hq b) (patchMap_injective hq b)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseLocalInverse hq b).isOpenEmbedding_restrict.isOpenMap.prodMap IsOpenMap.id))

/-- The range of the patch trivialization is the preimage of the patch. -/
theorem DiagonalQuotient.patchMap_range {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Set.range (patchMap (F := F) hq b) = projection G B F ⁻¹' (patch hq b : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, projection_patchMap]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ patch hq b at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (baseQuotient_localInverse hq b hy)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    apply (quotient_eq_iff G B F _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

/-- The preimage of a patch is homeomorphic to the patch times the fibre. -/
def DiagonalQuotient.patchHomeomorph {G : Type*} {B : Type*} {F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    (projection G B F ⁻¹' (patch hq b : Set _)) ≃ₜ (patch hq b × F) :=
  ((patchMap_openEmbedding (F := F) hq b).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (patchMap_range hq b))).symm

/-- The patch homeomorphism's first component is the projection. -/
theorem DiagonalQuotient.patchHomeomorph_projection {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B)
    (x : projection G B F ⁻¹' (patch hq b : Set _)) :
    ((patchHomeomorph hq b x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_patchMap hq b (patchHomeomorph hq b x)
  have he : patchMap hq b (patchHomeomorph hq b x) = x.val :=
    congrArg Subtype.val ((patchHomeomorph hq b).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

/-- The fibre over a base class is homeomorphic to `F`. -/
def DiagonalQuotient.fibreHomeomorphOver {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    (projection G B F ⁻¹' {baseQuotient G B b}) ≃ₜ F :=
  fibreHomeomorphOfLocalTrivializations (projection G B F) (patch hq) (patchHomeomorph hq)
    (patchHomeomorph_projection hq) b (baseQuotient G B b) (baseQuotient_mem_patch hq b)

/-- The projection is proper when the fibre is compact. -/
theorem DiagonalQuotient.projection_proper {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] [CompactSpace F] :
    IsProperMap (projection G B F) :=
  proper_of_localTrivializations (projection G B F) (projection_continuous G B F) (patch hq)
    (patch_cover hq) (patchHomeomorph hq) (patchHomeomorph_projection hq)

/-- The diagonal quotient is Hausdorff when base quotient and fibre are. -/
theorem DiagonalQuotient.spaceT2Space {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F]
    [T2Space (BaseSpace G B)] [T2Space F] : T2Space (Space G B F) :=
  t2Space_of_localTrivializations (projection G B F) (projection_continuous G B F) (patch hq)
    (patch_cover hq) (patchHomeomorph hq) (patchHomeomorph_projection hq)

/-- The base quotient is Hausdorff for a properly discontinuous action on a locally compact Hausdorff space. -/
theorem DiagonalQuotient.baseT2Space {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul G B] : T2Space (BaseSpace G B) := by
  let := hq.toContinuousConstSMul
  infer_instance

/-- The diagonal quotient is second countable when base and fibre are. -/
theorem DiagonalQuotient.spaceSecondCountable {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F]
    [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (Space G B F) :=
  (quotient_isQuotientMap G B F).secondCountableTopology
    (quotient_isOpenQuotientMap (F := F) hq).isOpenMap

/-- Acting on the base component equals acting inversely on the fibre. -/
theorem DiagonalQuotient.quotient_smul_fst {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] (g : G) (b : B) (f : F) :
    quotient G B F (g • b, f) = quotient G B F (b, g⁻¹ • f) := by
  apply (quotient_eq_iff G B F _ _).mpr
  exact ⟨g, by simp⟩

/-- Conjugation by a path computes the fundamental-group basepoint change. -/
theorem fundamentalGroup_basepoint_change_apply {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (p : Path x₀ x₁) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p γ =
      (Path.Homotopic.Quotient.mk p).symm.trans (γ.trans (Path.Homotopic.Quotient.mk p)) :=
  rfl

/-! ### The zero section and fundamental group -/

/-- The section of the diagonal quotient induced by a `G`-fixed point of `F`. -/
def DiagonalQuotient.zeroSection {G B F : Type*} [Group G] [MulAction G B] [MulAction G F] (c : F)
    (hc : ∀ g : G, g • c = c) : BaseSpace G B → Space G B F :=
  Quotient.lift (fun b : B => quotient G B F (b, c))
    (by
      rintro b b' ⟨g, hg⟩
      exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg (hc g)⟩)

/-- The zero section is continuous. -/
theorem DiagonalQuotient.zeroSection_continuous {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) (hc : ∀ g : G, g • c = c) :
    Continuous (zeroSection (B := B) c hc) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr
    ((quotient_continuous G B F).comp (continuous_id.prodMk continuous_const))

/-- The zero section is a section of the projection. -/
@[simp]
theorem DiagonalQuotient.projection_zeroSection {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] (c : F) (hc : ∀ g : G, g • c = c) (x : BaseSpace G B) :
    projection G B F (zeroSection c hc x) = x := by
  induction x using Quotient.inductionOn with
  | h b => rfl

/-- The fundamental-group map induced by the fibre inclusion. -/
def DiagonalQuotient.fibreFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    FundamentalGroup F c →* FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ c

/-- The fundamental-group map induced by the projection. -/
def DiagonalQuotient.projectionFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    FundamentalGroup (Space G B F) (fibreInclusion G B F b c) →*
      FundamentalGroup (BaseSpace G B) (baseQuotient G B b) :=
  FundamentalGroup.map ⟨projection G B F, projection_continuous G B F⟩ (fibreInclusion G B F b c)

/-- The fundamental-group map induced by the zero section. -/
def DiagonalQuotient.sectionFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) (hc : ∀ g : G, g • c = c)
    (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →*
      FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨zeroSection c hc, zeroSection_continuous c hc⟩ (baseQuotient G B b)

/-- The projection map after the section map is the identity on the base fundamental group. -/
theorem DiagonalQuotient.projectionFundamentalGroupHom_comp_section {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F)
    (hc : ∀ g : G, g • c = c) (b : B) :
    (projectionFundamentalGroupHom (G := G) b c).comp (sectionFundamentalGroupHom c hc b) =
      MonoidHom.id (FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) := by
  apply DFunLike.ext
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk
    γ =>
    change
      Path.Homotopic.Quotient.mk
          ((γ.map (zeroSection_continuous c hc)).map (projection_continuous G B F)) =
        Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact projection_zeroSection c hc (γ t)

/-- Fibre loops project to the trivial base loop. -/
@[simp]
theorem DiagonalQuotient.projectionFundamentalGroupHom_fibre {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F)
    (γ : FundamentalGroup F c) :
    projectionFundamentalGroupHom (G := G) b c (fibreFundamentalGroupHom b c γ) = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk
    γ =>
    change
      Path.Homotopic.Quotient.mk
          ((γ.map (fibreInclusion_continuous G B F b)).map (projection_continuous G B F)) =
        Path.Homotopic.Quotient.mk (Path.refl (baseQuotient G B b))
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl

/-- The fibre fundamental-group image lies in the kernel of the projection map. -/
theorem DiagonalQuotient.fibreFundamentalGroupHom_range_le_ker {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range ≤
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  rintro γ ⟨δ, rfl⟩
  exact projectionFundamentalGroupHom_fibre b c δ

/-- The monodromy action of the base fundamental group as a homomorphism to `G`. -/
def DiagonalQuotient.deckTransportHom {G B : Type*} [Group G] [MulAction G B] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →* G :=
  (MulEquiv.inv' G).symm.toMonoidHom.comp (hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩)

/-- The deck-transport element realizes the covering monodromy on `b`. -/
theorem DiagonalQuotient.deckTransportHom_monodromy {G B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (γ : FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) :
    (deckTransportHom hq b γ)⁻¹ • b = (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) := by
  change ((hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩ γ).unop⁻¹)⁻¹ • b = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

/-- The fundamental-group endomorphism induced by a `G`-action on the fibre fixing `c`. -/
def DiagonalQuotient.fibreActionFundamentalGroupHom {G F : Type*} [Group G] [MulAction G F]
    [TopologicalSpace F] [ContinuousConstSMul G F] (c : F) (hc : ∀ g : G, g • c = c) (g : G) :
    FundamentalGroup F c →* FundamentalGroup F c :=
  FundamentalGroup.mapOfEq ⟨fun x : F => g • x, ContinuousConstSMul.continuous_const_smul g⟩
    (hc g)

/-- A quotient loop with trivial projection lifts to a vertical loop of the product. -/
theorem DiagonalQuotient.quotient_loop_lift_of_projection_eq_refl {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F)
    (γ : Path.Homotopic.Quotient (fibreInclusion G B F b c) (fibreInclusion G B F b c))
    (hγ :
      γ.map ⟨projection G B F, projection_continuous G B F⟩ =
        Path.Homotopic.Quotient.refl (baseQuotient G B b)) :
    ∃ δ : Path.Homotopic.Quotient (b, c) (b, c),
      δ.map ⟨quotient G B F, quotient_continuous G B F⟩ = γ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    let cov := (quotientCoveringMap (F := F) hq).isCoveringMap
    let L : C(unitInterval, B × F) := cov.liftPath γ (b, c) γ.source
    let γb : Path (baseQuotient G B b) (baseQuotient G B b) := γ.map (projection_continuous G B F)
    let Lb : C(unitInterval, B) := ⟨fun t => (L t).1, continuous_fst.comp L.continuous⟩
    have hLb : Lb = hq.isCoveringMap.liftPath γb b γb.source := by
      apply (hq.isCoveringMap.eq_liftPath_iff' γb.source).mpr
      constructor
      · funext t
        exact congrArg (projection G B F) (congrFun (cov.liftPath_lifts γ (b, c) γ.source) t)
      · exact congrArg Prod.fst (cov.liftPath_zero γ (b, c) γ.source)
    have hnull : γb.Homotopic (Path.refl (baseQuotient G B b)) := by
      apply Path.Homotopic.Quotient.eq.mp
      exact hγ
    have hbaseEnd : hq.isCoveringMap.liftPath γb b γb.source 1 = b := by
      have h := hq.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel hnull b γb.source rfl
      have hc : hq.isCoveringMap.liftPath (Path.refl (baseQuotient G B b)) b rfl 1 = b := by
        exact
          congrArg (fun p : C(unitInterval, B) => p 1)
            (hq.isCoveringMap.liftPath_const (e := b) rfl)
      exact h.trans hc
    have hfirst : (L 1).1 = b := (congrArg (fun p : C(unitInterval, B) => p 1) hLb).trans hbaseEnd
    have hquot : quotient G B F (L 1) = quotient G B F (b, c) :=
      (congrFun (cov.liftPath_lifts γ (b, c) γ.source) 1).trans γ.target
    have hsecond : (L 1).2 = c := by
      apply fibreInclusion_injective (F := F) hq b
      have hp : (b, (L 1).2) = L 1 := Prod.ext hfirst.symm rfl
      exact (congrArg (quotient G B F) hp).trans hquot
    have hlast : L 1 = (b, c) := Prod.ext hfirst hsecond
    let δ : Path (b, c) (b, c) := ⟨L, cov.liftPath_zero γ (b, c) γ.source, hlast⟩
    refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
    change
      Path.Homotopic.Quotient.mk (δ.map (quotient_continuous G B F)) =
        Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact congrFun (cov.liftPath_lifts γ (b, c) γ.source) t

/-- A product loop with trivial first component is its second component made vertical. -/
theorem DiagonalQuotient.product_loop_eq_vertical_of_fst_eq_refl {B F : Type*}
    [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F)
    (α : Path.Homotopic.Quotient (b, c) (b, c)) (h : α.map ⟨Prod.fst, continuous_fst⟩ = .refl b) :
    α =
      (α.map ⟨Prod.snd, continuous_snd⟩).map
        ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
  have hv (β : Path.Homotopic.Quotient c c) :
    Path.Homotopic.prod (.refl b) β =
      β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  calc
    α =
        Path.Homotopic.prod (α.map ⟨Prod.fst, continuous_fst⟩)
          (α.map ⟨Prod.snd, continuous_snd⟩) :=
      (Path.Homotopic.prod_projLeft_projRight α).symm
    _ = Path.Homotopic.prod (.refl b) (α.map ⟨Prod.snd, continuous_snd⟩) := by rw [h]
    _ =
        (α.map ⟨Prod.snd, continuous_snd⟩).map
          ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ :=
      hv _

/-- Mapping fibre loops vertically into the product is injective. -/
theorem DiagonalQuotient.product_vertical_loop_map_injective {B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] (b : B) (c : F) :
    Function.Injective
      (fun β : Path.Homotopic.Quotient c c =>
        β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩) := by
  have hleft (β : Path.Homotopic.Quotient c c) :
    (β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨Prod.snd, continuous_snd⟩ =
      β := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  intro α β h
  have hs :=
    congrArg (fun γ : Path.Homotopic.Quotient (b, c) (b, c) => γ.map ⟨Prod.snd, continuous_snd⟩) h
  exact (hleft α).symm.trans (hs.trans (hleft β))

/-- The fibre fundamental-group map is injective. -/
theorem DiagonalQuotient.fibreFundamentalGroupHom_injective {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F) :
    Function.Injective (fibreFundamentalGroupHom (G := G) b c) := by
  intro α β h
  apply product_vertical_loop_map_injective b c
  apply (quotient_isCoveringMap (F := F) hq).injective_path_homotopic_map (b, c) (b, c)
  change
    (Path.Homotopic.Quotient.map α
            ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨quotient G B F, quotient_continuous G B F⟩ =
      (Path.Homotopic.Quotient.map β
            ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨quotient G B F, quotient_continuous G B F⟩
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
  exact h

/-- The fibre fundamental-group image is exactly the kernel of the projection map. -/
theorem DiagonalQuotient.fibreFundamentalGroupHom_range_eq_ker {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range =
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  apply le_antisymm (fibreFundamentalGroupHom_range_le_ker b c)
  intro γ hγ
  change
    Path.Homotopic.Quotient.map γ ⟨projection G B F, projection_continuous G B F⟩ =
      Path.Homotopic.Quotient.refl (baseQuotient G B b) at hγ
  obtain ⟨α, hα⟩ := quotient_loop_lift_of_projection_eq_refl hq b c γ hγ
  have hfst : α.map ⟨Prod.fst, continuous_fst⟩ = Path.Homotopic.Quotient.refl b := by
    apply hq.isCoveringMap.injective_path_homotopic_map b b
    change
      (α.map ⟨Prod.fst, continuous_fst⟩).map ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        Path.Homotopic.Quotient.refl (baseQuotient G B b)
    have hs :
      (α.map ⟨Prod.fst, continuous_fst⟩).map ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        (α.map ⟨quotient G B F, quotient_continuous G B F⟩).map
          ⟨projection G B F, projection_continuous G B F⟩ := by
      rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
      rfl
    exact
      hs.trans
        ((congrArg
              (fun η :
                  Path.Homotopic.Quotient (fibreInclusion G B F b c) (fibreInclusion G B F b c) =>
                η.map ⟨projection G B F, projection_continuous G B F⟩)
              hα).trans
          hγ)
  refine ⟨α.map ⟨Prod.snd, continuous_snd⟩, ?_⟩
  have hv :=
    congrArg
      (fun η : Path.Homotopic.Quotient (b, c) (b, c) =>
        η.map ⟨quotient G B F, quotient_continuous G B F⟩)
      (product_loop_eq_vertical_of_fst_eq_refl b c α hfst)
  rw [← Path.Homotopic.Quotient.map_comp] at hv
  exact hv.symm.trans hα

/-- The homotopy lifting a base loop to a fibre translation by its monodromy element. -/
def DiagonalQuotient.liftedFibreHomotopy {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (γ : Path (baseQuotient G B b) (baseQuotient G B b)) (g : G)
    (hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ : C(F, Space G B F))
      ⟨fun f : F => fibreInclusion G B F b (g • f),
        (fibreInclusion_continuous G B F b).comp (ContinuousConstSMul.continuous_const_smul g)⟩
    where
  toFun p := quotient G B F (hq.isCoveringMap.liftPath γ b γ.source p.1, p.2)
  continuous_toFun :=
    (quotient_continuous G B F).comp
      (((hq.isCoveringMap.liftPath γ b γ.source).continuous.comp continuous_fst).prodMk
        continuous_snd)
  map_zero_left
    f := by
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source 0, f) = quotient G B F (b, f)
    rw [hq.isCoveringMap.liftPath_zero]
  map_one_left
    f := by
    change
      quotient G B F ((hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B), f) =
        quotient G B F (b, g • f)
    rw [hend, quotient_smul_fst, inv_inv]

/-- A homotopy between maps conjugates the induced fundamental-group maps by the evaluation path. -/
theorem DiagonalQuotient.fundamentalGroup_conjugation_of_homotopy {F E : Type*}
    [TopologicalSpace F] [TopologicalSpace E] (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁) (c : F)
    (e : E) (h₀ : f₀ c = e) (h₁ : f₁ c = e) (v : FundamentalGroup F c) :
    let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
    s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ = FundamentalGroup.mapOfEq f₁ h₁ v := by
  let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
  change s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ = FundamentalGroup.mapOfEq f₁ h₁ v
  have hsquare : s * FundamentalGroup.mapOfEq f₀ h₀ v = FundamentalGroup.mapOfEq f₁ h₁ v * s := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
    simp only [s, FundamentalGroup.mul_def, FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_trans]
    apply Path.Homotopic.Quotient.eq.mpr
    have hp := (Path.Homotopic.map_trans_evalAt H p).pathCast h₀.symm h₁.symm
    rw [Path.cast_trans (p.map f₀.continuous) (H.evalAt c) h₀.symm h₀.symm h₁.symm,
      Path.cast_trans (H.evalAt c) (p.map f₁.continuous) h₀.symm h₁.symm h₁.symm] at hp
    exact hp
  rw [hsquare, mul_inv_cancel_right]

/-- Basepoint-change maps compose along composed maps. -/
theorem DiagonalQuotient.fundamentalGroup_mapOfEq_comp {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (a : A) (b : B) (c : C)
    (hf : f a = b) (hg : g b = c) (v : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) v =
      FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf v) := by
  simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
    Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.cast_cast]

/-- The section conjugates a fibre loop by the deck-transport action of the base loop. -/
theorem DiagonalQuotient.sectionFundamentalGroupHom_conjugate_fibre {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (c : F)
    (hc : ∀ g : G, g • c = c) (b : B) (β : FundamentalGroup (BaseSpace G B) (baseQuotient G B b))
    (v : FundamentalGroup F c) :
    sectionFundamentalGroupHom c hc b β * fibreFundamentalGroupHom b c v *
        (sectionFundamentalGroupHom c hc b β)⁻¹ =
      fibreFundamentalGroupHom b c
        (fibreActionFundamentalGroupHom c hc (deckTransportHom hq b β) v) := by
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective β
  let g : G := deckTransportHom hq b (.mk γ)
  have hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b :=
    (deckTransportHom_monodromy hq b (.mk γ)).symm
  let i : C(F, Space G B F) := ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩
  let a : C(F, F) := ⟨fun f : F => g • f, ContinuousConstSMul.continuous_const_smul g⟩
  let H : i.Homotopy (i.comp a) := liftedFibreHomotopy (F := F) hq b γ g hend
  have h₁ : (i.comp a) c = i c := congrArg i (hc g)
  let s : FundamentalGroup (Space G B F) (i c) := .mk ((H.evalAt c).cast rfl h₁.symm)
  have hs : s = sectionFundamentalGroupHom c hc b (.mk γ) := by
    change
      Path.Homotopic.Quotient.mk ((H.evalAt c).cast rfl h₁.symm) =
        Path.Homotopic.Quotient.mk (γ.map (zeroSection_continuous c hc))
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source t, c) = zeroSection c hc (γ t)
    have hlift : baseQuotient G B (hq.isCoveringMap.liftPath γ b γ.source t) = γ t :=
      congrFun (hq.isCoveringMap.liftPath_lifts γ b γ.source) t
    exact congrArg (zeroSection c hc) hlift
  have hi (w : FundamentalGroup F c) :
    FundamentalGroup.mapOfEq i rfl w = fibreFundamentalGroupHom b c w := by
    rw [FundamentalGroup.mapOfEq_apply]
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  have hterminal :
    FundamentalGroup.mapOfEq (i.comp a) h₁ v =
      fibreFundamentalGroupHom b c (fibreActionFundamentalGroupHom c hc g v) := by
    have hcomp := fundamentalGroup_mapOfEq_comp a i c c (i c) (hc g) rfl v
    rw [hi] at hcomp
    exact hcomp
  have hconj := fundamentalGroup_conjugation_of_homotopy i (i.comp a) H c (i c) rfl h₁ v
  change
    s * FundamentalGroup.mapOfEq i rfl v * s⁻¹ = FundamentalGroup.mapOfEq (i.comp a) h₁ v at hconj
  rw [hs, hi, hterminal] at hconj
  exact hconj

/-! ### Sections from local inverses -/

/-- The map `U × F → Space` built from a continuous local section of the base quotient. -/
def DiagonalQuotient.sectionMap {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B)) (x : U × F) :
    Space G B F :=
  quotient G B F (s x.1, x.2)

/-- The section map is continuous. -/
theorem DiagonalQuotient.sectionMap_continuous {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B)) :
    Continuous (sectionMap (F := F) U s) :=
  (quotient_continuous G B F).comp (s.continuous.prodMap continuous_id)

/-- A continuous section of the base quotient is an open embedding. -/
theorem DiagonalQuotient.baseSection_openEmbedding {G B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) : Topology.IsOpenEmbedding s := by
  apply hq.isCoveringMap.isLocalHomeomorph.isOpenEmbedding_of_comp _ s.continuous
  have hcomp : baseQuotient G B ∘ s = (Subtype.val : U → BaseSpace G B) := funext hs
  rw [hcomp]
  exact U.isOpenEmbedding'

/-- The section map projects to its first component. -/
@[simp]
theorem DiagonalQuotient.projection_sectionMap {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U × F) :
    projection G B F (sectionMap U s x) = (x.1 : BaseSpace G B) :=
  hs x.1

/-- The section map is injective. -/
theorem DiagonalQuotient.sectionMap_injective {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) : Function.Injective (sectionMap (F := F) U s) := by
  intro x y hxy
  have hbase : x.1 = y.1 :=
    Subtype.ext
      (by simpa only [projection_sectionMap U s hs] using congrArg (projection G B F) hxy)
  apply Prod.ext hbase
  apply fibreInclusion_injective hq (s y.1)
  simpa only [sectionMap, fibreInclusion, hbase] using hxy

/-- The range of the section map is the preimage of `U`. -/
theorem DiagonalQuotient.sectionMap_range {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    Set.range (sectionMap (F := F) U s) = projection G B F ⁻¹' (U : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, projection_sectionMap U s hs]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ U at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (hs ⟨baseQuotient G B z, hy⟩)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg rfl⟩

/-- The section map is an open embedding. -/
theorem DiagonalQuotient.sectionMap_openEmbedding {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    Topology.IsOpenEmbedding (sectionMap (F := F) U s) :=
  .of_continuous_injective_isOpenMap (sectionMap_continuous U s) (sectionMap_injective hq U s hs)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseSection_openEmbedding hq U s hs).isOpenMap.prodMap IsOpenMap.id))

/-- The preimage of a section domain is homeomorphic to `U × F`. -/
def DiagonalQuotient.sectionHomeomorph {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    (projection G B F ⁻¹' (U : Set _)) ≃ₜ (U × F) :=
  ((sectionMap_openEmbedding (F := F) hq U s hs).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (sectionMap_range hq U s hs))).symm

/-- The section homeomorphism's first component is the projection. -/
theorem DiagonalQuotient.sectionHomeomorph_projection {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (x : projection G B F ⁻¹' (U : Set _)) :
    ((sectionHomeomorph hq U s hs x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_sectionMap U s hs (sectionHomeomorph hq U s hs x)
  have he : sectionMap U s (sectionHomeomorph hq U s hs x) = x.val :=
    congrArg Subtype.val ((sectionHomeomorph hq U s hs).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

/-- The section homeomorphism computes on quotient points. -/
@[simp]
theorem DiagonalQuotient.sectionHomeomorph_apply_quotient {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U) (f : F) :
    sectionHomeomorph hq U s hs
        ⟨quotient G B F (s x, f), by
          change baseQuotient G B (s x) ∈ U
          rw [hs x]
          exact x.property⟩ =
      (x, f) :=
  (sectionHomeomorph hq U s hs).apply_symm_apply (x, f)

/-! ### Basepoint change along the fibre -/

/-- Basepoint change along the evaluation path identifies the two induced maps. -/
theorem DiagonalQuotient.fundamentalGroup_basepointChange_of_homotopy {F E : Type*}
    [TopologicalSpace F] [TopologicalSpace E] (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁) (c : F)
    (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt c) (FundamentalGroup.map f₀ c v) =
      FundamentalGroup.map f₁ c v := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
  rw [fundamentalGroup_basepoint_change_apply]
  change
    (Path.Homotopic.Quotient.mk (H.evalAt c)).symm.trans
        ((Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
          (Path.Homotopic.Quotient.mk (H.evalAt c))) =
      Path.Homotopic.Quotient.mk (p.map f₁.continuous)
  have hsquare :
    (Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
        (Path.Homotopic.Quotient.mk (H.evalAt c)) =
      (Path.Homotopic.Quotient.mk (H.evalAt c)).trans
        (Path.Homotopic.Quotient.mk (p.map f₁.continuous)) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p)
  rw [hsquare, ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- A base path gives a homotopy between the fibre inclusions at its endpoints. -/
def DiagonalQuotient.fibreBasepointHomotopy {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] {b₀ b₁ : B} (p : Path b₀ b₁) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b₀, fibreInclusion_continuous G B F b₀⟩ : C(F, Space G B F))
      ⟨fibreInclusion G B F b₁, fibreInclusion_continuous G B F b₁⟩
    where
  toFun x := quotient G B F (p x.1, x.2)
  continuous_toFun :=
    (quotient_continuous G B F).comp ((p.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left
    f := by
    change quotient G B F (p 0, f) = quotient G B F (b₀, f)
    rw [p.source]
  map_one_left
    f := by
    change quotient G B F (p 1, f) = quotient G B F (b₁, f)
    rw [p.target]

/-- The path between fibre inclusions traced at a fixed fibre point. -/
def DiagonalQuotient.fibreBasepointPath {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] (c : F) {b₀ b₁ : B} (p : Path b₀ b₁) :
    Path (fibreInclusion G B F b₀ c) (fibreInclusion G B F b₁ c) :=
  (fibreBasepointHomotopy (G := G) (F := F) p).evalAt c

/-- The fibre fundamental-group maps at two basepoints differ by the connecting path. -/
theorem DiagonalQuotient.fibreFundamentalGroupHom_baseChange {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) {b₀ b₁ : B}
    (p : Path b₀ b₁) (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (fibreBasepointPath (G := G) c p)
        (fibreFundamentalGroupHom (G := G) b₀ c v) =
      fibreFundamentalGroupHom (G := G) b₁ c v :=
  fundamentalGroup_basepointChange_of_homotopy _ _ (fibreBasepointHomotopy (G := G) (F := F) p) c
    v
