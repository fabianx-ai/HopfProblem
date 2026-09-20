/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Invariant subset quotients and product restriction

  Quotients by actions restricted to invariant subsets, and the restriction of
  quotient maps to products (Forster, Lectures on Riemann Surfaces, Sections
  1-2).
-/



open Set Function Filter Manifold Topology

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Quotient coverings on an invariant subset -/

/-- The quotient map restricted to an invariant subset's image. -/
def InvariantSubsetQuotient.imageProject {M Q : Type*} (q : M → Q) (S : Set M) (x : S) : q '' S :=
  ⟨q x, x, x.2, rfl⟩

/-- The restricted projection is surjective. -/
theorem InvariantSubsetQuotient.imageProject_surjective {M Q : Type*} {q : M → Q} {S : Set M} :
    Function.Surjective (imageProject q S) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The restricted projection is continuous. -/
theorem InvariantSubsetQuotient.imageProject_continuous {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] (hq : Continuous q) :
    Continuous (imageProject q S) :=
  (hq.comp continuous_subtype_val).subtype_mk _

/-- For a quotient covering, the preimage of `q '' S` is `S`. -/
theorem InvariantSubsetQuotient.preimage_image_eq {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : q ⁻¹' (q '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hxy.symm
    have he : ((g • (⟨y, hy⟩ : S) : S) : M) = x := (hcompat g ⟨y, hy⟩).trans hg
    exact he ▸ (g • (⟨y, hy⟩ : S)).2
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- `S` is homeomorphic to the preimage of its image. -/
def InvariantSubsetQuotient.preimageImageHomeomorph {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : S ≃ₜ q ⁻¹' (q '' S) :=
  Homeomorph.setCongr (InvariantSubsetQuotient.preimage_image_eq hq hcompat).symm

/-- The restricted projection is a covering map. -/
theorem InvariantSubsetQuotient.imageProject_isCoveringMap {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    IsCoveringMap (imageProject q S) := by
  exact
    (hq.isCoveringMap.restrictPreimage (q '' S)).comp_homeomorph
      (preimageImageHomeomorph hq hcompat)

/-- The `G`-action on `S` is continuous in each element. -/
theorem InvariantSubsetQuotient.subtypeAction_continuousConstSMul {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : ContinuousConstSMul G S where
  continuous_const_smul
    g := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    simpa only [Function.comp_def, hcompat] using
      (hq.continuous_const_smul g).comp continuous_subtype_val

/-- Two points of `S` project equally exactly when they share an orbit. -/
theorem InvariantSubsetQuotient.imageProject_eq_iff_mem_orbit {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) {x y : S} :
    imageProject q S x = imageProject q S y ↔ x ∈ MulAction.orbit G y := by
  rw [Subtype.ext_iff]
  change q x = q y ↔ _
  rw [hq.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩

/-- The restricted projection is a quotient covering. -/
theorem InvariantSubsetQuotient.imageProject_isQuotientCoveringMap {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    IsQuotientCoveringMap (imageProject q S) G
    where
  __ := (imageProject_isCoveringMap hq hcompat).isQuotientMap imageProject_surjective
  __ := subtypeAction_continuousConstSMul hq hcompat
  apply_eq_iff_mem_orbit := imageProject_eq_iff_mem_orbit hq hcompat
  disjoint
    x := by
    obtain ⟨U, hU, hdisj⟩ := hq.disjoint (x : M)
    refine
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, fun g hg =>
        ?_⟩
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ := hg
    apply hdisj g
    refine ⟨(y : M), ⟨(z : M), hz, ?_⟩, hy⟩
    exact (hcompat g z).symm.trans (congrArg Subtype.val hzy)

/-- The orbit quotient of `S` is equivalent to `q '' S`. -/
def InvariantSubsetQuotient.quotientEquiv {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    Quotient (MulAction.orbitRel G S) ≃ q '' S :=
  (Quotient.congrRight (fun _ _ => (imageProject_eq_iff_mem_orbit hq hcompat).symm)).trans
    (Setoid.quotientKerEquivOfSurjective (imageProject q S) imageProject_surjective)

/-- The equivalence sends an orbit to its image point. -/
@[simp]
theorem InvariantSubsetQuotient.quotientEquiv_mk {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (x : S) :
    quotientEquiv hq hcompat (Quotient.mk (MulAction.orbitRel G S) x) = imageProject q S x :=
  rfl

/-- The inverse sends an image point to its orbit. -/
@[simp]
theorem InvariantSubsetQuotient.quotientEquiv_symm_imageProject {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (x : S) :
    (quotientEquiv hq hcompat).symm (imageProject q S x) =
      Quotient.mk (MulAction.orbitRel G S) x := by
  rw [← quotientEquiv_mk hq hcompat x, Equiv.symm_apply_apply]

/-- The orbit quotient of `S` is homeomorphic to `q '' S`. -/
def InvariantSubsetQuotient.quotientHomeomorph {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    Quotient (MulAction.orbitRel G S) ≃ₜ q '' S
    where
  toEquiv := quotientEquiv hq hcompat
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr (imageProject_continuous hq.continuous)
  continuous_invFun := by
    apply (imageProject_isQuotientCoveringMap hq hcompat).toIsQuotientMap.continuous_iff.mpr
    change Continuous ((quotientEquiv hq hcompat).symm ∘ imageProject q S)
    have he :
      (quotientEquiv hq hcompat).symm ∘ imageProject q S = Quotient.mk (MulAction.orbitRel G S) :=
      by
      funext x
      exact quotientEquiv_symm_imageProject hq hcompat x
    rw [he]
    exact continuous_quotient_mk'

/-- The image of a closed invariant subset is closed. -/
theorem InvariantSubsetQuotient.isClosed_image {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (hS : IsClosed S) :
    IsClosed (q '' S) := by
  apply hq.isCoinducing.isClosed_preimage.mp
  rwa [InvariantSubsetQuotient.preimage_image_eq hq hcompat]

/-! ### Product restrictions of maps -/

/-- `K × B` is homeomorphic to the preimage of `C` under a fiberwise map. -/
def ProductRestriction.productPreimageHomeomorph {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] (f : K × X → Y) (B : Set X) (C : Set Y) (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) :
    K × B ≃ₜ (f ⁻¹' C)
    where
  toFun p := ⟨(p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩
  invFun p := (p.1.1, ⟨p.1.2, (hpre _).mp p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

/-- A product map restricted to `K × B → C`. -/
def ProductRestriction.productRestriction {K X Y : Type*} (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (p : K × B) : C :=
  ⟨f (p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩

/-- The product restriction is continuous. -/
theorem ProductRestriction.productRestriction_continuous {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] [TopologicalSpace Y] (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (hf : Continuous f) :
    Continuous (productRestriction f B C hpre) :=
  hf.restrictPreimage.comp (productPreimageHomeomorph f B C hpre).continuous

/-- The product restriction of a closed map is closed. -/
theorem ProductRestriction.productRestriction_isClosedMap {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] [TopologicalSpace Y] (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (hf : IsClosedMap f) :
    IsClosedMap (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).isClosedMap

/-- The product restriction of a surjective map is surjective. -/
theorem ProductRestriction.productRestriction_surjective {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] (f : K × X → Y) (B : Set X) (C : Set Y) (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B)
    (hf : Function.Surjective f) : Function.Surjective (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).surjective
