/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Topology.Algebra.FreeActionLocus
import Lib.Geometry.Manifold.Instances.RiemannSphere
/-!
# The local orbit quotient of a group action

  The local orbit quotient: for a properly discontinuous group action, the
  quotient of a small neighborhood of a point by the stabilizer-free action of
  the group elements mapping it into itself, is modeled on the quotient by a
  finite group (Forster, Lectures on Riemann Surfaces, Section 1).
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

/-! ### The local orbit quotient -/

/-- The `H`-action on an `H`-invariant open set. -/
@[instance_reducible]
def LocalOrbitQuotient.restrictedAction {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) : MulAction H U
    where
  smul h x := ⟨(h : G) • (x : X), hU h x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : X))
  mul_smul h k x := Subtype.ext (SemigroupAction.mul_smul (h : G) (k : G) (x : X))

/-- The orbit quotient of the restricted `H`-action on `U`. -/
abbrev LocalOrbitQuotient.LocalQuotient {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :=
  letI := restrictedAction H U hU
  Quotient (MulAction.orbitRel H U)

/-- The projection of `U` onto its `H`-orbit quotient. -/
def LocalOrbitQuotient.localProjection {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) : U → LocalQuotient H U hU :=
  Quotient.mk _

/-- Two points project equally exactly when an `H` element relates them. -/
theorem LocalOrbitQuotient.localProjection_eq_iff {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) (x y : U) :
    localProjection H U hU x = localProjection H U hU y ↔ ∃ h : H, (h : G) • (y : X) = (x : X) := by
  let := restrictedAction H U hU
  rw [localProjection, Quotient.eq]
  change (∃ h : H, h • y = x) ↔ _
  exact exists_congr fun h => Subtype.ext_iff

/-- The local projection is surjective. -/
theorem LocalOrbitQuotient.localProjection_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :
    Function.Surjective (localProjection H U hU) :=
  Quotient.mk_surjective

/-- The local projection is continuous. -/
theorem LocalOrbitQuotient.localProjection_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :
    Continuous (localProjection H U hU) :=
  continuous_quotient_mk'

/-! ### Comparing with the global orbit space -/

/-- The open image of `U` in the global orbit quotient. -/
def LocalOrbitQuotient.imageOpen {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    TopologicalSpace.Opens (Quotient (MulAction.orbitRel G X)) :=
  ⟨Quotient.mk (MulAction.orbitRel G X) '' (U : Set X),
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ U.isOpen⟩

/-- The projection of `U` onto its image in the global quotient. -/
def LocalOrbitQuotient.imageProjection {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    U → imageOpen (G := G) U := fun x => ⟨Quotient.mk _ (x : X), x, x.property, rfl⟩

/-- The image projection is surjective. -/
theorem LocalOrbitQuotient.imageProjection_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    Function.Surjective (imageProjection (G := G) U) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The image projection is continuous. -/
theorem LocalOrbitQuotient.imageProjection_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    Continuous (imageProjection (G := G) U) :=
  (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

/-- The image projection is an open map. -/
theorem LocalOrbitQuotient.imageProjection_isOpenMap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    IsOpenMap (imageProjection (G := G) U) :=
  (MulAction.isOpenQuotientMap_quotientMk.isOpenMap.comp
        U.isOpen.isOpenMap_subtype_val).subtype_mk
    _

/-- The image projection is an open quotient map. -/
theorem LocalOrbitQuotient.imageProjection_isOpenQuotientMap {G X : Type*} [Group G]
    [TopologicalSpace X] [MulAction G X] (U : TopologicalSpace.Opens X)
    [ContinuousConstSMul G X] : IsOpenQuotientMap (imageProjection (G := G) U) :=
  ⟨imageProjection_surjective U, imageProjection_continuous U, imageProjection_isOpenMap U⟩

/-! ### The local-to-global comparison -/

/-- The map from the local `H`-quotient to the global quotient image. -/
def LocalOrbitQuotient.localToImage {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    LocalQuotient H U hU → imageOpen (G := G) U :=
  Quotient.lift (imageProjection (G := G) U) fun x y h =>
    by
    apply Subtype.ext
    apply Quotient.sound
    obtain ⟨g, hg⟩ := h
    exact ⟨(g : G), congrArg Subtype.val hg⟩

/-- The local-to-global comparison is continuous. -/
theorem LocalOrbitQuotient.localToImage_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    Continuous (localToImage H U hU) :=
  (imageProjection_continuous U).quotient_lift _

/-- The local-to-global comparison is surjective. -/
theorem LocalOrbitQuotient.localToImage_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    Function.Surjective (localToImage H U hU) := by
  intro q
  obtain ⟨x, rfl⟩ := imageProjection_surjective U q
  exact ⟨localProjection H U hU x, rfl⟩

/-- The local-to-global comparison is an open map. -/
theorem LocalOrbitQuotient.localToImage_isOpenMap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    IsOpenMap (localToImage H U hU) :=
  IsOpenMap.of_comp (localProjection_continuous H U hU) (localProjection_surjective H U hU)
    (imageProjection_isOpenMap U)

/-- When only `H` returns `U` to itself the comparison is injective. -/
theorem LocalOrbitQuotient.localToImage_injective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X]
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    Function.Injective (localToImage H U hU) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  have hxy :
    Quotient.mk (MulAction.orbitRel G X) (x : X) = Quotient.mk (MulAction.orbitRel G X) (y : X) :=
    congrArg Subtype.val h
  obtain ⟨g, hg⟩ := Quotient.exact hxy
  have hgH : g ∈ H := hreturn g ⟨x, ⟨y, y.property, hg⟩, x.property⟩
  exact (localProjection_eq_iff H U hU x y).mpr ⟨⟨g, hgH⟩, hg⟩

def LocalOrbitQuotient.localHomeomorph {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X]
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    LocalQuotient H U hU ≃ₜ imageOpen (G := G) U :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (localToImage H U hU)
      ⟨localToImage_injective H U hU hreturn, localToImage_surjective H U hU⟩)
    (localToImage_continuous H U hU) (localToImage_isOpenMap H U hU)
