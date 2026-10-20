/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.OrientationCover

/-!
# Orientations of a manifold

A *local orientation* of an `n`-manifold `M` at `x` is a generator of the local homology
`H_n(M, M ∖ {x}) ≅ ℤ`, and an *orientation* is a locally consistent choice of local orientations
(Hatcher, *Algebraic Topology*, §3.3): a family `μ : ∀ x, H_n(M, M ∖ {x})` of generators such
that every point has a compact homology ball `K` (`x ∈ interior K`) and a class
`β ∈ H_n(M, M ∖ K)` restricting to `μ y` for all `y ∈ K`.

* `ManifoldOrientation.IsGenerator`, `ManifoldOrientation.IsLocallyConsistent`,
  `ManifoldOrientation.Orientation M n`, `ManifoldOrientation.IsOrientable M n`.

Sections of the local homology covering give locally consistent families
(`isLocallyConsistent_sectionClass`), and the lifting criterion for covering spaces gives the
first existence theorem: **a simply connected manifold is orientable**
(`isOrientable_of_simplyConnectedSpace`, Hatcher, the corollary of Proposition 3.25): the
identity of `M` lifts through the covering `proj : LocalHomologyCover M n → M` starting at a
generator, the lifted section is locally consistent, and the set of points where it is a
generator is clopen.

## Main definitions and results

* `ManifoldOrientation.Orientation`, `ManifoldOrientation.IsOrientable`.
* `ManifoldOrientation.isGenerator_localRestriction_iff` : along a homology ball, generators
  correspond to generators.
* `ManifoldOrientation.sectionClass`, `ManifoldOrientation.isLocallyConsistent_sectionClass`.
* `ManifoldOrientation.isOrientable_of_simplyConnectedSpace`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, orientations and Proposition 3.25

## Tags

orientation, local orientation, simply connected, covering space
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open RelativeSingularHomology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

/-! ### Generators and local consistency -/

/-- A class of the local homology at `x` is a generator if it spans. -/
def IsGenerator {x : M} (μ : localHomology M x n) : Prop := Submodule.span ℤ {μ} = ⊤

/-- Generators correspond under linear equivalences. -/
theorem span_singleton_eq_top_iff_of_linearEquiv {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (e : A ≃ₗ[ℤ] B) (a : A) :
    Submodule.span ℤ {e a} = ⊤ ↔ Submodule.span ℤ {a} = ⊤ := by
  rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_span, Set.image_singleton]
  rfl

/-- A linear equivalence with `ℤ` carries `1` to a generator. -/
theorem span_singleton_symm_one_eq_top {A : Type*} [AddCommGroup A] [Module ℤ A] (e : A ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ {e.symm 1} = ⊤ := by
  rw [← span_singleton_eq_top_iff_of_linearEquiv e, e.apply_symm_apply, eq_top_iff]
  intro m _
  rw [Submodule.mem_span_singleton]
  exact ⟨m, by simp⟩

/-- Along a homology ball, the restriction of `β` at `y ∈ K` is a generator iff `β` spans. -/
theorem isGenerator_localRestriction_iff {K : Set M} (hKb : IsHomologyBall M n K) {y : M} (hy : y ∈ K)
    (β : RelativeHomology M Kᶜ n) :
    IsGenerator (localRestriction hy n β) ↔ Submodule.span ℤ {β} = ⊤ :=
  span_singleton_eq_top_iff_of_linearEquiv (LinearEquiv.ofBijective _ (hKb y hy)) β

/-- A family of local classes is locally consistent if every point has a compact homology ball
`K` with the point in its interior and a class `β ∈ H_n(M, M ∖ K)` restricting to the family on
`K`. -/
def IsLocallyConsistent (s : ∀ x : M, localHomology M x n) : Prop :=
  ∀ x, ∃ K : Set M, IsCompact K ∧ IsHomologyBall M n K ∧ x ∈ interior K ∧
    ∃ β : RelativeHomology M Kᶜ n, ∀ y (hy : y ∈ K), s y = localRestriction hy n β

/-- For a locally consistent family, the set of points where it is a generator is clopen. -/
theorem isClopen_isGenerator_of_isLocallyConsistent {s : ∀ x : M, localHomology M x n}
    (hs : IsLocallyConsistent s) : IsClopen {x | IsGenerator (s x)} := by
  have key : ∀ x, ∃ U ∈ 𝓝 x, ∀ y ∈ U, (IsGenerator (s y) ↔ IsGenerator (s x)) := by
    intro x
    obtain ⟨K, _, hKb, hxK, β, hβ⟩ := hs x
    refine ⟨interior K, isOpen_interior.mem_nhds hxK, fun y hy => ?_⟩
    rw [hβ y (interior_subset hy), hβ x (interior_subset hxK),
      isGenerator_localRestriction_iff hKb, isGenerator_localRestriction_iff hKb]
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hUx⟩ := key x
    exact Filter.mem_of_superset hU fun y hy => fun hgen => hx ((hUx y hy).mp hgen)
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hUx⟩ := key x
    exact Filter.mem_of_superset hU fun y hy => (hUx y hy).mpr hx

/-- **An orientation** of `M` in degree `n`: a locally consistent family of generators of the local
homology groups (Hatcher, §3.3). -/
structure Orientation (M : Type) [TopologicalSpace M] (n : ℕ) where
  /-- The local orientation at each point. -/
  cls : ∀ x : M, localHomology M x n
  /-- Each local orientation generates the local homology. -/
  isGenerator : ∀ x, IsGenerator (cls x)
  /-- The local orientations are locally consistent. -/
  isLocallyConsistent : IsLocallyConsistent cls

/-- `M` is orientable in degree `n` if it has an orientation. -/
def IsOrientable (M : Type) [TopologicalSpace M] (n : ℕ) : Prop := Nonempty (Orientation M n)

/-! ### Sections of the local homology covering -/

/-- A point of the total space over `x` is `⟨x, μ⟩` for a unique `μ`. -/
theorem exists_eq_mk (p : Σ x : M, localHomology M x n) {x : M} (h : p.1 = x) :
    ∃ μ : localHomology M x n, p = ⟨x, μ⟩ := by
  subst h
  exact ⟨p.2, rfl⟩

/-- The family of local classes of a section `F` of the local homology covering. -/
def sectionClass (F : M → LocalHomologyCover M n) (hF : ∀ x, (F x).1 = x) (x : M) :
    localHomology M x n :=
  Classical.choose (exists_eq_mk (F x) (hF x))

theorem sectionClass_spec (F : M → LocalHomologyCover M n) (hF : ∀ x, (F x).1 = x) (x : M) :
    F x = LocalHomologyCover.mk x (sectionClass F hF x) :=
  Classical.choose_spec (exists_eq_mk (F x) (hF x))

section Manifold

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]

/-- The family of local classes of a continuous section is locally consistent. -/
theorem isLocallyConsistent_sectionClass (F : C(M, LocalHomologyCover M n)) (hF : ∀ x, (F x).1 = x) :
    IsLocallyConsistent (sectionClass F hF) := by
  intro x
  obtain ⟨K, hK, hKb, β, _, hFx⟩ :=
    exists_generating_sheet_mem (F x) (U := Set.univ) Filter.univ_mem
  have hW : IsOpen (F ⁻¹' sheet K β) := (isOpen_sheet hK hKb β).preimage F.continuous
  have hxK : x ∈ interior K := by
    have := hFx.1
    rwa [hF x] at this
  obtain ⟨K', hK', hK'sub, hxK', hK'b⟩ := exists_isHomologyBall (n := n) x
    (Filter.inter_mem (hW.mem_nhds hFx) (isOpen_interior.mem_nhds hxK)) n
  have hK'K : K' ⊆ K := hK'sub.trans (inter_subset_right.trans interior_subset)
  refine ⟨K', hK', hK'b, hxK', restriction (compl_subset_compl.mpr hK'K) n β, fun y hy => ?_⟩
  have hFy : F y ∈ sheet K β := (hK'sub hy).1
  rw [sectionClass_spec F hF y] at hFy
  obtain ⟨hyK, hβ⟩ := hFy
  change y ∈ interior K at hyK
  change sectionClass F hF y = localRestriction (interior_subset hyK) n β at hβ
  rw [hβ]
  exact (LinearMap.congr_fun (localRestriction_comp_restriction hK'K hy n) β).symm

/-- **A simply connected manifold is orientable** (Hatcher, §3.3, after Proposition 3.25): for
`n ≥ 2`, a simply connected `T₂` manifold modelled on `ℝⁿ` has an orientation in degree `n`. -/
theorem isOrientable_of_simplyConnectedSpace [SimplyConnectedSpace M] (hn : 2 ≤ n) :
    IsOrientable M n := by
  have : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  -- a generator at a base point
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨e⟩ := localHomology_equiv_int hn x₀
  set μ₀ : localHomology M x₀ n := e.symm 1 with hμ₀
  have hgen₀ : IsGenerator μ₀ := span_singleton_symm_one_eq_top e
  -- lift the identity through the covering
  obtain ⟨F, ⟨hF₀, hFproj⟩, -⟩ := isCoveringMap_proj.existsUnique_continuousMap_lifts
    (ContinuousMap.id M) x₀ (LocalHomologyCover.mk x₀ μ₀) rfl
  have hF : ∀ x, (F x).1 = x := fun x => congrFun hFproj x
  -- the section is locally consistent, and generates at `x₀`
  have hcons := isLocallyConsistent_sectionClass F hF
  have hgen : ∀ x, IsGenerator (sectionClass F hF x) := by
    have hclopen := isClopen_isGenerator_of_isLocallyConsistent hcons
    have hx₀ : x₀ ∈ {x | IsGenerator (sectionClass F hF x)} := by
      change IsGenerator (sectionClass F hF x₀)
      have h := sectionClass_spec F hF x₀
      rw [hF₀] at h
      have : μ₀ = sectionClass F hF x₀ := by
        have h' : (⟨x₀, μ₀⟩ : Σ x : M, localHomology M x n) = ⟨x₀, sectionClass F hF x₀⟩ := h
        exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
      rw [← this]
      exact hgen₀
    have huniv := hclopen.eq_univ ⟨x₀, hx₀⟩
    intro x
    have : x ∈ {x | IsGenerator (sectionClass F hF x)} := by rw [huniv]; trivial
    exact this
  exact ⟨⟨sectionClass F hF, hgen, hcons⟩⟩

end Manifold

end ManifoldOrientation
