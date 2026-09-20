/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The one-point collapse `X ⊔ {∞}` with the quotient topology

`OnePointCollapse.collapse` realizes the one-point (Alexandroff) compactification picture
for a locally compact noncompact space: a homeomorphism between the complement of a
compact subset and its image, with the remainder collapsed to a point
(`SixSphereCube.collapse`, `isQuotientMap_collapse` — the namespace `SixSphereCube` is
renamed to `OnePointCollapse` in the lane rename commit).

Consumed by the sphere presentations of
`Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` (the sphere `Sⁿ` as the
one-point compactification of `ℝⁿ`).

## Outline of the construction

1. *The collapsed space.*  `collapse` defines the quotient map; `isQuotientMap_collapse`
   proves it is a quotient map.
2. *Interior recognition.*  `collapse_interior`-family lemmas identify the interior of the
   collapsed part, so the collapsed space is the original space plus one point.

## Main definitions and results

* `OnePointCollapse.collapse` : the collapse map to the quotient.
* `OnePointCollapse.isQuotientMap_collapse` : it is a quotient map.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §0 (CW complexes, one-point
  compactification as a quotient)

## Tags

one-point compactification, quotient topology, collapse
-/



open Set Function Filter Manifold Topology

@[expose] public noncomputable section

/-! ### The collapse map to the one-point compactification -/

/-- The map collapsing `F` to the point at infinity of `OnePoint Fᶜ`. -/
def OnePointCollapse.collapse {K : Type*} (F : Set K) (a : K) : OnePoint ↥Fᶜ := by
  classical exact if h : a ∈ F then (OnePoint.infty) else ((⟨a, h⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ)

/-- Points of `F` collapse to infinity. -/
@[simp]
theorem OnePointCollapse.collapse_of_mem {K : Type*} (F : Set K) {a : K} (ha : a ∈ F) :
    collapse F a = (OnePoint.infty) := by classical simp only [collapse, dif_pos ha]

/-- Points off `F` collapse to their image. -/
theorem OnePointCollapse.collapse_of_not_mem {K : Type*} (F : Set K) {a : K} (ha : a ∉ F) :
    collapse F a = ((⟨a, ha⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ) := by
  classical simp only [collapse, dif_neg ha]

/-- A complement point collapses to its image. -/
@[simp]
theorem OnePointCollapse.collapse_coe {K : Type*} (F : Set K) (a : ↥Fᶜ) :
    collapse F a.val = (a : OnePoint ↥Fᶜ) :=
  collapse_of_not_mem F a.property

/-- The collapse hits infinity exactly on `F`. -/
@[simp]
theorem OnePointCollapse.collapse_eq_infty_iff {K : Type*} (F : Set K) (a : K) :
    collapse F a = (OnePoint.infty) ↔ a ∈ F := by
  classical
  by_cases ha : a ∈ F
  · simp only [OnePointCollapse.collapse_of_mem F ha, ha]
  · simp only [collapse_of_not_mem F ha, OnePoint.coe_ne_infty, ha]

/-- Collapses agree exactly on equal points or inside `F`. -/
theorem OnePointCollapse.collapse_eq_iff {K : Type*} (F : Set K) (a b : K) :
    collapse F a = collapse F b ↔ a = b ∨ a ∈ F ∧ b ∈ F := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ F
    · exact
        Or.inr
          ⟨ha, (collapse_eq_infty_iff F b).mp (h.symm.trans (OnePointCollapse.collapse_of_mem F ha))⟩
    · have hb : b ∉ F := fun hb =>
        ha ((collapse_eq_infty_iff F a).mp (h.trans (OnePointCollapse.collapse_of_mem F hb)))
      rw [collapse_of_not_mem F ha, collapse_of_not_mem F hb] at h
      exact Or.inl (congrArg Subtype.val (OnePoint.coe_injective h))
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [OnePointCollapse.collapse_of_mem F ha, OnePointCollapse.collapse_of_mem F hb]

/-- The collapse of a nonempty `F` is surjective. -/
theorem OnePointCollapse.collapse_surjective {K : Type*} (F : Set K) (hne : F.Nonempty) :
    Function.Surjective (collapse F) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, OnePointCollapse.collapse_of_mem F ha⟩
  | coe a => exact ⟨a.val, collapse_coe F a⟩

/-- The preimage of a set avoiding infinity is the image of the complement. -/
theorem OnePointCollapse.collapse_preimage_of_not_mem {K : Type*} (F : Set K)
    (s : Set (OnePoint ↥Fᶜ)) (hs : (OnePoint.infty) ∉ s) :
    collapse F ⁻¹' s = Subtype.val '' (((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s) := by
  ext a
  constructor
  · intro ha
    change collapse F a ∈ s at ha
    have haF : a ∉ F := by
      intro haF
      exact hs (by simpa only [OnePointCollapse.collapse_of_mem F haF] using ha)
    exact ⟨⟨a, haF⟩, by simpa only [Set.mem_preimage, collapse_of_not_mem F haF] using ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [Set.mem_preimage, collapse_coe] using hb

/-- The complement of a preimage containing infinity is the complement image. -/
theorem OnePointCollapse.collapse_preimage_compl_of_mem {K : Type*} (F : Set K)
    (s : Set (OnePoint ↥Fᶜ)) (hs : (OnePoint.infty) ∈ s) :
    (collapse F ⁻¹' s)ᶜ = Subtype.val '' ((((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s)ᶜ) :=
  collapse_preimage_of_not_mem F sᶜ (fun h => h hs)

/-- The collapse of a closed set in a Hausdorff space is continuous. -/
theorem OnePointCollapse.continuous_collapse {K : Type*} [TopologicalSpace K] [T2Space K] (F : Set K)
    (hF : IsClosed F) : Continuous (collapse F) := by
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hinf : (OnePoint.infty) ∈ s
  · apply isClosed_compl_iff.mp
    rw [collapse_preimage_compl_of_mem F s hinf]
    exact (((OnePoint.isOpen_def.mp hs).1 hinf).image continuous_subtype_val).isClosed
  · rw [collapse_preimage_of_not_mem F s hinf]
    exact hF.isOpen_compl.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hs).2

/-- The collapse as a continuous map. -/
def OnePointCollapse.collapseMap {K : Type*} [TopologicalSpace K] [T2Space K] (F : Set K)
    (hF : IsClosed F) : C(K, OnePoint ↥Fᶜ) :=
  ⟨collapse F, continuous_collapse F hF⟩

/-- The collapse of a compact Hausdorff space is a quotient map. -/
theorem OnePointCollapse.isQuotientMap_collapse {K : Type*} [TopologicalSpace K] [T2Space K]
    (F : Set K) [CompactSpace K] (hF : IsClosed F) (hne : F.Nonempty) :
    Topology.IsQuotientMap (collapse F) := by
  let : LocallyCompactSpace ↥Fᶜ := hF.isOpen_compl.locallyCompactSpace
  exact
    Topology.IsQuotientMap.of_surjective_continuous (collapse_surjective F hne)
      (continuous_collapse F hF)
