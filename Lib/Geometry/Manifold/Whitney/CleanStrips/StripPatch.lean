/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.BigonModel

/-!
# Clean strip patches

`CleanStripPatch S T a k₀ k₁` is an immersed injective map of a neighbourhood of a strip
`[0, 1] × [-w, w]` into `M`, a closed embedding on the strip, which meets the sheet `S` exactly in
the centre line and the sheet `T` exactly in the two ends `t = 0` and `t = 1`, restricts to the arc
`a` on the centre line, and agrees near `(0, 0)` with the corner patch `k₀` and near `(1, 0)` with
`k₁ ∘ StripCoordinates.reverse`.

The file proves that the centre arc is injective, that the patch avoids both sheets off the
centre line and the ends, that two patches with corner-compatible overlaps have centre arcs meeting
only at the shared endpoints, and that a map given by a patch composed with an immersion is an
immersion. These are the strips along the edges of the Whitney disk (Milnor, *Lectures on the
h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- A clean strip patch along an arc `a` joining two corners: an immersed injective map of a
neighbourhood of the strip `[0, 1] × [-w, w]` into `M` which is a closed embedding on that
strip, meets the sheet `S` exactly in the centre line `s = 0` and the sheet `T` exactly in the two
vertical lines `t = 0` and `t = 1`, restricts to `a` on the centre line, agrees near `(0, 0)` with
the corner patch `k₀`, and agrees near `(1, 0)` with `k₁ ∘ StripCoordinates.reverse`.
-/
structure CleanStripPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a : ℝ → M) (k₀ k₁ : (ℝ × ℝ) → M) where
  /-- The half-width `w` of the strip `[0, 1] × [-w, w]`. -/
  width : ℝ
  /-- The half-width is positive. -/
  width_pos : 0 < width
  /-- The domain of the patch in the plane. -/
  domain : Set (ℝ × ℝ)
  /-- The domain is open. -/
  open_domain : IsOpen domain
  /-- The domain contains the strip `[0, 1] × [-w, w]`. -/
  contains_strip : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width ⊆ domain
  /-- The patch map. -/
  map : (ℝ × ℝ) → M
  /-- The patch map is smooth on its domain. -/
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  /-- The patch map is injective on its domain. -/
  injective : Set.InjOn map domain
  /-- The patch map restricted to the strip is a closed embedding. -/
  closed_embedding :
    Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width => map p)
  /-- The patch map is an immersion on its domain. -/
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  /-- A point of the domain is sent into `S` exactly when its second coordinate vanishes. -/
  first_sheet : ∀ p ∈ domain, map p ∈ S ↔ p.2 = 0
  /-- A point of the domain is sent into `T` exactly when its first coordinate is `0` or `1`. -/
  second_sheet : ∀ p ∈ domain, map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1
  /-- On the centre line over `[0, 1]` the patch map is the arc `a`. -/
  center : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (t, 0) = a t
  /-- Near `(0, 0)` the patch map agrees with the corner patch `k₀`. -/
  left_germ : map =ᶠ[𝓝 (0, 0)] k₀
  /-- Near `(1, 0)` the patch map agrees with `k₁ ∘ StripCoordinates.reverse`. -/
  right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse

/-- The centre arc of a clean strip patch is injective on `[0, 1]`. -/
theorem CleanStripPatch.center_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  have h0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have htK : (t, 0) ∈ k.domain := k.contains_strip ⟨ht, h0⟩
  have hsK : (s, 0) ∈ k.domain := k.contains_strip ⟨hs, h0⟩
  have hmaps : k.map (t, 0) = k.map (s, 0) := by
    rw [k.center t ht, k.center s hs]
    exact heq
  exact congrArg Prod.fst (k.injective htK hsK hmaps)

/-- If two clean strip patches can only agree over swapped corner parameters, then their centre arcs
meet only at the two shared endpoints.
-/
theorem strip_center_coincidences_of_corner_overlap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  intro t ht s hs heq
  have hk0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hl0 : (0 : ℝ) ∈ Set.Icc (-l.width) l.width :=
    ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hmaps : k.map (t, 0) = l.map (s, 0) := by rw [k.center t ht, l.center s hs]; exact heq
  rcases hover (t, 0) (k.contains_strip ⟨ht, hk0⟩) (s, 0) (l.contains_strip ⟨hs, hl0⟩) hmaps with
    hleft | hright
  · exact Or.inl ⟨congrArg Prod.fst hleft, (congrArg Prod.snd hleft).symm⟩
  · right
    have ht' : 1 - t = 0 := congrArg Prod.fst hright
    have hs' : 0 = 1 - s := congrArg Prod.snd hright
    constructor <;> linarith

/-- A map given on an open set by a clean strip patch composed with an immersion `r` is itself an
immersion there.
-/
theorem injective_mfderiv_of_eqOn_cleanStripPatch_comp {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {r : (ℝ × ℝ) → ℝ × ℝ}
    (hr : ContDiff ℝ ∞ r) {f : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (heq : Set.EqOn f (k.map ∘ r) U) (hmap : Set.MapsTo r U k.domain) {p : ℝ × ℝ} (hp : p ∈ U)
    (hi : Function.Injective (fderiv ℝ r p)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hgerm : f =ᶠ[𝓝 p] k.map ∘ r := Filter.mem_of_superset (hU.mem_nhds hp) (fun _ hx => heq hx)
  rw [hgerm.mfderiv_eq]
  have hk := k.smooth.contMDiffAt (k.open_domain.mem_nhds (hmap hp))
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp)) (hr.contMDiff.mdifferentiableAt (by simp))]
  have hri : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r p) := by
    rw [mfderiv_eq_fderiv]
    exact hi
  exact (k.derivative_injective (r p) (hmap hp)).comp hri

/-- A clean strip patch avoids both sheets at parameters with time strictly between `0` and `1` and
nonzero height.
-/
theorem CleanStripPatch.avoids_sheets {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) {p : ℝ × ℝ} (hp : p ∈ k.domain)
    (ht : p.1 ∈ Set.Ioo (0 : ℝ) 1) (hn : p.2 ≠ 0) : k.map p ∉ S ∪ T := by
  rintro (hS | hT)
  · exact hn ((k.first_sheet p hp).mp hS)
  · rcases (k.second_sheet p hp).mp hT with h0 | h1
    · exact ht.1.ne' h0
    · exact ht.2.ne h1

end
