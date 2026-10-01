/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib

/-!
# Removing intersections by a map supported in a set

Set-theoretic lemmas about a bijection `d : X ≃ X` that is the identity off a set `U`: if it carries
`S ∩ U` off `T ∩ U`, then `d '' S ∩ T = (S ∩ T) \ U` (`SupportedDiffeomorph.image_inter_eq_diff`);
the corresponding statement for preimages along a parametrisation
(`SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal`); and a map that is the identity
off a closed set does not change the germ of a continuous parametrisation at a point mapped outside
it (`SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed`).

They express that the Whitney isotopy removes exactly the intersection points inside its support;
cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

support, intersection, germ
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- If a bijection is the identity off `U` and carries `S ∩ U` off `T ∩ U`, then the image of `S`
meets `T` exactly in `(S ∩ T) \ U`: the intersections inside `U` have been removed and no
others. -/
theorem SupportedDiffeomorph.image_inter_eq_diff {X : Type*} (d : X ≃ X) {S T U : Set X}
    (hfix : ∀ x ∉ U, d x = x) (hdisjoint : Disjoint (d '' (S ∩ U)) (T ∩ U)) :
    (d '' S) ∩ T = (S ∩ T) \ U := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyT⟩
    have hyU : y ∉ U := by
      intro hy
      have hxU : x ∈ U := by
        by_contra hnot
        have he : x = y := (hfix x hnot).symm.trans hxy
        exact hnot (he.symm ▸ hy)
      exact Set.disjoint_left.mp hdisjoint ⟨x, ⟨hx, hxU⟩, hxy⟩ ⟨hyT, hy⟩
    have he : x = y := d.injective (hxy.trans (hfix y hyU).symm)
    exact ⟨⟨he ▸ hx, hyT⟩, hyU⟩
  · rintro ⟨⟨hyS, hyT⟩, hyU⟩
    exact ⟨⟨y, hyS, hfix y hyU⟩, hyT⟩

/-- Under the same removal, the preimage of the second sheet along a composed parametrisation loses
exactly the preimage of the removed set. -/
theorem SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal {X Y : Type*}
    (d : X ≃ X) (F : Y → X) {T R : Set X} (hfix : ∀ y ∈ (Set.range F ∩ T) \ R, d y = y)
    (himage : (d '' Set.range F) ∩ T = (Set.range F ∩ T) \ R) :
    (d ∘ F) ⁻¹' T = (F ⁻¹' T) \ (F ⁻¹' R) := by
  ext x
  constructor
  · intro hx
    have hy : d (F x) ∈ (d '' Set.range F) ∩ T := ⟨⟨F x, ⟨x, rfl⟩, rfl⟩, hx⟩
    rw [himage] at hy
    have heq : F x = d (F x) := d.injective (hfix _ hy).symm
    change F x ∈ T ∧ F x ∉ R
    rw [heq]
    exact ⟨hy.1.2, hy.2⟩
  · intro hx
    have hy : F x ∈ (Set.range F ∩ T) \ R := ⟨⟨⟨x, rfl⟩, hx.1⟩, hx.2⟩
    change d (F x) ∈ T
    rw [hfix _ hy]
    exact hx.1

/-- A map that is the identity off a closed set does not change the germ of a parametrisation at a
point mapped outside that set. -/
theorem SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {d : X → X} {F : Y → X} {K : Set X}
    (hK : IsClosed K) (hfix : ∀ y ∉ K, d y = y) (hF : Continuous F) {x : Y} (hx : F x ∉ K) :
    (d ∘ F) =ᶠ[𝓝 x] F := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hx)] with y hy
  exact hfix _ hy


end
