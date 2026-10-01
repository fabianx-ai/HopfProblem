/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.PointMoving
import Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.ImmersionRepair

/-!
# Embedded arcs avoiding a finite set

In a manifold of dimension at least two:

* every point of an open set starts a nonconstant embedded arc inside it
  (`exists_short_embedded_arc`);
* two distinct points joined by a path are joined by an embedded smooth arc whose interior avoids a
  prescribed finite set (`exists_embedded_connecting_arc_avoiding_finite_of_two_le_finrank`);
* such an arc carries a tubular neighbourhood of prescribed codimension whose image meets the
  finite set only at the two endpoints
  (`exists_tubular_connecting_arc_avoiding_finite_with_global_zero`).

This is general position for arcs (the arcs joining two intersection points in the Whitney trick),
cf. Milnor, *Lectures on the h-cobordism theorem*, §6, and Hirsch, *Differential Topology*, Ch. 2.

## Tags

embedded arc, general position, tubular neighbourhood
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- In a manifold of dimension at least two, every point of an open set is the starting point of a
nonconstant embedded arc contained in that open set. -/
theorem exists_short_embedded_arc {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {U : Set N}
    (hU : IsOpen U) {x : N} (hx : x ∈ U) (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 ≠ x ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ U := by
  let c : C(ℝ, N) := ContinuousMap.const ℝ x
  obtain ⟨g, hg, hrel, hi⟩ :=
    ManifoldImmersion.exists_curve_endpoint_derivative_repair (J := J) c contMDiff_const hdim
  have hg0 : g 0 = x := (hrel.fst_eq_snd (by simp)).symm
  have hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := hi 0 (by simp)
  obtain ⟨V, hV, h0V, hinj⟩ :=
    ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative hg hi0
  let W := V ∩ ({t : ℝ | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)} ∩ g ⁻¹' U)
  have hW : IsOpen W :=
    hV.inter ((ManifoldImmersion.isOpen_injective_derivative hg).inter (hU.preimage g.continuous))
  have h0W : (0 : ℝ) ∈ W := ⟨h0V, hi0, (show g 0 ∈ U from hg0.symm ▸ hx)⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let L : ℝ →L[ℝ] ℝ := (r / 2) • ContinuousLinearMap.id ℝ ℝ
  have hLs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ L := L.contDiff.contMDiff
  have hL (t : ℝ) : L t = (r / 2) * t := rfl
  have hscale : 0 < r / 2 := by positivity
  have hLinj : Function.Injective L := by
    intro s t hst
    exact mul_left_cancel₀ hscale.ne' hst
  have hLW : ∀ t ∈ Set.Icc (0 : ℝ) 1, L t ∈ W := by
    intro t ht
    apply hball
    change Dist.dist (L t) 0 < r
    rw [dist_zero_right, Real.norm_eq_abs, hL, abs_of_nonneg (mul_nonneg hscale.le ht.1)]
    have hbound := mul_le_mul_of_nonneg_left ht.2 hscale.le
    linarith
  let f : C(ℝ, N) := ⟨g ∘ L, g.continuous.comp L.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := hg.comp hLs
  have hfinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hLinj (hinj (hLW s hs).1 (hLW t ht).1 hst)
  have hf0 : f 0 = x := by
    change g (L 0) = x
    rw [map_zero, hg0]
  have hemb : Topology.IsClosedEmbedding (fun t : unitInterval => f t) := by
    apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact Subtype.ext (hfinj s.property t.property hst)
  refine ⟨f, hf, hf0, ?_, hemb, ?_, ?_⟩
  · intro hfx
    have h10 : (1 : ℝ) = 0 := hfinj (by simp) (by simp) (hfx.trans hf0.symm)
    exact one_ne_zero h10
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (g ∘ L) t)
    rw [mfderiv_comp t (hg.mdifferentiableAt (by simp)) (hLs.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, L.fderiv]
    exact (hLW t ht).2.1.comp hLinj
  · intro t ht
    exact (hLW t ht).2.2

/-- Two distinct points joined by a path in a manifold of dimension at least two are joined by an
embedded smooth arc whose interior avoids a prescribed finite set (general position for arcs). -/
theorem exists_embedded_connecting_arc_avoiding_finite_of_two_le_finrank {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S := by
  have hSx : (S \ { x }).Finite := hS.subset Set.sdiff_subset
  obtain ⟨g, hg, hg0, hg1, hemb, hi, havoid⟩ :=
    exists_short_embedded_arc (J := J) hSx.isClosed.isOpen_compl
      (show x ∈ (S \ { x })ᶜ from by simp) hdim
  have hginj : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  have hg1S : g 1 ∉ S := by
    intro hs
    exact havoid 1 (by simp) ⟨hs, hg1⟩
  let C : Set N := (Insert.insert x S) \ { y }
  have hC : C.Finite := (hS.insert x).subset Set.sdiff_subset
  have hxC : x ∈ C := ⟨Set.mem_insert x S, hxy⟩
  have hg1C : g 1 ∉ C := by
    rintro ⟨hr, _⟩
    rcases hr with hr | hr
    · exact hg1 hr
    · exact hg1S hr
  have hyC : y ∉ C := fun hy => hy.2 rfl
  let α : Path x (g 1) :=
    { toFun := fun t => g t
      continuous_toFun := g.continuous.comp continuous_subtype_val
      source' := hg0
      target' := rfl }
  obtain ⟨d, hd, hfix⟩ :=
    exists_pointMoving_fixing_finite (J := J) (α.symm.trans γ) hdim hC hg1C hyC
  let f : C(ℝ, N) := ⟨d ∘ g, d.continuous.comp g.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := d.contMDiff.comp hg
  refine ⟨f, hf, ?_, hd, ?_, ?_, ?_⟩
  · change d (g 0) = x
    rw [hg0]
    exact hfix x hxC
  · apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact hemb.injective (d.injective hst)
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (d ∘ g) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    exact
      (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (Set.mem_univ (g t))).1.comp
        (hi t ht)
  · intro t ht hftS
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    by_cases hfty : f t = y
    · have hgt : g t = g 1 := d.injective (hfty.trans hd.symm)
      exact ht.2.ne (hginj htI (by simp) hgt)
    · have hftC : f t ∈ C := ⟨Or.inr hftS, hfty⟩
      have hgt : g t = f t := d.injective (hfix (f t) hftC).symm
      have hgtS : g t ∈ S := hgt.symm ▸ hftS
      have hgtx : g t ≠ x := by
        intro he
        exact ht.1.ne' (hginj htI (by simp) (he.trans hg0.symm))
      exact havoid t htI ⟨hgtS, hgtx⟩

/-- The connecting arc of the previous statement can be taken with a tubular neighbourhood of the
prescribed codimension whose image avoids the finite set except at the two endpoints. -/
theorem exists_tubular_connecting_arc_avoiding_finite_with_global_zero {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {x y : N}
    (γ : Path x y) (hxy : x ≠ y) (hdim : 2 ≤ Module.finrank ℝ G) (n : ℕ)
    (hcodim : 1 + n = Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) ∧
                  ∃ ε : ℝ,
                    0 < ε ∧
                      ∃ Φ :
                        PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
                          (ℝ × EuclideanSpace ℝ (Fin n)) N ∞,
                        Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
                          (∀ t, Φ (t, 0) = f t) ∧ Φ.target ⊆ (S \ { x, y })ᶜ := by
  obtain ⟨f, hf, hf0, hf1, hemb, hi, havoid⟩ :=
    exists_embedded_connecting_arc_avoiding_finite_of_two_le_finrank (J := 𝓘(ℝ, G)) γ hxy hdim hS
  have hinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hO : IsOpen (S \ { x, y })ᶜ := (hS.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hfO : Set.MapsTo f (Set.Icc (0 : ℝ) 1) (S \ { x, y })ᶜ := by
    intro t ht
    change f t ∉ S \ { x, y }
    by_cases ht0 : t = 0
    · rw [ht0, hf0]
      exact fun hx => hx.2 (by simp)
    by_cases ht1 : t = 1
    · rw [ht1, hf1]
      exact fun hy => hy.2 (by simp)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact fun hs => havoid t hti hs.1
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinj hi n
      (by simpa only [Module.finrank_self] using hcodim) hO hfO
  exact ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, htarget⟩

end
