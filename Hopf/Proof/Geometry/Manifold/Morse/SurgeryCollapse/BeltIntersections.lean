/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Algebra.BigOperators.SignedCancellation
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Whitney.CleanStrips
import Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization
import Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport

/-!
# Belt-sphere intersections of an index-two window in dimension six (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement carries `Module.finrank ℝ E = 6` and the index `2`:
circles in the lower level of an index-`2` window are null-homotopic when all earlier windows have
index `2` or `3` (`ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices`,
`MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices`); the Whitney trick
cancels pairs of opposite intersection points of a transverse `2`-sphere with the belt `3`-sphere
of an index-`2` window (`ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step`,
`exists_finite_belt_reduction`, `exists_minimal_signed_belt_sphere`,
`exists_single_belt_intersection_of_unit_count`); and a transverse loop through the belt sphere
of an index-`1` window is placed in a regular level (`AdaptedWindows.exists_transverse_middle_belt_loop`).

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val →
            Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
            ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : SublevelDisk 6 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 5) (by norm_num)
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow :
        ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel),
          ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
        FlowConstruction.circle_nullhomotopies_regular_level hf
          (S.ordered_windows _ _ hlt).le (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with htwo | hthree
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 1 + 1) :=
          ⟨htwo⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 1 (by norm_num) (by omega)
            hlow
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) :=
          ⟨hthree⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2 (by norm_num) (by omega)
            hlow
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact
    FlowConstruction.circle_nullhomotopies_regular_level hf
      (S.ordered_windows _ _ hprevj).le
      (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
      (hupper (j.val - 1) hprev hprevj)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (p : ManifoldMorse.criticalPoints E f)
    (hpindex : nativeMorseIndex E f p = 2) (hzero : nativeMorseCount E f 0 = 1)
    (hone : nativeMorseCount E f 1 = 0)
    (horder :
      ∀ r : ManifoldMorse.criticalPoints E f, f r < f p → nativeMorseIndex E f r ≤ 2) :
    ∀ γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨j, rfl⟩ := S.point.surjective p
  have hn : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  have hpnotfirst : S.point j ≠ S.first hn := by
    intro hpfirst
    have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
      (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
    rw [hpfirst] at hpindex
    omega
  have hj : 0 < j.val := by
    by_contra hj
    have hj0 : j.val = 0 := by omega
    have heq : S.point j = S.first hn := congrArg S.point (Fin.ext hj0)
    exact hpnotfirst heq
  have hmiddle (i : Fin S.count) (hi : 0 < i.val) (hij : i.val < j.val) :
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 := by
    have hvalues : f (S.point i) < f (S.point j) := S.point_strictMono (show i < j from hij)
    have hle := horder (S.point i) hvalues
    have hne0 : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hindex
      have heq : (S.point i).val = (S.first hn).val :=
        native_index_zero_point_unique S hf hn hzero _ (S.point i).property hindex
      have heq' : S.point i = S.point ⟨0, hn⟩ := Subtype.ext heq
      have hival := congrArg Fin.val (S.point.injective heq')
      change i.val = 0 at hival
      omega
    have hne1 := native_index_one_excluded S hone _ (S.point i).property
    have hindex : nativeMorseIndex E f (S.point i) = 2 := by omega
    exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point i)).chart).symm.trans hindex)
  exact S.lower_circle_nullhomotopies_of_middle_indices hf hdim j hj hmiddle

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) (x y : Hemisphere.Sphere 2)
    (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ z, g' z = e (g z)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              ((P \ { x, y } : Finset (Hemisphere.Sphere 2)) :
                    Set (Hemisphere.Sphere 2)) =
                  D.beltIntersectionPoints 2 g' ∧
                (∀ z ∈ P \ { x, y }, (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
                  (∑ z ∈ P \ { x, y }, (D.beltIntersectionSign 2 r g' z : ℤ)) =
                    ∑ z ∈ P, (D.beltIntersectionSign 2 r g z : ℤ) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hxB : x ∈ D.beltIntersectionPoints 2 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 2 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hg', hinj', hi', ht', hpoints, hgerm, hsign⟩ :=
    D.exists_signed_belt_cancellation_step hf hdim hindex hnull r g hg hinj hi ht x y hxB hyB hxy
  have hP' :
    ((P \ { x, y } : Finset (Hemisphere.Sphere 2)) : Set (Hemisphere.Sphere 2)) =
      D.beltIntersectionPoints 2 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Hemisphere.Sphere 2) (hz : z ∈ P \ { x, y }) :
    z ∈ D.beltIntersectionPoints 2 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, ⟨hg', hinj', hi', ht'⟩, hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact
      FiniteSignedCancellation.sum_sdiff_pair_of_eq P (D.beltIntersectionSign 2 r g)
        (D.beltIntersectionSign 2 r g') (x := x) (y := y) hx hy hxy
        (fun z hz => hsign z (hmem z hz))

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        ∃ P' : Finset (Hemisphere.Sphere 2),
          SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g' x = e (g x)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                (P' : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g' ∧
                  P' ⊆ P ∧
                    (∀ x ∈ P', (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                      (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)) =
                          ∑ x ∈ P, (D.beltIntersectionSign 2 r g x : ℤ) ∧
                        ∀ x ∈ P',
                          ∀ y ∈ P',
                            D.beltIntersectionSign 2 r g' x * D.beltIntersectionSign 2 r g' y ≠
                              -1 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  induction P using Finset.strongInductionOn generalizing g with
  | _ P
    ih =>
    by_cases hpair :
      ∃ x ∈ P, ∃ y ∈ P, D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨e₁, g₁, hiso₁, heq₁, hgood₁, hR, hgerm₁, hsum₁⟩ :=
        D.exists_finite_belt_cancellation_step hf hdim hindex hnull r P g hP hgood x y hx hy hxy
      let R : Finset (Hemisphere.Sphere 2) := P \ { x, y }
      have hsubpair : ({ x, y } : Finset (Hemisphere.Sphere 2)) ⊆ P := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hRlt : R ⊂ P := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨e₂, g₂, P₂, hiso₂, heq₂, hgood₂, hP₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih R hRlt g₁ hR hgood₁
      refine
        ⟨e₁.trans e₂, g₂, P₂, hiso₁.trans hiso₂, ?_, hgood₂, hP₂, hsub₂.trans Finset.sdiff_subset,
          ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change g₂ z = e₂ (e₁ (g z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hsub₂ hz))
    · refine
        ⟨Diffeomorph.refl _ _ _, g, P, SupportedDiffeomorph.isotopicToIdentity_refl,
          fun _ => rfl, hgood, hP, fun _ hx => hx, fun _ _ => Filter.EventuallyEq.refl _ _, rfl,
          ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ x, g' x = e (g x)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              D.beltIntersectionPoints 2 g' ⊆ D.beltIntersectionPoints 2 g ∧
                (∀ x ∈ D.beltIntersectionPoints 2 g',
                    (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                  (∀ hfin' : (D.beltIntersectionPoints 2 g').Finite,
                      D.beltIntersectionCount 2 r g' hfin' =
                        D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)) ∧
                    (D.beltIntersectionPoints 2 g').ncard =
                      (D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex
                            hgood)).natAbs := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let hfin := D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood
  obtain ⟨e, g', P', hiso, heq, hgood', hP', hsub, hgerm, hsum, hno⟩ :=
    D.exists_finite_belt_reduction hf hdim hindex hnull r hfin.toFinset g hfin.coe_toFinset hgood
  have hunit :
    ∀ x ∈ P', D.beltIntersectionSign 2 r g' x = 1 ∨ D.beltIntersectionSign 2 r g' x = -1 := by
    obtain ⟨hg', _, _, ht'⟩ := hgood'
    intro x hx
    exact D.beltIntersectionSign_unit hf 3 2 hindex r g' hg' ht' x (hP' ▸ hx)
  have hmem (x : Hemisphere.Sphere 2) (hx : x ∈ D.beltIntersectionPoints 2 g') : x ∈ P' := by
    change x ∈ (P' : Set (Hemisphere.Sphere 2))
    rw [hP']
    exact hx
  refine ⟨e, g', hiso, heq, hgood', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ P' := hmem x hx
    exact hfin.mem_toFinset.mp (hsub hxP)
  · intro x hx
    exact hgerm x (hmem x hx)
  · intro hfin'
    have hPfin : hfin'.toFinset = P' := by
      apply Finset.coe_injective
      exact hfin'.coe_toFinset.trans hP'.symm
    change (∑ x ∈ hfin'.toFinset, (D.beltIntersectionSign 2 r g' x : ℤ)) = _
    rw [hPfin]
    exact hsum
  · calc
      (D.beltIntersectionPoints 2 g').ncard = P'.card := by rw [← hP', Set.ncard_coe_finset]
      _ = (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)).natAbs :=
        (FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite P'
          (D.beltIntersectionSign 2 r g') hunit hno)
      _ = _ := congrArg Int.natAbs hsum

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount :
      (D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs =
        1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        ∃ x : Hemisphere.Sphere 2,
          SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ y, g' y = e (g y)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                D.beltIntersectionPoints 2 g' = { x } ∧
                  Set.range g' ∩ Set.range D.surgery.beltSphere = {g' x} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 2 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage :
    g' '' D.beltIntersectionPoints 2 g' = Set.range g' ∩ Set.range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' Set.range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [← himage, hx, Set.image_singleton]

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_transverse_middle_belt_loop {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hq : MorseCancellation.nativeMorseIndex E f q = 1)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ 2) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ δ : C(Hemisphere.Sphere 1, { y : M // f y = a }),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ ∧
        Function.Injective δ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) ∧
            ∃ (z₀ : Hemisphere.Sphere 1) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (β :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1 → { y : M // f y = a }),
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧
                β v = δ z₀ ∧
                  NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) δ β
                      z₀ v ∧
                    (∀ᶠ w in 𝓝 v,
                        Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val)) ∧
                      (∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) ↔
                            z = z₀) ∧
                        ∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) :=
  by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf ha
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, htrans, hendpoints⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq 4 u hbranches hqa
      ha hlow (by omega) (by omega) (by omega)
  obtain ⟨t₀, ht₀⟩ := hreach z₀
  let za : { y : M // f y = a } := ⟨S.flow t₀ (γ z₀).val, ht₀⟩
  obtain ⟨D, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data q).upper_regular ha (γ z₀) za
  have hγsource (z : Circle) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hΓsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
        hγ.contMDiffAt
  let Γ : C(Circle, { y : M // f y = a }) := ⟨D ∘ γ, hΓsmooth.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro z w hzw
    exact hγi (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hΓd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
        (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (S.data q).surgery.beltSphere v = γ z₀ := ((hsingle z₀ v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (S.data q).surgery.beltSphere v ∈ D.source := hcross.symm ▸ hγsource z₀
  let β := D ∘ (S.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp))
  have hβcross : β v = Γ z₀ := congrArg D hcross
  have hΓtrans :
    NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) Γ β z₀ v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff D
          (hγ.mdifferentiableAt (by simp))
          (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp)) hcross (hγsource z₀)).mp
      (fun _ => htrans)
  have hβbasin :
    ∀ᶠ w in 𝓝 v, Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val) := by
    have hnear :=
      (((S.data q).belt_smooth hf 4).continuous.tendsto v) (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((S.data q).surgery.beltSphere w) hw
    change S.flow t ((S.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr
        ((S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hforward (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    have hbasin :
      Filter.Tendsto (fun s => S.flow s (Γ z).val) Filter.atTop (𝓝 q.val) ↔
        γ z ∈ Set.range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact
        (MorseCancellation.flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
          (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  have hΓends (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    rw [← ht]
    exact
      (hendpoints z).imp ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ p.val).mpr)
        ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr)
  let δ : C(Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨Γ ∘ MorseCancellation.standardCircleParametrization,
      Γ.continuous.comp MorseCancellation.standardCircleParametrization.continuous⟩
  let z := MorseCancellation.standardCircleParametrization.symm z₀
  have hz : MorseCancellation.standardCircleParametrization z = z₀ :=
    MorseCancellation.standardCircleParametrization.apply_symm_apply z₀
  have hδcross : β v = δ z := by
    change β v = Γ (MorseCancellation.standardCircleParametrization z)
    rw [hz]
    exact hβcross
  have hδtrans :
    NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) δ β z v := by
    intro _
    let B : EuclideanSpace ℝ (Fin 4) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v
    apply MorseCancellation.transverse_comp_standardCircle hΓsmooth B z
    rw [hz]
    exact hΓtrans hβcross
  refine
    ⟨δ, MorseCancellation.contMDiff_comp_standardCircle hΓsmooth,
      MorseCancellation.injective_comp_standardCircle hΓi,
      MorseCancellation.injective_derivative_comp_standardCircle hΓsmooth hΓd, z, v, β, hβ, hδcross,
      hδtrans, hβbasin, ?_, fun w => hΓends (MorseCancellation.standardCircleParametrization w)⟩
  intro w
  change
    Filter.Tendsto (fun t => S.flow t (Γ (MorseCancellation.standardCircleParametrization w)).val)
        Filter.atTop (𝓝 q.val) ↔
      _
  rw [hforward]
  exact
    ⟨fun hw => MorseCancellation.standardCircleParametrization.injective (hw.trans hz.symm), fun hw =>
      hw ▸ hz⟩

end
