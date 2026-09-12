/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

def HigherHurewicz.SimplexGeometry.prefixMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).inf u

@[simp]
theorem HigherHurewicz.SimplexGeometry.prefixMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    prefixMinimum u 0 = 1 := by
  simp [prefixMinimum]
  rfl

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (prefixMinimum u) := by
  intro k l hkl
  apply Finset.inf_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hkl

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) (i : Fin n) (hi : i.val < k) : prefixMinimum u k ≤ u i :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_succ {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k < n) : prefixMinimum u (k + 1) = Min.min (prefixMinimum u k) (u ⟨k, hk⟩) := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixMinimum
  rw [hs, Finset.inf_insert]
  exact min_comm _ _

theorem HigherHurewicz.SimplexGeometry.continuous_prefixMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => prefixMinimum u k) :=
  Continuous.finset_inf_apply (fun i _ => continuous_apply i)

def HigherHurewicz.SimplexGeometry.extendedMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  if k ≤ n then prefixMinimum u k else 0

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_of_le {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k ≤ n) : extendedMinimum u k = prefixMinimum u k :=
  if_pos hk

@[simp]
theorem HigherHurewicz.SimplexGeometry.extendedMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    extendedMinimum u 0 = 1 := by simp [extendedMinimum]

@[simp]
theorem HigherHurewicz.SimplexGeometry.extendedMinimum_last_succ {n : ℕ}
    (u : Fin n → (unitInterval)) : extendedMinimum u (n + 1) = 0 := by simp [extendedMinimum]

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (extendedMinimum u) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · have hk := hkl.trans hl
    simpa only [extendedMinimum, if_pos hk, if_pos hl] using prefixMinimum_antitone u hkl
  · rw [show extendedMinimum u l = 0 from if_neg hl]
    exact bot_le

theorem HigherHurewicz.SimplexGeometry.continuous_extendedMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => extendedMinimum u k) := by
  by_cases hk : k ≤ n
  · simpa only [extendedMinimum, if_pos hk] using continuous_prefixMinimum n k
  · simpa only [extendedMinimum, if_neg hk] using
      (continuous_const : Continuous (fun _ : Fin n → (unitInterval) => (0 : (unitInterval))))

def HigherHurewicz.SimplexGeometry.simplexQuotient (n : ℕ) :
    C(Fin n → (unitInterval), SingularChains.Simplex n)
    where
  toFun
    u :=
    ⟨fun i => (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ),
      by
      constructor
      · intro i
        exact sub_nonneg.mpr (extendedMinimum_antitone u (Nat.le_succ i.val))
      · calc
          (∑ i : Fin (n + 1),
                ((extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ))) =
              ∑ i ∈ Finset.range (n + 1),
                ((extendedMinimum u i : ℝ) - (extendedMinimum u (i + 1) : ℝ)) :=
            Fin.sum_univ_eq_sum_range
              (fun k : ℕ => (extendedMinimum u k : ℝ) - (extendedMinimum u (k + 1) : ℝ)) (n + 1)
          _ = (extendedMinimum u 0 : ℝ) - (extendedMinimum u (n + 1) : ℝ) :=
            (Finset.sum_range_sub' _ _)
          _ = 1 := by simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact
      (continuous_subtype_val.comp (continuous_extendedMinimum n i.val)).sub
        (continuous_subtype_val.comp (continuous_extendedMinimum n (i.val + 1)))

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_apply {n : ℕ} (u : Fin n → (unitInterval))
    (i : Fin (n + 1)) :
    simplexQuotient n u i = (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ) :=
  rfl

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) :
    simplexQuotient n u i.castSucc =
      (prefixMinimum u i.val : ℝ) - (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [simplexQuotient_apply]
  exact
    congrArg₂ (fun a b : (unitInterval) => (a : ℝ) - (b : ℝ))
      (extendedMinimum_of_le u i.val i.isLt.le) (extendedMinimum_of_le u (i.val + 1) i.isLt)

@[simp]
theorem HigherHurewicz.SimplexGeometry.simplexQuotient_last {n : ℕ} (u : Fin n → (unitInterval)) :
    simplexQuotient n u (Fin.last n) = (prefixMinimum u n : ℝ) := by
  rw [simplexQuotient_apply]
  simp only [Fin.val_last, extendedMinimum_last_succ, extendedMinimum_of_le u n le_rfl]
  exact sub_zero _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hp : prefixMinimum u n = 0 :=
    le_antisymm (hi ▸ prefixMinimum_le_coordinate u n i i.isLt) bot_le
  exact ⟨Fin.last n, by rw [simplexQuotient_last, hp]; rfl⟩

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨i.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact simplexQuotient_boundary_of_zero u i hi
  · exact simplexQuotient_boundary_of_one u i hi

def HigherHurewicz.SimplexGeometry.BasedSimplex (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(SingularChains.Simplex n, X) //
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, τ s = x }

def HigherHurewicz.SimplexGeometry.basedSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp (simplexQuotient n), fun u hu => τ.property _ (simplexQuotient_boundary u hu)⟩

def HigherHurewicz.SimplexGeometry.basedSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : Additive (π_ n X x) :=
  Additive.ofMul (⟦basedSimplexLoop τ⟧ : π_ n X x)

theorem HigherHurewicz.SimplexGeometry.basedSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex (n + 1) x) (i : Fin (n + 2)) :
    τ.val.comp (SingularChains.simplexFace n i) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, SingularChains.simplexFace_apply_self n i s⟩

def HigherHurewicz.constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X) :
    SingularChains.Chains X n :=
  SingularChains.simplexChain X n (ContinuousMap.const (SingularChains.Simplex n) x)

def HigherHurewicz.correctedSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : SingularChains.SingularSimplex X n) : SingularChains.Chains X n :=
  SingularChains.simplexChain X n smp - constantSimplexChain n x

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : Fin n → (unitInterval)) (i : Fin n) :
    (HigherHurewicz.CubeTriangulation.cubeSimplex e (simplexQuotient n u) (e i) : ℝ) =
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
  have h :=
    HigherHurewicz.CubeTriangulation.sum_fin_differences_tail (n + 1)
      (fun k : Fin (n + 2) => (extendedMinimum u k.val : ℝ)) i.succ
  simpa only [simplexQuotient_apply, Fin.val_castSucc, Fin.val_succ, Nat.succ_le_iff,
    Fin.val_last, extendedMinimum_last_succ, show ((0 : (unitInterval)) : ℝ) = 0 from rfl,
    sub_zero, extendedMinimum_of_le u (i.val + 1) i.isLt] using h

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) (i : Fin n) :
    prefixMinimum u (i.val + 1) = u i := by
  apply le_antisymm (prefixMinimum_le_coordinate u (i.val + 1) i (Nat.lt_succ_self _))
  unfold prefixMinimum
  apply Finset.le_inf
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hu (Nat.le_of_lt_succ hj)

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) :
    HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n)) (simplexQuotient n u) = u :=
  by
  funext i
  apply Subtype.ext
  simpa only [Equiv.refl_apply, prefixMinimum_of_antitone u hu i] using
    cubeSimplex_quotient_coordinate (Equiv.refl (Fin n)) u i

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_refl (n : ℕ) :
    (simplexQuotient n).comp (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      ContinuousMap.id (SingularChains.Simplex n) := by
  apply ContinuousMap.ext
  intro s
  apply HigherHurewicz.CubeTriangulation.cubeSimplex_injective (Equiv.refl (Fin n))
  exact
    cubeSimplex_quotient_of_antitone _
      (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone (Equiv.refl (Fin n)) s)

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_coordinate_le {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hu : u i ≤ u j) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨j.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u j.val j.isLt]
  have hp : prefixMinimum u j.val ≤ u j := (prefixMinimum_le_coordinate u j.val i hij).trans hu
  rw [min_eq_left hp]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_coordinate_inversion {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : SingularChains.Simplex n) :
    ∃ i j : Fin n,
      i < j ∧
        HigherHurewicz.CubeTriangulation.cubeSimplex e s i ≤
          HigherHurewicz.CubeTriangulation.cubeSimplex e s j := by
  by_contra h
  have hu : StrictAnti (HigherHurewicz.CubeTriangulation.cubeSimplex e s) := by
    intro i j hij
    exact lt_of_not_ge (fun hle => h ⟨i, j, hij, hle⟩)
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : SingularChains.Simplex n) :
    simplexQuotient n (HigherHurewicz.CubeTriangulation.cubeSimplex e s) ∈
      SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, j, hij, hu⟩ := cubeSimplex_coordinate_inversion e he s
  exact simplexQuotient_boundary_of_coordinate_le _ i j hij hu

theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_refl {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) :
    (basedSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      τ.val := by
  change (τ.val.comp (simplexQuotient n)).comp _ = _
  rw [ContinuousMap.comp_assoc, simplexQuotient_cubeSimplex_refl, ContinuousMap.comp_id]

theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_other {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) :
    (basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (simplexQuotient_cubeSimplex_boundary e he s)

theorem HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex (n + 2) x) :
    (∑ e : Equiv.Perm (Fin (n + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain X (n + 2)
            ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
  classical
  let c := HigherHurewicz.constantSimplexChain (n + 2) x
  have heq (e : Equiv.Perm (Fin (n + 2))) :
    HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X (n + 2)
          ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      (if e = Equiv.refl (Fin (n + 2)) then HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
        else 0) +
        HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin (n + 2))
    · subst e
      rw [basedSimplexLoop_cubeSimplex_refl,
        HigherHurewicz.CubeTriangulation.cubeOrientation_refl, one_smul, if_pos rfl, one_smul]
      change
        SingularChains.simplexChain X (n + 2) τ.val =
          (SingularChains.simplexChain X (n + 2) τ.val - c) + c
      exact (sub_add_cancel _ _).symm
    · rw [basedSimplexLoop_cubeSimplex_other τ e he, if_neg he, zero_add]
      rfl
  calc
    _ =
        ∑ e : Equiv.Perm (Fin (n + 2)),
          ((if e = Equiv.refl (Fin (n + 2)) then
              HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
            else 0) +
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ =
        HigherHurewicz.correctedSimplexChain (n + 2) x τ.val +
          (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) •
            c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin (n + 2)),
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
        let f : ℤ →+ SingularChains.Chains X (n + 2) :=
          { toFun := fun k => k • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f HigherHurewicz.CubeTriangulation.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
      rw [HigherHurewicz.CubeTriangulation.cubeOrientation_sum n, zero_smul, add_zero]

def HigherHurewicz.SimplexGeometry.simplexTwoBoundary (n : ℕ) : Set (SingularChains.Simplex n) :=
  {s | ∃ i j : Fin (n + 1), i ≠ j ∧ s i = 0 ∧ s j = 0}

theorem HigherHurewicz.SimplexGeometry.simplexFace_simplexBoundary (n : ℕ) (i : Fin (n + 2))
    (s : SingularChains.Simplex n) (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    SingularChains.simplexFace n i s ∈ simplexTwoBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, SingularChains.simplexFace_apply_self n i s,
      (SingularChains.simplexFace_apply_succAbove n i s j).trans hj⟩

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_eq_zero_of_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) (k : ℕ) (hik : i.val < k) :
    prefixMinimum u k = 0 :=
  le_antisymm (hi ▸ prefixMinimum_le_coordinate u k i hik) bot_le

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_last_eq_zero_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u (Fin.last n) = 0 := by
  rw [simplexQuotient_last, prefixMinimum_eq_zero_of_coordinate u i hi n i.isLt]
  rfl

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u i.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_earlier_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hi : u i = 0) :
    simplexQuotient n u j.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_eq_zero_of_coordinate u i hi j.val hij,
    prefixMinimum_eq_zero_of_coordinate u i hi (j.val + 1)
      ((show i.val < j.val from hij).trans_le (Nat.le_succ j.val))]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_codimTwo {n : ℕ}
    (u : Fin n → (unitInterval))
    (hu : ∃ i j : Fin n, i ≠ j ∧ (u i = 0 ∨ u i = 1) ∧ (u j = 0 ∨ u j = 1)) :
    simplexQuotient n u ∈ simplexTwoBoundary n := by
  obtain ⟨i, j, hij, hi | hi, hj | hj⟩ := hu
  · rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact
        ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u i j hij' hi,
          simplexQuotient_last_eq_zero_of_zero u i hi⟩
    · exact
        ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u j i hji' hj,
          simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
        simplexQuotient_castSucc_eq_zero_of_one u j hj,
        simplexQuotient_last_eq_zero_of_zero u i hi⟩
  · exact
      ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective n h),
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_castSucc_eq_zero_of_one u j hj⟩

def HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(SingularChains.Simplex n, X) // ∀ s ∈ simplexTwoBoundary n, τ s = x }

def HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 2)) : BasedSimplex n x :=
  ⟨τ.val.comp (SingularChains.simplexFace n i), fun s hs =>
    τ.property _ (simplexFace_simplexBoundary n i s hs)⟩

def HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : C(SingularChains.Simplex (n + 1), X))
    (h :
      ∀ i : Fin (n + 2),
        ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
          (τ.comp (SingularChains.simplexFace n i)) s = x) :
    HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n + 1) x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (SingularChains.simplexFace n i t) = x at he
    rw [show SingularChains.simplexFace n i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse n i ⟨s, hi⟩] at he
    exact he⟩

def HigherHurewicz.NativeSubdivision.nativeCubePair {N : Type*} (i j : N) :
    C(N → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap {N : Type*} [DecidableEq N]
    (i j : N) : C((unitInterval) × (N → (unitInterval)), N → (unitInterval))
    where
  toFun z
    k :=
    if k = i then
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else
      if k = j then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
      else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [if_pos hi]
      exact
        (continuous_apply (0 : Fin 2)).comp
          (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
            (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [if_neg hi, if_pos hj]
        exact
          (continuous_apply (1 : Fin 2)).comp
            (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
              (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [if_neg hi, if_neg hj]
        exact (continuous_apply k).comp continuous_snd

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_zero {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change
    (if k = i then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
      else
        if k = j then
          SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 1
        else u k) =
      u k
  simp only [SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_one {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_boundary {N : Type*}
    [DecidableEq N] (i j : N) (hij : i ≠ j) (t : (unitInterval)) (u : N → (unitInterval))
    (hu : u ∈ Cube.boundary N) : nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ :=
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    GenLoop N X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_apply {N : Type*}
    [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopy {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary N)
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

abbrev HigherHurewicz.NativeSubdivision.NativeCube (N : Type*) :=
  N → (unitInterval)

def HigherHurewicz.NativeSubdivision.nativeClass {N X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop N X x) : Additive (HomotopyGroup N X x) :=
  Additive.ofMul (⟦p⟧ : HomotopyGroup N X x)

theorem HigherHurewicz.NativeSubdivision.nativeClass_homotopic {N X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) : nativeClass p = nativeClass q :=
  congrArg (fun a : HomotopyGroup N X x => Additive.ofMul a) (Quotient.sound h)

theorem HigherHurewicz.NativeSubdivision.nativeClass_transAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nontrivial N] (i : N) (p q : GenLoop N X x) :
    nativeClass (GenLoop.transAt i p q) = nativeClass p + nativeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

theorem HigherHurewicz.NativeSubdivision.nativeClass_symmAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] (i : N) (p : GenLoop N X x) :
    nativeClass (GenLoop.symmAt i p) = -nativeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeClass_const {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] : nativeClass (GenLoop.const : GenLoop N X x) = 0 :=
  rfl

def HigherHurewicz.NativeSubdivision.NativeCubeInternalBased {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) : Prop :=
  ∀ u : NativeCube N, ∀ i j : N, i ≠ j → u i = u j → p u = x

inductive HigherHurewicz.NativeSubdivision.NativeCubeSameFlat {N : Type*} (a b : NativeCube N) :
    Prop
  | zero (i : N) (ha : a i = 0) (hb : b i = 0)
  | one (i : N) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : N) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

def HigherHurewicz.NativeSubdivision.nativeCubeBlend {N : Type*} (t : (unitInterval))
    (a b : NativeCube N) : NativeCube N := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_zero {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_one {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def HigherHurewicz.NativeSubdivision.nativeCubeBlendMap {N : Type*}
    (f g : C(NativeCube N, NativeCube N)) : C((unitInterval) × NativeCube N, NativeCube N)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_based {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p) {a b : NativeCube N}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

def HigherHurewicz.NativeSubdivision.nativeCubePullbackLoop {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) : GenLoop N X x :=
  ⟨p.val.comp f, hf⟩

def HigherHurewicz.NativeSubdivision.nativeCubeLinearHomotopy {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N)) (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary N)
    where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left
    u := by
    change p (nativeCubeBlend 0 (f u) (g u)) = p (f u)
    rw [nativeCubeBlend_zero]
  map_one_left
    u := by
    change p (nativeCubeBlend 1 (f u) (g u)) = p (g u)
    rw [nativeCubeBlend_one]
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

def HigherHurewicz.NativeSubdivision.permuteCubeCoordinates {N : Type*} (e : Equiv.Perm N) :
    C(N → (unitInterval), N → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

theorem HigherHurewicz.NativeSubdivision.permuteCubeCoordinates_boundary {N : Type*}
    (e : Equiv.Perm N) (u : N → (unitInterval)) (hu : u ∈ Cube.boundary N) :
    permuteCubeCoordinates e u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

def HigherHurewicz.NativeSubdivision.permuteCubeLoop {N : Type*} {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) : GenLoop N X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) (u : N → (unitInterval)) :
    permuteCubeLoop p e u = p (fun i => u (e i)) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_one {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_mul {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e f : Equiv.Perm N) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_eq_symmAt_permute {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij = GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) :=
  by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change
    p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) =
      p
        (fun k =>
          if Equiv.swap i j k = i then (unitInterval.symm) (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem HigherHurewicz.NativeSubdivision.nativeClass_quarterTurn {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    nativeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeClass p :=
  (nativeClass_homotopic ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩).symm

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) : nativeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeClass p :=
  by
  have h := nativeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_additiveClass {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] [Fintype N] (p : GenLoop N X x)
    (e : Equiv.Perm N) :
    nativeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_iff_mo1973_8180 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : k ≤ i.val) : (i.succAbove j).val < k ↔ j.val < k :=
  by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_succ]
    omega

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_succ_iff_mo1973_8181 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : i.val ≤ k) :
    (i.succAbove j).val < k + 1 ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_le {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i ε u) k = prefixMinimum u k := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_iff_mo1973_8180 i _ k h, not_lt_of_ge h, false_implies, true_and]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_succ {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i ε u) (k + 1) = Min.min ε (prefixMinimum u k) := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    le_min_iff]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_succ_iff_mo1973_8181 i _ k h, Nat.lt_succ_of_le h, true_implies]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i 1 u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le i 1 u k h

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i 1 u) (k + 1) = prefixMinimum u k := by
  rw [prefixMinimum_insertNth_succ i 1 u k h]
  exact min_eq_right (show prefixMinimum u k ≤ (⊤ : (unitInterval)) from le_top)

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_last_le {n : ℕ}
    (u : Fin n → (unitInterval)) (ε : (unitInterval)) (k : ℕ) (hk : k ≤ n) :
    prefixMinimum (Fin.insertNth (Fin.last n) ε u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le (Fin.last n) ε u k hk

def HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (HigherHurewicz.CubeTriangulation.cubeSimplex e).comp
    (HigherHurewicz.SimplexGeometry.simplexQuotient n)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplex_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    p (HigherHurewicz.CubeTriangulation.cubeSimplex e s) = x := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := hs
    have hi0 : i = 0 := Fin.ext (by omega)
    subst i
    have hsum : s 0 = 1 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using stdSimplex.sum_eq_one s
    exact False.elim (by linarith)
  | succ
    n =>
    rcases HigherHurewicz.CubeTriangulation.cubeSimplex_simplexBoundary e s hs with h |
      ⟨i, j, hij, h⟩
    · exact p.property _ h
    · exact hp _ i j hij h

def HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) : HigherHurewicz.SimplexGeometry.BasedSimplex n x :=
  ⟨p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e), nativeCubeSimplex_based p hp e⟩

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeCubeSimplexQuotient e u) = x :=
  nativeCubeSimplex_based p hp e _ (HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu)

def HigherHurewicz.NativeSubdivision.insertPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans (e.optionCongr.trans finSuccEquivLast.symm)

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_at {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : insertPermutation e r r = Fin.last n := by
  simp [insertPermutation]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_succAbove {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r (r.succAbove j) = (e j).castSucc := by simp [insertPermutation]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_symm_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : (insertPermutation e r).symm (Fin.last n) = r := by
  apply (insertPermutation e r).injective
  simp

theorem HigherHurewicz.NativeSubdivision.insertPermutation_pair_injective {n : ℕ} :
    Function.Injective
      (fun er : Equiv.Perm (Fin n) × Fin (n + 1) => insertPermutation er.1 er.2) := by
  rintro ⟨e, r⟩ ⟨f, s⟩ h
  have hrs : r = s := by
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E.symm (Fin.last n)) h
  subst s
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Fin.castSucc_injective n
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E (r.succAbove j)) h
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e, r)) hef

theorem HigherHurewicz.NativeSubdivision.optionCongr_removeNone_of_none {α β : Type*}
    (e : Option α ≃ Option β) (h : e Option.none = Option.none) : e.removeNone.optionCongr = e := by
  apply Equiv.ext
  intro a
  cases a with
  | none => simpa using h.symm
  | some a =>
    change Option.some (e.removeNone a) = e (Option.some a)
    cases ha : e (Option.some a) with
    | none =>
      have : Option.some a = Option.none := e.injective (ha.trans h.symm)
      cases this
    | some b => simpa only [ha] using e.removeNone_some ⟨b, ha⟩

def HigherHurewicz.NativeSubdivision.deletePermutationOption {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Option (Fin n)) :=
  (finSuccEquiv' (E.symm (Fin.last n))).symm.trans (E.trans finSuccEquivLast)

@[simp]
theorem HigherHurewicz.NativeSubdivision.deletePermutationOption_none {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : deletePermutationOption E Option.none = Option.none := by
  simp [deletePermutationOption]

def HigherHurewicz.NativeSubdivision.deletePermutation {n : ℕ} (E : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  (deletePermutationOption E).removeNone

theorem HigherHurewicz.NativeSubdivision.deletePermutation_castSucc {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (deletePermutation E j).castSucc = E ((E.symm (Fin.last n)).succAbove j) := by
  have h :=
    congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (Option.some j))
      (optionCongr_removeNone_of_none (deletePermutationOption E)
        (deletePermutationOption_none E))
  have h' := congrArg finSuccEquivLast.symm h
  simpa only [deletePermutation, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquivLast_symm_some, deletePermutationOption, Equiv.trans_apply,
    finSuccEquiv'_symm_some, Equiv.symm_apply_apply] using h'

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_deletePermutation {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) :
    insertPermutation (deletePermutation E) (E.symm (Fin.last n)) = E := by
  ext i
  refine Fin.succAboveCases (E.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [insertPermutation_apply_succAbove, deletePermutation_castSucc]

def HigherHurewicz.NativeSubdivision.insertPermutationEquiv (n : ℕ) :
    (Equiv.Perm (Fin n) × Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1))
    where
  toFun er := insertPermutation er.1 er.2
  invFun E := (deletePermutation E, E.symm (Fin.last n))
  left_inv
    er :=
    insertPermutation_pair_injective
      (insertPermutation_deletePermutation (insertPermutation er.1 er.2))
  right_inv := insertPermutation_deletePermutation

theorem HigherHurewicz.NativeSubdivision.sum_insertPermutation {n : ℕ} {A : Type*}
    [AddCommMonoid A] (F : Equiv.Perm (Fin (n + 1)) → A) :
    ∑ E, F E = ∑ e : Equiv.Perm (Fin n), ∑ r : Fin (n + 1), F (insertPermutation e r) := by
  rw [← (insertPermutationEquiv n).sum_comp F, Fintype.sum_prod_type]
  rfl

structure HigherHurewicz.NativeSubdivision.NativeChamberChart {n : ℕ}
    (e : Equiv.Perm (Fin n)) where
  toContinuousMap : C(NativeCube (Fin n), NativeCube (Fin n))
  zero_last : ∀ u i, i.val + 1 = n → u (e i) = 0 → toContinuousMap u (e i) = 0
  zero_adjacent :
    ∀ u i j, i.val + 1 = j.val → u (e i) = 0 → toContinuousMap u (e i) = toContinuousMap u (e j)
  one_first : ∀ u i, i.val = 0 → u (e i) = 1 → toContinuousMap u (e i) = 1
  one_adjacent :
    ∀ u i j, j.val + 1 = i.val → u (e i) = 1 → toContinuousMap u (e i) = toContinuousMap u (e j)

def HigherHurewicz.NativeSubdivision.chamberLower {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : r.val < n then (ContinuousMap.eval (e ⟨r.val, h⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 0

def HigherHurewicz.NativeSubdivision.chamberUpper {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : 0 < r.val then (ContinuousMap.eval (e ⟨r.val - 1, by omega⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 1

theorem HigherHurewicz.NativeSubdivision.chamberLower_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) : chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  have hr : r.val < n := h ▸ k.isLt
  have hk : (⟨r.val, hr⟩ : Fin n) = k := Fin.ext h
  simp [chamberLower, hr, hk]

theorem HigherHurewicz.NativeSubdivision.chamberLower_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = n) :
    chamberLower e r chart u = 0 := by simp [chamberLower, h]

theorem HigherHurewicz.NativeSubdivision.chamberUpper_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) : chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  have hr : 0 < r.val := by omega
  have hk : (⟨r.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  simp [chamberUpper, hr, hk]

theorem HigherHurewicz.NativeSubdivision.chamberUpper_first {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = 0) :
    chamberUpper e r chart u = 1 := by simp [chamberUpper, h]

theorem HigherHurewicz.NativeSubdivision.chamberLower_zero_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) (hu : u (e k) = 0) :
    chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : r.val < n
  · let j : Fin n := ⟨r.val, hr⟩
    rw [chamberLower_of_rank e r chart u j rfl]
    exact (chart.zero_adjacent u k j (by simpa [j] using h.symm) hu).symm
  · have hn : r.val = n := by omega
    rw [chamberLower_last e r chart u hn]
    exact (chart.zero_last u k (by omega) hu).symm

theorem HigherHurewicz.NativeSubdivision.chamberUpper_one_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) (hu : u (e k) = 1) :
    chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : 0 < r.val
  · let j : Fin n := ⟨r.val - 1, by omega⟩
    rw [chamberUpper_of_rank e r chart u j (by dsimp [j]; omega)]
    exact (chart.one_adjacent u k j (by dsimp [j]; omega) hu).symm
  · have hz : r.val = 0 := by omega
    rw [chamberUpper_first e r chart u hz]
    exact (chart.one_first u k (by omega) hu).symm

def HigherHurewicz.NativeSubdivision.chamberOldCoordinates {n : ℕ} :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin n))
    where
  toFun u k := u k.castSucc
  continuous_toFun := continuous_pi fun _ => continuous_apply _

def HigherHurewicz.NativeSubdivision.insertChamberMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin (n + 1)))
    where
  toFun
    u :=
    Fin.lastCases
      (Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)))
      (chart.toContinuousMap (chamberOldCoordinates u))
  continuous_toFun := by
    apply continuous_pi
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.lastCases_last]
      exact
        Set.Icc.continuous_convexComb_prod.comp
          (((chamberLower e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
            (((chamberUpper e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
              (continuous_apply (Fin.last n))))
    · simp only [Fin.lastCases_castSucc]
      exact
        (continuous_apply j).comp
          (chart.toContinuousMap.continuous.comp chamberOldCoordinates.continuous)

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_castSucc {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u k.castSucc = chart.toContinuousMap (chamberOldCoordinates u) k :=
  by simp [insertChamberMap]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp [insertChamberMap]

theorem HigherHurewicz.NativeSubdivision.chamberSuccAbove_val_cases {n : ℕ} (r : Fin (n + 1))
    (i : Fin n) :
    ((r.succAbove i).val = i.val ∧ i.val < r.val) ∨
      ((r.succAbove i).val = i.val + 1 ∧ r.val ≤ i.val) := by
  by_cases h : i.castSucc < r
  · exact Or.inl ⟨congrArg Fin.val (Fin.succAbove_of_castSucc_lt r i h), h⟩
  · exact
      Or.inr
        ⟨congrArg Fin.val (Fin.succAbove_of_le_castSucc r i (le_of_not_gt h)), le_of_not_gt h⟩

theorem HigherHurewicz.NativeSubdivision.chamberUpper_succ_eq_lower_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin m) (u : NativeCube (Fin m)) :
    chamberUpper e j.succ chart u = chamberLower e j.castSucc chart u := by
  rw [chamberUpper_of_rank e j.succ chart u j rfl,
    chamberLower_of_rank e j.castSucc chart u j rfl]

def HigherHurewicz.NativeSubdivision.chamberCutSequence {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) : Fin (m + 2) → C(NativeCube (Fin m), (unitInterval)) :=
  Fin.cons (ContinuousMap.const _ 0) (fun j : Fin (m + 1) => chamberUpper e j.rev chart)

theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_succ {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.succ u = chamberUpper e j.rev chart u := by
  simp [chamberCutSequence]

@[simp]
theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_last {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart (Fin.last (m + 1)) u = 1 := by
  change chamberUpper e (Fin.last m).rev chart u = 1
  rw [Fin.rev_last]
  exact chamberUpper_first e 0 chart u rfl

theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.castSucc u = chamberLower e j.rev chart u := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change 0 = chamberLower e (0 : Fin (m + 1)).rev chart u
    rw [Fin.rev_zero]
    exact (chamberLower_last e (Fin.last m) chart u rfl).symm
  · change chamberUpper e k.castSucc.rev chart u = chamberLower e k.succ.rev chart u
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact chamberUpper_succ_eq_lower_castSucc e chart k.rev u

theorem HigherHurewicz.NativeSubdivision.chamberCuts_sum_rev {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (m + 1) → A) : ∑ j : Fin (m + 1), f j.rev = ∑ j : Fin (m + 1), f j :=
  Equiv.sum_comp Fin.revPerm f

def HigherHurewicz.NativeSubdivision.cubeRestriction {m n : ℕ} (h : m ≤ n) :
    C(NativeCube (Fin n), NativeCube (Fin m))
    where
  toFun u i := u (Fin.castLE h i)
  continuous_toFun := continuous_pi fun i => continuous_apply (Fin.castLE h i)

@[simp]
theorem HigherHurewicz.NativeSubdivision.cubeRestriction_apply {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin m) : cubeRestriction h u i = u (Fin.castLE h i) :=
  rfl

def HigherHurewicz.NativeSubdivision.extendCubeMap {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) : C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := if hi : i.val < m then f (cubeRestriction h u) ⟨i.val, hi⟩ else u i
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      exact (continuous_apply ⟨i.val, hi⟩).comp (f.continuous.comp (cubeRestriction h).continuous)
    · simpa only [dif_neg hi] using
        (continuous_apply i : Continuous fun u : NativeCube (Fin n) => u i)

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_castLE {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin m) :
    extendCubeMap h f u (Fin.castLE h i) = f (cubeRestriction h u) i := by simp [extendCubeMap]

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) : extendCubeMap h f u i = u i := by simp [extendCubeMap, Nat.not_lt.mpr hi]

theorem HigherHurewicz.NativeSubdivision.cubeRestriction_update_outside {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) (v : (unitInterval)) :
    cubeRestriction h (Function.update u i v) = cubeRestriction h u := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  exact (Nat.not_lt.mpr hi) (hv ▸ j.isLt)

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_update_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) (v : (unitInterval)) :
    extendCubeMap h f (Function.update u i v) = Function.update (extendCubeMap h f u) i v := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendCubeMap_outside h f _ i hi]
  · rw [Function.update_of_ne hj]
    by_cases hjm : j.val < m
    · simp only [extendCubeMap, ContinuousMap.coe_mk, dif_pos hjm]
      rw [cubeRestriction_update_outside h u i hi v]
    · rw [extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm), Function.update_of_ne hj]

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_refl {n : ℕ}
    (f : C(NativeCube (Fin n), NativeCube (Fin n))) : extendCubeMap (le_refl n) f = f := by
  ext u i
  simp [cubeRestriction, extendCubeMap]

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_zero {n : ℕ} (h : 0 ≤ n)
    (f : C(NativeCube (Fin 0), NativeCube (Fin 0))) : extendCubeMap h f = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro u
  funext i
  exact extendCubeMap_outside h f u i (Nat.zero_le _)

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_sameFlat {m n : ℕ} (h : m ≤ n)
    (f g : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n))
    (hfg : NativeCubeSameFlat (f (cubeRestriction h u)) (g (cubeRestriction h u))) :
    NativeCubeSameFlat (extendCubeMap h f u) (extendCubeMap h g u) := by
  cases hfg with
  | zero i hf hg => exact .zero (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | one i hf hg => exact .one (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | equal i j hij hf hg =>
    exact
      .equal (Fin.castLE h i) (Fin.castLE h j)
        (fun heq => hij (Fin.ext (congrArg (fun k : Fin n => k.val) heq))) (by simpa using hf)
        (by simpa using hg)

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val + 1 = n + 1)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) = 0 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_zero]
    exact chamberLower_last e r chart (chamberOldCoordinates u) (by omega)
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.zero_last (chamberOldCoordinates u) k (by omega) hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_zero]
      exact chamberLower_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_zero_face e r chart (chamberOldCoordinates u) k hr hu,
        chamberUpper_of_rank e r chart (chamberOldCoordinates u) k hr]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : k.val + 1 = l.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.zero_adjacent (chamberOldCoordinates u) k l hkl hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val = 0)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) = 1 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_one]
    exact chamberUpper_first e r chart (chamberOldCoordinates u) hi
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.one_first (chamberOldCoordinates u) k (by omega) hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : j.val + 1 = i.val)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_one]
      exact chamberUpper_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_of_rank e r chart (chamberOldCoordinates u) k hr,
        chamberUpper_one_face e r chart (chamberOldCoordinates u) k hr hu]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : l.val + 1 = k.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.one_adjacent (chamberOldCoordinates u) k l hkl hu

def HigherHurewicz.NativeSubdivision.insertChamberChart {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : NativeChamberChart (insertPermutation e r)
    where
  toContinuousMap := insertChamberMap e r chart
  zero_last := insertChamberMap_zero_last e r chart
  zero_adjacent := insertChamberMap_zero_adjacent e r chart
  one_first := insertChamberMap_one_first e r chart
  one_adjacent := insertChamberMap_one_adjacent e r chart

@[ext]
theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.ext {n : ℕ} {e : Equiv.Perm (Fin n)}
    {f g : HigherHurewicz.NativeSubdivision.NativeChamberChart e}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

def HigherHurewicz.NativeSubdivision.chamberCutIndex {m n : ℕ} (h : m + 1 ≤ n) : Fin n :=
  Fin.castLE h (Fin.last m)

theorem HigherHurewicz.NativeSubdivision.chamberCutIndex_ne_castLE {m n : ℕ} (h : m + 1 ≤ n)
    (j : Fin m) : Fin.castLE (Nat.le_of_succ_le h) j ≠ chamberCutIndex h := by
  intro he
  have hv := congrArg Fin.val he
  exact (Nat.ne_of_lt j.isLt) hv

@[simp]
theorem HigherHurewicz.NativeSubdivision.chamberOldCoordinates_cubeRestriction {m n : ℕ}
    (h : m + 1 ≤ n) (u : NativeCube (Fin n)) :
    chamberOldCoordinates (cubeRestriction h u) = cubeRestriction (Nat.le_of_succ_le h) u :=
  rfl

theorem HigherHurewicz.NativeSubdivision.extend_insertChamberMap {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (r : Fin (m + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin n)) :
    extendCubeMap h (insertChamberMap e r chart) u =
      Function.update (extendCubeMap (Nat.le_of_succ_le h) chart.toContinuousMap u)
        (chamberCutIndex h)
        (Set.Icc.convexComb (chamberLower e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (chamberUpper e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (u (chamberCutIndex h))) := by
  funext j
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k.castSucc = j := Fin.ext rfl
    have hk' : Fin.castLE h k.castSucc = Fin.castLE (Nat.le_of_succ_le h) k := Fin.ext rfl
    have hji : j ≠ chamberCutIndex h := by
      rw [← hk, hk']
      exact chamberCutIndex_ne_castLE h k
    rw [Function.update_of_ne hji, ← hk, extendCubeMap_castLE, insertChamberMap_apply_castSucc,
      chamberOldCoordinates_cubeRestriction, hk', extendCubeMap_castLE]
  · by_cases hji : j = chamberCutIndex h
    · subst j
      rw [Function.update_self]
      change extendCubeMap h (insertChamberMap e r chart) u (Fin.castLE h (Fin.last m)) = _
      rw [extendCubeMap_castLE, insertChamberMap_apply_last,
        chamberOldCoordinates_cubeRestriction]
      rfl
    · have hjval : j.val ≠ m := fun he => hji (Fin.ext he)
      have hmj : m + 1 ≤ j.val := by omega
      rw [extendCubeMap_outside h _ u j hmj, Function.update_of_ne hji,
        extendCubeMap_outside (Nat.le_of_succ_le h) _ u j (Nat.le_of_succ_le hmj)]

def HigherHurewicz.NativeSubdivision.extendedChamberCutSequence {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) :
    Fin (m + 2) → C(NativeCube (Fin n), (unitInterval)) := fun j =>
  (chamberCutSequence e chart j).comp (cubeRestriction (Nat.le_of_succ_le h))

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_zero {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart 0 u = 0 :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_last {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart (Fin.last (m + 1)) u = 1 :=
  chamberCutSequence_last e chart _

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_castSucc {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.castSucc u =
      chamberLower e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_castSucc e chart j _

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_succ {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.succ u =
      chamberUpper e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_succ e chart j _

theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.sameFlat {m : ℕ}
    {e : Equiv.Perm (Fin m)} (chart other : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin m)) (hu : u ∈ Cube.boundary (Fin m)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  let i := e.symm j
  have hei : e i = j := e.apply_symm_apply j
  rcases hj with hj | hj
  · have hi : u (e i) = 0 := hei ▸ hj
    by_cases hilast : i.val + 1 = m
    · exact .zero (e i) (chart.zero_last u i hilast hi) (other.zero_last u i hilast hi)
    · let k : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hik : i.val + 1 = k.val := rfl
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.zero_adjacent u i k hik hi)
          (other.zero_adjacent u i k hik hi)
  · have hi : u (e i) = 1 := hei ▸ hj
    by_cases hifirst : i.val = 0
    · exact .one (e i) (chart.one_first u i hifirst hi) (other.one_first u i hifirst hi)
    · let k : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hki : k.val + 1 = i.val := by dsimp [k]; omega
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.one_adjacent u i k hki hi) (other.one_adjacent u i k hki hi)

theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_sameFlat {m n : ℕ} (h : m ≤ n)
    {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (extendCubeMap h chart.toContinuousMap u)
      (extendCubeMap h other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k = j := Fin.ext rfl
    apply extendCubeMap_sameFlat
    apply chart.sameFlat other
    refine ⟨k, ?_⟩
    simpa only [cubeRestriction_apply, hk] using hj
  · rcases hj with hj | hj
    · exact
        .zero j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
    · exact
        .one j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)

theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (extendCubeMap h chart.toContinuousMap u) = x := by
  simpa only [nativeCubeBlend_zero] using
    nativeCubeBlend_based p hp (extendedChamberMap_sameFlat h chart chart u hu) 0

def HigherHurewicz.NativeSubdivision.extendedChamberLoop {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) : GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (extendCubeMap h chart.toContinuousMap)
    (extendedChamberMap_based p hp h chart)

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_apply {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberLoop p hp h chart u = p (extendCubeMap h chart.toContinuousMap u) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : 0 ≤ n) {e : Equiv.Perm (Fin 0)} (chart : NativeChamberChart e) :
    extendedChamberLoop p hp h chart = p := by
  apply GenLoop.ext
  intro u
  simp

def HigherHurewicz.NativeSubdivision.extendedChamberHomotopy {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    (extendedChamberLoop p hp h chart).val.HomotopyRel (extendedChamberLoop p hp h other).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (extendCubeMap h chart.toContinuousMap)
    (extendCubeMap h other.toContinuousMap) (extendedChamberMap_based p hp h chart)
    (extendedChamberMap_based p hp h other) (extendedChamberMap_sameFlat h chart other)

theorem HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp h chart) =
      nativeClass (extendedChamberLoop p hp h other) :=
  nativeClass_homotopic ⟨extendedChamberHomotopy p hp h chart other⟩

def HigherHurewicz.NativeSubdivision.CutIndependent {N : Type*} [DecidableEq N] (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

def HigherHurewicz.NativeSubdivision.CutBased {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

def HigherHurewicz.NativeSubdivision.sliceMap {N : Type*} [DecidableEq N] (i : N)
    (a b : C(NativeCube N, (unitInterval))) : C(NativeCube N, NativeCube N)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

theorem HigherHurewicz.NativeSubdivision.sliceMap_based {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) (hu : u ∈ Cube.boundary N) : p (sliceMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [sliceMap, hj] using ha u
    · simpa [sliceMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [sliceMap, hji] using hj⟩

def HigherHurewicz.NativeSubdivision.sliceLoop {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b) :
    GenLoop N X x :=
  ⟨p.val.comp (sliceMap i a b), sliceMap_based p i a b ha hb⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.sliceLoop_apply {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) :
    sliceLoop p i a b ha hb u = p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

theorem HigherHurewicz.NativeSubdivision.sliceLoop_self {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (a : C(NativeCube N, (unitInterval)))
    (ha : CutBased p i a) : sliceLoop p i a a ha ha = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simpa only [sliceLoop_apply, Set.Icc.convexComb_eq, GenLoop.const_apply] using ha u

theorem HigherHurewicz.NativeSubdivision.sliceLoop_full {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (ha0 : ∀ u, a u = 0) (hb1 : ∀ u, b u = 1) : sliceLoop p i a b ha hb = p := by
  apply GenLoop.ext
  intro u
  simp [ha0 u, hb1 u]

def HigherHurewicz.NativeSubdivision.sliceHomotopyOfCoordinate {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (q : GenLoop N X x) (w : C(NativeCube N, (unitInterval)))
    (hq : ∀ u, q u = p (Function.update u i (w u))) (hw0 : ∀ u, u i = 0 → w u = a u)
    (hw1 : ∀ u, u i = 1 → w u = b u) :
    (sliceLoop p i a b ha hb).val.HomotopyRel q.val (Cube.boundary N)
    where
  toFun
    v :=
    p
      (Function.update v.2 i
        (Set.Icc.convexComb (Set.Icc.convexComb (a v.2) (b v.2) (v.2 i)) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          ((Set.Icc.continuous_convexComb_prod.comp
                ((a.continuous.comp continuous_snd).prodMk
                  ((b.continuous.comp continuous_snd).prodMk
                    ((continuous_apply i).comp continuous_snd)))).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 0)) =
        _
    rw [Set.Icc.convexComb_zero]
    rfl
  map_one_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 1)) =
        q u
    rw [Set.Icc.convexComb_one]
    exact (hq u).symm
  prop' t u
    hu := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) t)) =
        sliceLoop p i a b ha hb u
    have hs : sliceLoop p i a b ha hb u = x := (sliceLoop p i a b ha hb).property u hu
    rw [hs]
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · simpa [hj, hw0 u hj] using ha u
      · simpa [hj, hw1 u hj] using hb u
    · exact p.property _ ⟨j, by simpa [hji] using hj⟩

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_independent {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutIndependent (chamberCutIndex h) (extendedChamberCutSequence h e chart j) := by
  intro u v
  change
    chamberCutSequence e chart j
        (cubeRestriction (Nat.le_of_succ_le h) (Function.update u (chamberCutIndex h) v)) =
      chamberCutSequence e chart j (cubeRestriction (Nat.le_of_succ_le h) u)
  rw [cubeRestriction_update_outside (Nat.le_of_succ_le h) u (chamberCutIndex h) (le_refl m) v]

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutBased (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j) := by
  intro u
  rw [extendedChamberLoop_apply,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  refine Fin.cases ?_ (fun r => ?_) j
  · rw [extendedChamberCutSequence_zero]
    exact p.property _ ⟨chamberCutIndex h, Or.inl (Function.update_self _ _ _)⟩
  · rw [extendedChamberCutSequence_succ]
    by_cases hr : 0 < r.rev.val
    · let k : Fin m := ⟨r.rev.val - 1, by have := r.rev.isLt; omega⟩
      have hk : r.rev.val = k.val + 1 := by
        change r.rev.val = (r.rev.val - 1) + 1
        omega
      rw [chamberUpper_of_rank e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) k hk]
      apply
        hp _ (chamberCutIndex h) (Fin.castLE (Nat.le_of_succ_le h) (e k))
          (chamberCutIndex_ne_castLE h (e k)).symm
      rw [Function.update_self, Function.update_of_ne (chamberCutIndex_ne_castLE h (e k)),
        extendCubeMap_castLE]
    · have hr0 : r.rev.val = 0 := by omega
      rw [chamberUpper_first e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) hr0]
      exact p.property _ ⟨chamberCutIndex h, Or.inr (Function.update_self _ _ _)⟩

def HigherHurewicz.NativeSubdivision.cutBinaryWarp :
    C(((unitInterval) × (unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb
      (Set.Icc.convexComb p.1.1 p.1.2.1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))) p.1.2.2
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_apply (a b c t : (unitInterval)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb (Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)))) c
        (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_zero (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 0) = a := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_one (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 1) = c := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_le_half (a b c t : (unitInterval))
    (ht : (t : ℝ) ≤ 1 / 2) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) := by
  have hz : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, hz, Set.Icc.convexComb_zero]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_le (a b c t : (unitInterval))
    (ht : 1 / 2 ≤ (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := by
  have ho : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, ho, Set.Icc.convexComb_one]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_lt (a b c t : (unitInterval))
    (ht : 1 / 2 < (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  cutBinaryWarp_of_half_le a b c t ht.le

def HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) : C(NativeCube N, (unitInterval))
    where
  toFun u := cutBinaryWarp ((a u, b u, c u), u i)
  continuous_toFun :=
    cutBinaryWarp.continuous.comp
      ((a.continuous.prodMk (b.continuous.prodMk c.continuous)).prodMk (continuous_apply i))

theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_zero {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 0) :
    sliceBinaryCoordinate i a b c u = a u := by simp [sliceBinaryCoordinate, hu]

theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_one {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 1) :
    sliceBinaryCoordinate i a b c u = c u := by simp [sliceBinaryCoordinate, hu]

theorem HigherHurewicz.NativeSubdivision.sliceTrans_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) (u : NativeCube N) :
    GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc) u =
      p (Function.update u i (sliceBinaryCoordinate i a b c u)) := by
  change
    (if (u i : ℝ) ≤ 1 / 2 then
        sliceLoop p i a b ha hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        sliceLoop p i b c hb hc
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) =
      p (Function.update u i (cutBinaryWarp ((a u, b u, c u), u i)))
  split_ifs with h
  · rw [sliceLoop_apply, haInd u _, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_le_half (a u) (b u) (c u) (u i) h).symm
  · rw [sliceLoop_apply, hbInd u _, hcInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_half_lt (a u) (b u) (c u) (u i) (lt_of_not_ge h)).symm

theorem HigherHurewicz.NativeSubdivision.slice_homotopic_trans {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) :
    GenLoop.Homotopic (sliceLoop p i a c ha hc)
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc)) :=
  ⟨sliceHomotopyOfCoordinate p i a c ha hc
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc))
      (sliceBinaryCoordinate i a b c) (sliceTrans_apply p i a b c ha hb hc haInd hbInd hcInd)
      (sliceBinaryCoordinate_zero i a b c) (sliceBinaryCoordinate_one i a b c)⟩

theorem HigherHurewicz.NativeSubdivision.slice_toLoop_transAt {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) (a b : GenLoop N X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

theorem HigherHurewicz.NativeSubdivision.slice_transAt_homotopic {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) {a b c d : GenLoop N X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [slice_toLoop_transAt, slice_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

def HigherHurewicz.NativeSubdivision.sliceConcat {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) :
    (k : ℕ) →
      (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) →
        (∀ j, CutBased p i (a j)) → GenLoop N X x
  | 0, _, _ => GenLoop.const
  | k + 1, a, ha =>
    GenLoop.transAt i
      (sliceLoop p i (a 0) (a (0 : Fin (k + 1)).succ) (ha 0) (ha (0 : Fin (k + 1)).succ))
      (sliceConcat p i k (fun j => a j.succ) (fun j => ha j.succ))

theorem HigherHurewicz.NativeSubdivision.slice_homotopic_concat {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) :
    GenLoop.Homotopic (sliceLoop p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)))
      (sliceConcat p i k a ha) := by
  induction k with
  | zero =>
    change GenLoop.Homotopic (sliceLoop p i (a 0) (a 0) (ha 0) (ha 0)) GenLoop.const
    rw [sliceLoop_self]
  | succ k
    ih =>
    have ht := ih (fun j => a j.succ) (fun j => ha j.succ) (fun j => hInd j.succ)
    have hs :=
      slice_homotopic_trans p i (a 0) (a (0 : Fin (k + 1)).succ) (a (Fin.last (k + 1))) (ha 0)
        (ha (0 : Fin (k + 1)).succ) (ha (Fin.last (k + 1))) (hInd 0) (hInd (0 : Fin (k + 1)).succ)
        (hInd (Fin.last (k + 1)))
    apply hs.trans
    apply slice_transAt_homotopic
    · exact GenLoop.Homotopic.refl _
    · exact ht

theorem HigherHurewicz.NativeSubdivision.sliceConcat_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j)) :
    nativeClass (sliceConcat p i k a ha) =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) := by
  induction k with
  | zero => simp [sliceConcat]
  | succ k ih =>
    rw [sliceConcat, nativeClass_transAt, ih, Fin.sum_univ_succ]
    rfl

theorem HigherHurewicz.NativeSubdivision.finiteCuts_homotopic {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) : GenLoop.Homotopic p (sliceConcat p i k a ha) := by
  have h := slice_homotopic_concat p i k a ha hInd
  rwa [sliceLoop_full p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)) hzero hone] at h

theorem HigherHurewicz.NativeSubdivision.finiteCuts_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) :
    nativeClass p =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) :=
  (nativeClass_homotopic (finiteCuts_homotopic p i k a ha hInd hzero hone)).trans
    (sliceConcat_class p i k a ha)

theorem HigherHurewicz.NativeSubdivision.extendedChamberCut_slice_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1)) :
    sliceLoop (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
        (extendedChamberCutSequence h e chart j.castSucc)
        (extendedChamberCutSequence h e chart j.succ)
        (extendedChamberCutSequence_based p hp h e chart j.castSucc)
        (extendedChamberCutSequence_based p hp h e chart j.succ) =
      extendedChamberLoop p hp h (insertChamberChart e j.rev chart) := by
  apply GenLoop.ext
  intro u
  rw [sliceLoop_apply, extendedChamberLoop_apply, extendedChamberCutSequence_castSucc,
    extendedChamberCutSequence_succ,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  exact congrArg p (extend_insertChamberMap h e j.rev chart u).symm

theorem HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq_sum_insertions {m n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ r : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart)) := by
  have hcut :=
    finiteCuts_class (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (m + 1) (extendedChamberCutSequence h e chart)
      (extendedChamberCutSequence_based p hp h e chart)
      (extendedChamberCutSequence_independent h e chart)
      (extendedChamberCutSequence_zero h e chart) (extendedChamberCutSequence_last h e chart)
  have hrev :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ j : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e j.rev chart)) := by
    simpa only [extendedChamberCut_slice_eq p hp h e chart] using hcut
  exact
    hrev.trans
      (chamberCuts_sum_rev
        (fun r => nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart))))

def HigherHurewicz.NativeSubdivision.prefixProduct {n : ℕ} (u : NativeCube (Fin n)) (k : ℕ) :
    (unitInterval) :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), u i

@[simp]
theorem HigherHurewicz.NativeSubdivision.prefixProduct_zero {n : ℕ} (u : NativeCube (Fin n)) :
    prefixProduct u 0 = 1 := by simp [prefixProduct]

theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (hk : k < n) : prefixProduct u (k + 1) = prefixProduct u k * u ⟨k, hk⟩ := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

theorem HigherHurewicz.NativeSubdivision.prefixProduct_eq_zero_of_coordinate {n : ℕ}
    (u : NativeCube (Fin n)) (k : ℕ) (i : Fin n) (hik : i.val < k) (hi : u i = 0) :
    prefixProduct u k = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩) hi

theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ_of_one {n : ℕ}
    (u : NativeCube (Fin n)) (i : Fin n) (hi : u i = 1) :
    prefixProduct u (i.val + 1) = prefixProduct u i.val := by
  rw [prefixProduct_succ u i.val i.isLt, hi, mul_one]

theorem HigherHurewicz.NativeSubdivision.continuous_prefixProduct (n k : ℕ) :
    Continuous (fun u : NativeCube (Fin n) => prefixProduct u k) := by
  unfold prefixProduct
  generalize Finset.univ.filter (fun i : Fin n => i.val < k) = s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : NativeCube (Fin n) => (1 : (unitInterval))))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact
      ((continuous_subtype_val.comp (continuous_apply i)).mul
            (continuous_subtype_val.comp ih)).subtype_mk
        _

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeCanonical (n : ℕ) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := prefixProduct u (i.val + 1)
  continuous_toFun := continuous_pi fun i => continuous_prefixProduct n (i.val + 1)

def HigherHurewicz.NativeSubdivision.nativeDuffyCube {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := nativeDuffyCubeCanonical n u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i =>
      (continuous_apply (e.symm i)).comp (nativeDuffyCubeCanonical n).continuous

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u (e i) = prefixProduct u (i.val + 1) := by simp [nativeDuffyCube_apply]

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeDuffyCube e u (e j) = 0 := by
  rw [nativeDuffyCube_coordinate]
  exact prefixProduct_eq_zero_of_coordinate u _ i (by omega) hi

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeDuffyCube e u (e 0) = 1 := by
  rw [nativeDuffyCube_coordinate, prefixProduct_succ_of_one u 0 hu]
  exact prefixProduct_zero u

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) : nativeDuffyCube e u (e i.castSucc) = nativeDuffyCube e u (e i.succ) := by
  rw [nativeDuffyCube_coordinate, nativeDuffyCube_coordinate,
    prefixProduct_succ_of_one u i.succ hi]
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin n) ∨
      ∃ i j : Fin n, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact Or.inl ⟨e i, Or.inl (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)⟩
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero => exact Or.inl ⟨e 0, Or.inr (nativeDuffyCube_coordinate_zero_of_one e u hi)⟩
      | succ i =>
        exact
          Or.inr
            ⟨e i.castSucc, e i.succ,
              e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this),
              nativeDuffyCube_adjacent_of_one e u i hi⟩

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

def HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeOrderedDuffyMap e u (e i) = prefixProduct (fun k => u (e k)) (i.val + 1) := by
  exact nativeDuffyCube_coordinate e (permuteCubeCoordinates e u) i

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j)
    (hi : u (e i) = 0) : nativeOrderedDuffyMap e u (e j) = 0 :=
  nativeDuffyCube_coordinate_eq_zero e (permuteCubeCoordinates e u) i j hij hi

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (_hi : i.val + 1 = n)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = 0 :=
  nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i.val + 1 = j.val)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu,
    nativeOrderedDuffyMap_coordinate_eq_zero e u i j (by omega) hu]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (hi : i.val = 0)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = 1 := by
  rw [nativeOrderedDuffyMap_coordinate, prefixProduct_succ_of_one (fun k => u (e k)) i hu, hi,
    prefixProduct_zero]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hji : j.val + 1 = i.val)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate, nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hji]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeOrderedDuffyMap e u) = x :=
  nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)

def HigherHurewicz.NativeSubdivision.nativeCubeOrderedDuffyHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (nativeOrderedDuffyMap_based p hp e) hfg

theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedDuffy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass (nativeDuffyCubeLoop p hp e) := by
  calc
    nativeClass (nativeCubePullbackLoop p f hf) =
        nativeClass (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e) :=
      nativeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp e f hf hfg⟩
    _ = _ := permuteCubeLoop_additiveClass _ e

def HigherHurewicz.NativeSubdivision.orderedDuffyChart {n : ℕ} (e : Equiv.Perm (Fin n)) :
    NativeChamberChart e
    where
  toContinuousMap := nativeOrderedDuffyMap e
  zero_last := nativeOrderedDuffyMap_zero_last e
  zero_adjacent := nativeOrderedDuffyMap_zero_adjacent e
  one_first := nativeOrderedDuffyMap_one_first e
  one_adjacent := nativeOrderedDuffyMap_one_adjacent e

theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.commonOrderedDuffy {n : ℕ}
    {e : Equiv.Perm (Fin n)} (chart : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap e u) :=
  chart.sameFlat (HigherHurewicz.NativeSubdivision.orderedDuffyChart e) u hu

theorem HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_partialChambers {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (m : ℕ) (h : m ≤ n) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin m), nativeClass (extendedChamberLoop p hp h (orderedDuffyChart e)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_insertPermutation]
    calc
      nativeClass p =
          ∑ e : Equiv.Perm (Fin m),
            nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) (orderedDuffyChart e)) :=
        ih (Nat.le_of_succ_le h)
      _ =
          ∑ e : Equiv.Perm (Fin m),
            ∑ r : Fin (m + 1),
              nativeClass
                (extendedChamberLoop p hp h (orderedDuffyChart (insertPermutation e r))) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [nativeClass_extendedChamber_eq_sum_insertions p hp h (orderedDuffyChart e)]
        apply Finset.sum_congr rfl
        intro r _
        exact
          nativeClass_extendedChamber_eq p hp h (insertChamberChart e r (orderedDuffyChart e))
            (orderedDuffyChart (insertPermutation e r))

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeCubeSimplexQuotient e u (e i) =
      HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) :=
  Subtype.ext (HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate e u i)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeCubeSimplexQuotient e u (e j) = 0 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  exact
    le_antisymm (hi ▸ HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate u _ i (by omega))
      bot_le

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeCubeSimplexQuotient e u (e 0) = 1 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  change HigherHurewicz.SimplexGeometry.prefixMinimum u (0 + 1) = 1
  rw [HigherHurewicz.SimplexGeometry.prefixMinimum_succ u 0 (Nat.zero_lt_succ n),
    HigherHurewicz.SimplexGeometry.prefixMinimum_zero]
  simp [hu]

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) :
    nativeCubeSimplexQuotient e u (e i.castSucc) = nativeCubeSimplexQuotient e u (e i.succ) := by
  rw [nativeCubeSimplexQuotient_coordinate, nativeCubeSimplexQuotient_coordinate,
    HigherHurewicz.SimplexGeometry.prefixMinimum_succ u i.succ.val i.succ.isLt]
  change
    HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) =
      Min.min (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)) (u i.succ)
  rw [hi,
    min_eq_left
      (show HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) ≤ 1 from
        (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)).property.2)]

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_simplex_sameFlat {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeSimplexQuotient e u) := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact
      .zero (e i) (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)
        (nativeCubeSimplexQuotient_coordinate_eq_zero e u i i le_rfl hi)
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero =>
        exact
          .one (e 0) (nativeDuffyCube_coordinate_zero_of_one e u hi)
            (nativeCubeSimplexQuotient_coordinate_zero_of_one e u hi)
      | succ i =>
        exact
          .equal (e i.castSucc) (e i.succ)
            (e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this))
            (nativeDuffyCube_adjacent_of_one e u i hi)
            (nativeCubeSimplexQuotient_adjacent_of_one e u i hi)

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeSimplexHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeSimplexQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeSimplexQuotient_based p hp e)
    (nativeDuffyCube_simplex_sameFlat e)

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_homotopic_basedSimplexLoop {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)) :=
  ⟨nativeDuffyCubeSimplexHomotopy p hp e⟩

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCubeClass_eq_basedSimplexClass {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeClass (nativeDuffyCubeLoop p hp e) =
      HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_homotopic (nativeDuffyCube_homotopic_basedSimplexLoop p hp e)

theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedSimplex {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  rw [nativeClass_commonOrderedDuffy p hp e f hf hfg, nativeDuffyCubeClass_eq_basedSimplexClass]
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeClass_chamber_eq_orientedSimplex {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (le_refl n) chart) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  apply
    nativeClass_commonOrderedSimplex p hp e (extendCubeMap (le_refl n) chart.toContinuousMap)
      (extendedChamberMap_based p hp (le_refl n) chart)
  intro u hu
  rw [extendCubeMap_refl]
  exact chart.commonOrderedDuffy u hu

theorem HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_simplices {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  calc
    nativeClass p =
        ∑ e : Equiv.Perm (Fin n),
          nativeClass (extendedChamberLoop p hp (le_refl n) (orderedDuffyChart e)) :=
      nativeClass_eq_sum_partialChambers p hp n (le_refl n)
    _ = _ :=
      Finset.sum_congr rfl fun e _ =>
        nativeClass_chamber_eq_orientedSimplex p hp e (orderedDuffyChart e)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_eq_sum_simplices p hp

end Mathoverflow1973
