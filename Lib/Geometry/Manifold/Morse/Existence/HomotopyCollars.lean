/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Flattening a homotopy near its ends

The reparametrisation `flattenTime t = max 0 (min 1 (3t - 1))` of the unit interval is `0` on
`[0, 1/3]` and `1` on `[2/3, 1]`, so for a homotopy `H` from `f` to `g` the map
`flattenedHomotopyMap H (t, x) = H (flattenTime t, x)` equals `f` for `t ≤ 1/3` and `g` for
`2/3 ≤ t`. If `f` and `g` are smooth, the flattened map is therefore smooth on the open set
`homotopyCollarNeighborhood = {t < 1/3} ∪ {2/3 < t}`, a neighbourhood of the closed collars
`homotopyCollars = {t ≤ 1/4} ∪ {3/4 ≤ t}`. This is the input for smoothing a homotopy relative
to its ends (cf. Lee, *Introduction to Smooth Manifolds*, Ch. 6, smooth homotopies).

## Main definitions and results

* `ManifoldSmoothing.flattenTime`, `ManifoldSmoothing.flattenedHomotopyMap`
* `ManifoldSmoothing.homotopyCollars`, `ManifoldSmoothing.homotopyCollarNeighborhood`
* `ManifoldSmoothing.contMDiffOn_flattenedHomotopyMap`

## Tags

homotopy, reparametrisation, collar
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Smoothing homotopies -/

/-- The flattening time function of a homotopy. -/
def ManifoldSmoothing.flattenTime (t : unitInterval) : unitInterval :=
  ⟨Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The flattening time is continuous. -/
theorem ManifoldSmoothing.continuous_flattenTime : Continuous flattenTime :=
  (continuous_const.max
      (continuous_const.min
        ((continuous_const.mul continuous_subtype_val).sub continuous_const))) |>.subtype_mk
    _

/-- The flattening time is zero on the lower collar. -/
theorem ManifoldSmoothing.flattenTime_eq_zero (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 3) :
    flattenTime t = 0 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

/-- The flattening time is one on the upper collar. -/
theorem ManifoldSmoothing.flattenTime_eq_one (t : unitInterval) (ht : 2 / 3 ≤ (t : ℝ)) :
    flattenTime t = 1 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The homotopy flattened to be stationary on the collars. -/
def ManifoldSmoothing.flattenedHomotopyMap {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) : C(unitInterval × X, N)
    where
  toFun q := H (flattenTime q.1, q.2)
  continuous_toFun :=
    H.continuous.comp ((continuous_flattenTime.comp continuous_fst).prodMk continuous_snd)

/-- The flattened homotopy on the lower collar. -/
theorem ManifoldSmoothing.flattenedHomotopyMap_lower {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : (t : ℝ) ≤ 1 / 3) : flattenedHomotopyMap H (t, x) = f x := by
  change H (flattenTime t, x) = f x
  rw [flattenTime_eq_zero t ht, H.apply_zero]

/-- The flattened homotopy on the upper collar. -/
theorem ManifoldSmoothing.flattenedHomotopyMap_upper {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : 2 / 3 ≤ (t : ℝ)) : flattenedHomotopyMap H (t, x) = g x := by
  change H (flattenTime t, x) = g x
  rw [flattenTime_eq_one t ht, H.apply_one]

/-! ### Homotopy collars -/

/-- The collar regions where the homotopy is flattened. -/
def ManifoldSmoothing.homotopyCollars (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (q.1 : ℝ)}

/-- A neighborhood of the homotopy collars. -/
def ManifoldSmoothing.homotopyCollarNeighborhood (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) < 1 / 3 ∨ 2 / 3 < (q.1 : ℝ)}

/-- The homotopy collars are closed. -/
theorem ManifoldSmoothing.isClosed_homotopyCollars {X : Type*} [TopologicalSpace X] :
    IsClosed (homotopyCollars X) :=
  (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst))

/-- The collar neighborhood is open. -/
theorem ManifoldSmoothing.isOpen_homotopyCollarNeighborhood {X : Type*}
    [TopologicalSpace X] : IsOpen (homotopyCollarNeighborhood X) :=
  (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst))

/-- The collars lie in the collar neighborhood. -/
theorem ManifoldSmoothing.homotopyCollars_subset {X : Type*} :
    homotopyCollars X ⊆ homotopyCollarNeighborhood X := by
  rintro q (hl | hu)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-! ### Existence of smoothings -/

/-- The flattened homotopy is smooth on the collar complement. -/
theorem ManifoldSmoothing.contMDiffOn_flattenedHomotopyMap {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ContMDiffOn ((𝓡∂ 1).prod I) J ∞ (flattenedHomotopyMap H) (homotopyCollarNeighborhood X) := by
  rintro q (hl | hu)
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => f r.2) :=
      hf.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => f r.2) := by
      have hn : {r : unitInterval × X | (r.1 : ℝ) < 1 / 3} ∈ 𝓝 q :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds hl
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_lower H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => g r.2) :=
      hg.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => g r.2) := by
      have hn : {r : unitInterval × X | 2 / 3 < (r.1 : ℝ)} ∈ 𝓝 q :=
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds hu
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_upper H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
