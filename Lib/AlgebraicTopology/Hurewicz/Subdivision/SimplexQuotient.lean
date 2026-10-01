/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension

/-!
# The simplex as a quotient of the cube

The `n`-cube `Fin n → I` maps onto the `n`-simplex by the *prefix minima* of the
coordinates: `Hurewicz.SimplexGeometry.simplexQuotient n` sends `u` to the point with
barycentric coordinates `extendedMinimum u i - extendedMinimum u (i + 1)`, where
`prefixMinimum u k = min {u i | i < k}`. On the Kuhn cell of the identity permutation
(`Hurewicz.CubeTriangulation.cubeSimplex 1`, the points with antitone coordinates) the
quotient is inverse to the cell map (`simplexQuotient_cubeSimplex_refl`); every other cell
is sent into the boundary of the simplex (`simplexQuotient_cubeSimplex_boundary`), and the
cube boundary goes to the simplex boundary (`simplexQuotient_boundary`).

A *based simplex* `BasedSimplex n x` is a singular simplex sending the boundary to `x`;
precomposition with the quotient turns it into a based cube `basedSimplexLoop τ`, whose
class in `π_n X x` is `basedSimplexClass τ`. The signed sum of its cell restrictions is its
corrected chain (`basedSimplex_simplexChain_sum`). The boundary strata of the quotient
(`simplexTwoBoundary`, `simplexQuotient_codimTwo`) and the behaviour of the prefix minima
under `Fin.insertNth` complete the calculus.

This is the cube-to-simplex half of the comparison used in this development's proof of the
Hurewicz theorem (statement: Hatcher, *Algebraic Topology*, Theorem 4.32; the argument is
recorded in `Lib/docs/C.md`); the Kuhn (Freudenthal)
triangulation of the cube is the one of `Lib.AlgebraicTopology.Hurewicz.CubeTriangulation`.

## Main definitions

* `Hurewicz.SimplexGeometry.prefixMinimum`, `Hurewicz.SimplexGeometry.extendedMinimum`
* `Hurewicz.SimplexGeometry.simplexQuotient`
* `Hurewicz.SimplexGeometry.BasedSimplex`, `Hurewicz.SimplexGeometry.basedSimplexLoop`,
  `Hurewicz.SimplexGeometry.basedSimplexClass`
* `Hurewicz.SimplexGeometry.BasedSimplexBoundary`, `Hurewicz.SimplexGeometry.simplexTwoBoundary`

## Main results

* `Hurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_refl`,
  `Hurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_boundary`
* `Hurewicz.SimplexGeometry.basedSimplex_simplexChain_sum`
-/

open Set Function Topology

noncomputable section

/-! ### Coordinate minima and the simplex quotient -/

/-- The minimum of the first `k` coordinates of a cube point `u` (the infimum over
`{i | i.val < k}`). -/
def Hurewicz.SimplexGeometry.prefixMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).inf u

/-- The prefix minimum at `k = 0` is the infimum over the empty set, i.e. `1`. -/
@[simp]
theorem Hurewicz.SimplexGeometry.prefixMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    prefixMinimum u 0 = 1 := by
  simp [prefixMinimum]
  rfl

/-- The prefix minimum is antitone in `k`: longer prefixes can only lower the
minimum. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (prefixMinimum u) := by
  intro k l hkl
  apply Finset.inf_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hkl

/-- The prefix minimum at `k` is at most coordinate `i` whenever `i.val < k`. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_le_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) (i : Fin n) (hi : i.val < k) : prefixMinimum u k ≤ u i :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- The prefix minimum at `k + 1` is the minimum of the prefix minimum at `k` and
the `k`-th coordinate. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_succ {n : ℕ} (u : Fin n → (unitInterval))
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

/-- The prefix minimum is continuous on the cube. -/
theorem Hurewicz.SimplexGeometry.continuous_prefixMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => prefixMinimum u k) :=
  Continuous.finset_inf_apply (fun i _ => continuous_apply i)

/-- The extended minimum: the prefix minimum when `k ≤ n`, and `0` otherwise. -/
def Hurewicz.SimplexGeometry.extendedMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  if k ≤ n then prefixMinimum u k else 0

/-- For `k ≤ n`, the extended minimum equals the prefix minimum. -/
theorem Hurewicz.SimplexGeometry.extendedMinimum_of_le {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k ≤ n) : extendedMinimum u k = prefixMinimum u k :=
  if_pos hk

/-- The extended minimum at `k = 0` is `1`. -/
@[simp]
theorem Hurewicz.SimplexGeometry.extendedMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    extendedMinimum u 0 = 1 := by simp [extendedMinimum]

/-- The extended minimum at `n + 1` (beyond the last index) is `0`. -/
@[simp]
theorem Hurewicz.SimplexGeometry.extendedMinimum_last_succ {n : ℕ}
    (u : Fin n → (unitInterval)) : extendedMinimum u (n + 1) = 0 := by simp [extendedMinimum]

/-- The extended minimum is antitone in `k`. -/
theorem Hurewicz.SimplexGeometry.extendedMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (extendedMinimum u) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · have hk := hkl.trans hl
    simpa only [extendedMinimum, if_pos hk, if_pos hl] using prefixMinimum_antitone u hkl
  · rw [show extendedMinimum u l = 0 from if_neg hl]
    exact bot_le

/-- The extended minimum is continuous on the cube. -/
theorem Hurewicz.SimplexGeometry.continuous_extendedMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => extendedMinimum u k) := by
  by_cases hk : k ≤ n
  · simpa only [extendedMinimum, if_pos hk] using continuous_prefixMinimum n k
  · simpa only [extendedMinimum, if_neg hk] using
      (continuous_const : Continuous (fun _ : Fin n → (unitInterval) => (0 : (unitInterval))))

/-- The quotient map from the `n`-cube onto the `n`-simplex sending `u` to the
barycentric coordinates given by consecutive differences of the extended
minima of `u`. -/
def Hurewicz.SimplexGeometry.simplexQuotient (n : ℕ) :
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

/-- The `i`-th barycentric coordinate of `simplexQuotient n u` is the difference
of consecutive extended minima. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_apply {n : ℕ} (u : Fin n → (unitInterval))
    (i : Fin (n + 1)) :
    simplexQuotient n u i = (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ) :=
  rfl

/-- The `i.castSucc` barycentric coordinate of `simplexQuotient n u` is
`extendedMinimum u i - extendedMinimum u (i+1)`. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_castSucc {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) :
    simplexQuotient n u i.castSucc =
      (prefixMinimum u i.val : ℝ) - (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [simplexQuotient_apply]
  exact
    congrArg₂ (fun a b : (unitInterval) => (a : ℝ) - (b : ℝ))
      (extendedMinimum_of_le u i.val i.isLt.le) (extendedMinimum_of_le u (i.val + 1) i.isLt)

/-- The last barycentric coordinate of `simplexQuotient n u` is
`extendedMinimum u n`. -/
@[simp]
theorem Hurewicz.SimplexGeometry.simplexQuotient_last {n : ℕ} (u : Fin n → (unitInterval)) :
    simplexQuotient n u (Fin.last n) = (prefixMinimum u n : ℝ) := by
  rw [simplexQuotient_apply]
  simp only [Fin.val_last, extendedMinimum_last_succ, extendedMinimum_of_le u n le_rfl]
  exact sub_zero _

/-- If a coordinate of `u` is `0`, then `simplexQuotient n u` has a vanishing
barycentric coordinate: it lies on the simplex boundary. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_boundary_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  have hp : prefixMinimum u n = 0 :=
    le_antisymm (hi ▸ prefixMinimum_le_coordinate u n i i.isLt) bot_le
  exact ⟨Fin.last n, by rw [simplexQuotient_last, hp]; rfl⟩

/-- If a coordinate of `u` is `1`, the corresponding extended-minimum difference
vanishes and `simplexQuotient n u` lies on the simplex boundary. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_boundary_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  refine ⟨i.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

/-- The simplex quotient sends the cube boundary into the simplex boundary. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_boundary {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient n u ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact simplexQuotient_boundary_of_zero u i hi
  · exact simplexQuotient_boundary_of_one u i hi

/-- A based singular `n`-simplex at `x`: a simplex map sending the whole simplex
boundary to `x`. -/
def Hurewicz.SimplexGeometry.BasedSimplex (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(SingularChains.Simplex n, X) //
    ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n, τ s = x }

/-- The based cube map `GenLoop (Fin n) X x` obtained from a based simplex `τ` by
precomposing with the simplex quotient. -/
def Hurewicz.SimplexGeometry.basedSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp (simplexQuotient n), fun u hu => τ.property _ (simplexQuotient_boundary u hu)⟩

/-- The additive π-class `⟦basedSimplexLoop τ⟧` of a based simplex. -/
def Hurewicz.SimplexGeometry.basedSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : Additive (π_ n X x) :=
  Additive.ofMul (⟦basedSimplexLoop τ⟧ : π_ n X x)

/-- Each face of a based simplex is the constant map `x`. -/
theorem Hurewicz.SimplexGeometry.basedSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex (n + 1) x) (i : Fin (n + 2)) :
    τ.val.comp (SingularChains.simplexFace n i) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, SingularChains.simplexFace_apply_self n i s⟩

/-- The chain of the constant `n`-simplex at `x`. -/
def Hurewicz.constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X) :
    SingularChains.Chains X n :=
  SingularChains.simplexChain X n (ContinuousMap.const (SingularChains.Simplex n) x)

/-- The corrected chain of a simplex at `x`: the simplex chain minus the constant
simplex chain. -/
def Hurewicz.correctedSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : SingularChains.SingularSimplex X n) : SingularChains.Chains X n :=
  SingularChains.simplexChain X n smp - constantSimplexChain n x

/-- The `i`-th barycentric coordinate of `simplexQuotient n (cubeSimplex e s)`
computed from the tail sums of `s`. -/
theorem Hurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : Fin n → (unitInterval)) (i : Fin n) :
    (Hurewicz.CubeTriangulation.cubeSimplex e (simplexQuotient n u) (e i) : ℝ) =
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [Hurewicz.CubeTriangulation.cubeSimplex_coordinate]
  have h :=
    Hurewicz.CubeTriangulation.sum_fin_differences_tail (n + 1)
      (fun k : Fin (n + 2) => (extendedMinimum u k.val : ℝ)) i.succ
  simpa only [simplexQuotient_apply, Fin.val_castSucc, Fin.val_succ, Nat.succ_le_iff,
    Fin.val_last, extendedMinimum_last_succ, show ((0 : (unitInterval)) : ℝ) = 0 from rfl,
    sub_zero, extendedMinimum_of_le u (i.val + 1) i.isLt] using h

/-- On a point with antitone coordinates, the prefix minimum at `k` is the
`k - 1`-th coordinate. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) (i : Fin n) :
    prefixMinimum u (i.val + 1) = u i := by
  apply le_antisymm (prefixMinimum_le_coordinate u (i.val + 1) i (Nat.lt_succ_self _))
  unfold prefixMinimum
  apply Finset.le_inf
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hu (Nat.le_of_lt_succ hj)

/-- For antitone `u`, `simplexQuotient n u` recovers the consecutive coordinate
differences. -/
theorem Hurewicz.SimplexGeometry.cubeSimplex_quotient_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) :
    Hurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n)) (simplexQuotient n u) = u :=
  by
  funext i
  apply Subtype.ext
  simpa only [Equiv.refl_apply, prefixMinimum_of_antitone u hu i] using
    cubeSimplex_quotient_coordinate (Equiv.refl (Fin n)) u i

/-- The simplex quotient of the identity-permutation Kuhn cell recovers the simplex
point: `simplexQuotient n (cubeSimplex 1 s) = s`. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_refl (n : ℕ) :
    (simplexQuotient n).comp (Hurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      ContinuousMap.id (SingularChains.Simplex n) := by
  apply ContinuousMap.ext
  intro s
  apply Hurewicz.CubeTriangulation.cubeSimplex_injective (Equiv.refl (Fin n))
  exact
    cubeSimplex_quotient_of_antitone _
      (Hurewicz.CubeTriangulation.cubeSimplex_antitone (Equiv.refl (Fin n)) s)

/-- If one extended coordinate of `u` is dominated by a later one, the quotient
point lies on the simplex boundary. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_boundary_of_coordinate_le {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hu : u i ≤ u j) :
    simplexQuotient n u ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  refine ⟨j.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u j.val j.isLt]
  have hp : prefixMinimum u j.val ≤ u j := (prefixMinimum_le_coordinate u j.val i hij).trans hu
  rw [min_eq_left hp]
  exact sub_self _

/-- On a non-identity chamber, `simplexQuotient ∘ cubeSimplex e` sends `s` to a
boundary point of the simplex. -/
theorem Hurewicz.SimplexGeometry.cubeSimplex_coordinate_inversion {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : SingularChains.Simplex n) :
    ∃ i j : Fin n,
      i < j ∧
        Hurewicz.CubeTriangulation.cubeSimplex e s i ≤
          Hurewicz.CubeTriangulation.cubeSimplex e s j := by
  by_contra h
  have hu : StrictAnti (Hurewicz.CubeTriangulation.cubeSimplex e s) := by
    intro i j hij
    exact lt_of_not_ge (fun hle => h ⟨i, j, hij, hle⟩)
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (Hurewicz.CubeTriangulation.cubeSimplex_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

/-- For `e ≠ 1`, `simplexQuotient n (cubeSimplex e s)` lies on the simplex
boundary. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : SingularChains.Simplex n) :
    simplexQuotient n (Hurewicz.CubeTriangulation.cubeSimplex e s) ∈
      Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, j, hij, hu⟩ := cubeSimplex_coordinate_inversion e he s
  exact simplexQuotient_boundary_of_coordinate_le _ i j hij hu

/-- For the identity permutation, `basedSimplexLoop τ ∘ cubeSimplex 1` agrees with
`τ` up to the quotient. -/
theorem Hurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_refl {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) :
    (basedSimplexLoop τ).val.comp
        (Hurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      τ.val := by
  change (τ.val.comp (simplexQuotient n)).comp _ = _
  rw [ContinuousMap.comp_assoc, simplexQuotient_cubeSimplex_refl, ContinuousMap.comp_id]

/-- For `e ≠ 1`, `basedSimplexLoop τ ∘ cubeSimplex e` is constant at `x`, since the
quotient image lies on the simplex boundary. -/
theorem Hurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_other {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) :
    (basedSimplexLoop τ).val.comp (Hurewicz.CubeTriangulation.cubeSimplex e) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (simplexQuotient_cubeSimplex_boundary e he s)

/-- The signed sum of `τ`-pushforwards over the Kuhn cells equals
`correctedSimplexChain (n + 2) x τ.val`: the constant simplex contributions total the
negative constant chain. -/
theorem Hurewicz.SimplexGeometry.basedSimplex_simplexChain_sum {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex (n + 2) x) :
    (∑ e : Equiv.Perm (Fin (n + 2)),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain X (n + 2)
            ((basedSimplexLoop τ).val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))) =
      Hurewicz.correctedSimplexChain (n + 2) x τ.val := by
  classical
  let c := Hurewicz.constantSimplexChain (n + 2) x
  have heq (e : Equiv.Perm (Fin (n + 2))) :
    Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X (n + 2)
          ((basedSimplexLoop τ).val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) =
      (if e = Equiv.refl (Fin (n + 2)) then Hurewicz.correctedSimplexChain (n + 2) x τ.val
        else 0) +
        Hurewicz.CubeTriangulation.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin (n + 2))
    · subst e
      rw [basedSimplexLoop_cubeSimplex_refl,
        Hurewicz.CubeTriangulation.cubeOrientation_refl, one_smul, if_pos rfl, one_smul]
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
              Hurewicz.correctedSimplexChain (n + 2) x τ.val
            else 0) +
            Hurewicz.CubeTriangulation.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ =
        Hurewicz.correctedSimplexChain (n + 2) x τ.val +
          (∑ e : Equiv.Perm (Fin (n + 2)), Hurewicz.CubeTriangulation.cubeOrientation e) •
            c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin (n + 2)), Hurewicz.CubeTriangulation.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin (n + 2)),
            Hurewicz.CubeTriangulation.cubeOrientation e • c := by
        let f : ℤ →+ SingularChains.Chains X (n + 2) :=
          { toFun := fun k => k • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f Hurewicz.CubeTriangulation.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = Hurewicz.correctedSimplexChain (n + 2) x τ.val := by
      rw [Hurewicz.CubeTriangulation.cubeOrientation_sum n, zero_smul, add_zero]

/-! ### Boundary strata of the simplex quotient -/

/-- The codimension-two boundary of the simplex: points where two distinct
barycentric coordinates vanish. -/
def Hurewicz.SimplexGeometry.simplexTwoBoundary (n : ℕ) : Set (SingularChains.Simplex n) :=
  {s | ∃ i j : Fin (n + 1), i ≠ j ∧ s i = 0 ∧ s j = 0}

/-- Each face map lands in the simplex boundary (the face's `i`-th coordinate is
`0`). -/
theorem Hurewicz.SimplexGeometry.simplexFace_simplexBoundary (n : ℕ) (i : Fin (n + 2))
    (s : SingularChains.Simplex n) (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) :
    SingularChains.simplexFace n i s ∈ simplexTwoBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, SingularChains.simplexFace_apply_self n i s,
      (SingularChains.simplexFace_apply_succAbove n i s j).trans hj⟩

/-- If a coordinate `u i = 0` with `i.val < k`, the prefix minimum at `k` is `0`. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_eq_zero_of_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) (k : ℕ) (hik : i.val < k) :
    prefixMinimum u k = 0 :=
  le_antisymm (hi ▸ prefixMinimum_le_coordinate u k i hik) bot_le

/-- If some coordinate of `u` is `0`, the last barycentric coordinate of the
quotient is `0`. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_last_eq_zero_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u (Fin.last n) = 0 := by
  rw [simplexQuotient_last, prefixMinimum_eq_zero_of_coordinate u i hi n i.isLt]
  rfl

/-- If a coordinate of `u` is `1`, some `castSucc` barycentric coordinate of the
quotient is `0`. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u i.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

/-- If an earlier coordinate of `u` is `0`, a `castSucc` barycentric coordinate of
the quotient vanishes. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_earlier_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hi : u i = 0) :
    simplexQuotient n u j.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_eq_zero_of_coordinate u i hi j.val hij,
    prefixMinimum_eq_zero_of_coordinate u i hi (j.val + 1)
      ((show i.val < j.val from hij).trans_le (Nat.le_succ j.val))]
  exact sub_self _

/-- If two distinct coordinates of `u` are boundary values, the quotient point lies
on the codimension-two simplex boundary `simplexTwoBoundary`. -/
theorem Hurewicz.SimplexGeometry.simplexQuotient_codimTwo {n : ℕ}
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

/-- A boundary-based `n`-simplex at `x`: a simplex map sending the codimension-two
boundary `simplexTwoBoundary` to `x`. -/
def Hurewicz.SimplexGeometry.BasedSimplexBoundary (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(SingularChains.Simplex n, X) // ∀ s ∈ simplexTwoBoundary n, τ s = x }

/-- The `i`-th face of a boundary-based simplex, as a boundary-based simplex. -/
def Hurewicz.SimplexGeometry.basedSimplexBoundaryFace {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 2)) : BasedSimplex n x :=
  ⟨τ.val.comp (SingularChains.simplexFace n i), fun s hs =>
    τ.property _ (simplexFace_simplexBoundary n i s hs)⟩

/-- A simplex map is boundary-based if all its boundary-face values are `x`:
constructing a `BasedSimplexBoundary` from face data. -/
def Hurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : C(SingularChains.Simplex (n + 1), X))
    (h :
      ∀ i : Fin (n + 2),
        ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n,
          (τ.comp (SingularChains.simplexFace n i)) s = x) :
    Hurewicz.SimplexGeometry.BasedSimplexBoundary (n + 1) x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := Hurewicz.DegreeTwo.SimplyConnected.simplexFaceInverse n i ⟨s, hi⟩
    have ht : t ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (SingularChains.simplexFace n i t) = x at he
    rw [show SingularChains.simplexFace n i t = s from
        Hurewicz.DegreeTwo.SimplyConnected.simplexFace_inverse n i ⟨s, hi⟩] at he
    exact he⟩

/-! ### Prefix minima of `Fin.insertNth` tuples -/

/-- Below `i`'s value, `Fin.succAbove` preserves the `< k` prefix test. -/
private theorem Hurewicz.SimplexGeometry.succAbove_lt_prefix_iff {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : k ≤ i.val) : (i.succAbove j).val < k ↔ j.val < k :=
  by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_succ]
    omega

/-- At or above `i`'s value, `Fin.succAbove j < k + 1` iff `j < k`: the skip at `i` is
absorbed by the `+1`. -/
private theorem Hurewicz.SimplexGeometry.succAbove_lt_prefix_succ_iff {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : i.val ≤ k) :
    (i.succAbove j).val < k + 1 ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]

/-- The prefix minimum of an `insertNth`-extended tuple at a bounded index. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_insertNth_le {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i ε u) k = prefixMinimum u k := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_iff i _ k h, not_lt_of_ge h, false_implies, true_and]

/-- The prefix minimum of an `insertNth` tuple at a successor index. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_insertNth_succ {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i ε u) (k + 1) = Min.min ε (prefixMinimum u k) := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    le_min_iff]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_succ_iff i _ k h, Nat.lt_succ_of_le h, true_implies]

/-- The prefix minimum of an `insertNth 1` tuple is dominated by `1`. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_insertNth_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i 1 u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le i 1 u k h

/-- The prefix minimum of an `insertNth 1` tuple at a successor index equals the
original prefix minimum. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_insertNth_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i 1 u) (k + 1) = prefixMinimum u k := by
  rw [prefixMinimum_insertNth_succ i 1 u k h]
  exact min_eq_right (show prefixMinimum u k ≤ (⊤ : (unitInterval)) from le_top)

/-- The prefix minimum of an `insertNth` tuple at the last index. -/
theorem Hurewicz.SimplexGeometry.prefixMinimum_insertNth_last_le {n : ℕ}
    (u : Fin n → (unitInterval)) (ε : (unitInterval)) (k : ℕ) (hk : k ≤ n) :
    prefixMinimum (Fin.insertNth (Fin.last n) ε u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le (Fin.last n) ε u k hk
