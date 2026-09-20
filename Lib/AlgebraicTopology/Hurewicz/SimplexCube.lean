/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.Chains

/-!
# The simplex–cube dictionary

`Hurewicz.simplexCubeHomeomorph n : SingularChains.Simplex n ≃ₜ (Fin n → unitInterval)`
is a homeomorphism between the standard `n`-simplex and the unit `n`-cube, and
`Hurewicz.simplexCubeHomeomorph_boundary_iff` identifies the simplex boundary with the
cube boundary under it.

## Outline of the construction

1. The simplex is flattened to the convex flat simplex `Hurewicz.flatSimplexSet`
   (`{v : Fin n → ℝ | 0 ≤ v i, ∑ i, v i ≤ 1}`) via `Hurewicz.simplexFlatHomeomorph`.
2. Two compact convex bodies with nonempty interior in `Fin n → ℝ` are ambiently
   homeomorphic preserving frontiers, giving
   `Hurewicz.ambientSimplexCubeHomeomorph` between the flat simplex and the real cube
   `Hurewicz.realCubeSet`.
3. Composing with the real cube's homeomorphism to `Fin n → unitInterval` transports
   the result to the cube; `Hurewicz.simplexCubeHomeomorph_boundary_iff` and
   `Hurewicz.simplexCubeHomeomorph_symm_boundary_iff` carry the boundary
   identification through.

## Main definitions and results

* `Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary`, `SimplexBoundary`,
  `bottomOrSide`: the simplex boundary and the bottom-or-side part of the cylinder.
* `Hurewicz.simplexCubeHomeomorph`: the simplex–cube homeomorphism.
* `Hurewicz.simplexCubeHomeomorph_boundary_iff`: boundary correspondence.

## References

* The construction is recorded in `Lib/docs/C.md`, §§4 and 16; it feeds the
  homotopy-extension arguments for which [Allen Hatcher, *Algebraic
  Topology*][hatcher02], Proposition 0.16 is the relevant context.

## Tags

simplex, cube, homeomorphism, boundary
-/


open Set Function Filter Manifold Topology

noncomputable section

/-! ### Simplex boundaries -/

/-- The boundary of the standard `n`-simplex: the set of points where at least one
barycentric coordinate vanishes. -/
def Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (n : ℕ) : Set (SingularChains.Simplex n) :=
  {s | ∃ i : Fin (n + 1), s i = 0}

/-- The simplex boundary `simplexBoundary n` as a subtype. -/
abbrev Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n : ℕ) :=
  ↥(simplexBoundary n)

/-- The bottom-or-side part of the simplex cylinder `unitInterval × Simplex n`:
the bottom face `t = 0` together with the lateral faces over the simplex boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.bottomOrSide (n : ℕ) :
    Set (unitInterval × SingularChains.Simplex n) :=
  {u | u.1 = 0 ∨ u.2 ∈ simplexBoundary n}

/-- The simplex boundary is closed, as a finite union of closed face preimages. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.isClosed_simplexBoundary (n : ℕ) :
    IsClosed (simplexBoundary n) := by
  have h : IsClosed (⋃ i : Fin (n + 1), {s : SingularChains.Simplex n | s i = 0}) :=
    isClosed_iUnion_of_finite fun i =>
      isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  simpa only [simplexBoundary, Set.ofPred_exists] using h

/-- Every point in the image of a face inclusion `simplexFace n i` lies in the simplex
boundary (its `i`-th coordinate is `0`). -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_mem_boundary (n : ℕ) (i : Fin (n + 2))
    (s : SingularChains.Simplex n) : SingularChains.simplexFace n i s ∈ simplexBoundary (n + 1) :=
  ⟨i, SingularChains.simplexFace_apply_self n i s⟩

/-- The inclusion of the simplex as the bottom face `(0, s)` of `bottomOrSide n`. -/
def Hurewicz.DegreeTwo.SimplyConnected.bottomInclusion (n : ℕ) :
    C(SingularChains.Simplex n, ↥(bottomOrSide n))
    where
  toFun s := ⟨(0, s), Or.inl rfl⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

/-- The inclusion of `unitInterval × SimplexBoundary n` as the lateral part of
`bottomOrSide n`. -/
def Hurewicz.DegreeTwo.SimplyConnected.sideInclusion (n : ℕ) :
    C(unitInterval × SimplexBoundary n, ↥(bottomOrSide n))
    where
  toFun u := ⟨(u.1, u.2.val), Or.inr u.2.property⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-! ### Flat simplex geometry -/

/-- The flat simplex `{v : Fin n → ℝ | 0 ≤ v i, ∑ i, v i ≤ 1}` in `Fin n → ℝ`, the
image of the standard `n`-simplex after dropping its last barycentric coordinate. -/
def Hurewicz.flatSimplexSet (n : ℕ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}

/-- The real unit cube `{v : Fin n → ℝ | 0 ≤ v i ≤ 1}` in `Fin n → ℝ`. -/
def Hurewicz.realCubeSet (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc 0 1

/-- A based singular `n`-simplex in `X` at `x`: a continuous simplex map sending the
whole simplex boundary to the basepoint. -/
def Hurewicz.BasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex n, X) //
    ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n, τ s = x }

/-- The constant based simplex at `x`. -/
def Hurewicz.constantBasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :
    BasedSimplex n x :=
  ⟨ContinuousMap.const (SingularChains.Simplex n) x, fun _ _ => rfl⟩

/-- The real unit cube is convex. -/
theorem Hurewicz.convex_realCubeSet (n : ℕ) : Convex ℝ (realCubeSet n) :=
  convex_Icc 0 1

/-- The real unit cube is closed. -/
theorem Hurewicz.isClosed_realCubeSet (n : ℕ) : IsClosed (realCubeSet n) :=
  isClosed_Icc

/-- The real unit cube is compact. -/
theorem Hurewicz.isCompact_realCubeSet (n : ℕ) : IsCompact (realCubeSet n) :=
  CompactIccSpace.isCompact_Icc

/-- A point lies in the interior of the real cube iff every coordinate lies in the
open interval `(0, 1)`. -/
theorem Hurewicz.mem_interior_realCubeSet (n : ℕ) (v : Fin n → ℝ) :
    v ∈ interior (realCubeSet n) ↔ ∀ i, 0 < v i ∧ v i < 1 := by
  rw [realCubeSet, ← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ)]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, interior_Icc, Pi.zero_apply, Pi.one_apply,
    Set.mem_Ioo]

/-- The interior of the real cube is nonempty. -/
theorem Hurewicz.interior_realCubeSet_nonempty (n : ℕ) :
    (interior (realCubeSet n)).Nonempty := by
  refine ⟨fun _ => 1 / 2, (mem_interior_realCubeSet n _).mpr ?_⟩
  intro i
  norm_num

/-- A point of the real cube lies on its frontier iff some coordinate equals `0` or `1`. -/
theorem Hurewicz.realCubeSet_mem_frontier_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    v.val ∈ frontier (realCubeSet n) ↔ ∃ i, v.val i = 0 ∨ v.val i = 1 := by
  classical
  rw [frontier, (isClosed_realCubeSet n).closure_eq]
  simp only [Set.mem_sdiff, v.property, true_and, mem_interior_realCubeSet]
  constructor
  · intro h
    simp only [Classical.not_forall, not_and_or, not_lt] at h
    obtain ⟨i, h | h⟩ := h
    · exact ⟨i, Or.inl (le_antisymm h (v.property.1 i))⟩
    · exact ⟨i, Or.inr (le_antisymm (v.property.2 i) h)⟩
  · rintro ⟨i, h | h⟩ hi
    · have h0 := (hi i).1
      rw [h] at h0
      exact lt_irrefl _ h0
    · have h1 := (hi i).2
      rw [h] at h1
      exact lt_irrefl _ h1

/-- The real unit cube is homeomorphic to the product `Fin n → unitInterval` by
restricting each coordinate. -/
def Hurewicz.realCubeHomeomorph (n : ℕ) : ↥(realCubeSet n) ≃ₜ (Fin n → (unitInterval))
    where
  toFun v i := ⟨v.val i, v.property.1 i, v.property.2 i⟩
  invFun u := ⟨fun i => (u i : ℝ), fun i => (u i).property.1, fun i => (u i).property.2⟩
  left_inv v := Subtype.ext rfl
  right_inv
    u := by
    funext i
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

/-- Under `realCubeHomeomorph`, the cube boundary `Cube.boundary (Fin n)` corresponds
to the frontier of the real cube, i.e. some coordinate is `0` or `1`. -/
theorem Hurewicz.realCubeHomeomorph_mem_boundary_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    realCubeHomeomorph n v ∈ Cube.boundary (Fin n) ↔ v.val ∈ frontier (realCubeSet n) := by
  rw [realCubeSet_mem_frontier_iff]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (congrArg (fun t : (unitInterval) => (t : ℝ)) hi)⟩
    · exact ⟨i, Or.inr (congrArg (fun t : (unitInterval) => (t : ℝ)) hi)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (Subtype.ext hi)⟩
    · exact ⟨i, Or.inr (Subtype.ext hi)⟩

/-- The map flattening a simplex point to its first `n` barycentric coordinates in the
flat simplex set. -/
def Hurewicz.simplexFlat (n : ℕ) (s : SingularChains.Simplex n) : ↥(flatSimplexSet n) :=
  ⟨fun i => s i.succ, by
    refine ⟨fun i => stdSimplex.zero_le s i.succ, ?_⟩
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    have h0 := stdSimplex.zero_le s 0
    linarith⟩

/-- The inverse of `simplexFlat`: a flat-simplex point `v` is sent to the barycentric
coordinates `(v 0, …, v (n-1), 1 - ∑ i, v i)`. -/
def Hurewicz.flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) : SingularChains.Simplex n :=
  ⟨Fin.cons (1 - ∑ i, v.val i) v.val, by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr v.property.2
      · exact v.property.1 j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact sub_add_cancel 1 _⟩

/-- Flattening `simplexFlat` is continuous. -/
theorem Hurewicz.continuous_simplexFlat (n : ℕ) : Continuous (simplexFlat n) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val

/-- Unflattening `flatSimplex` is continuous. -/
theorem Hurewicz.continuous_flatSimplex (n : ℕ) : Continuous (flatSimplex n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact
      continuous_const.sub <|
        continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val
  · exact (continuous_apply j).comp continuous_subtype_val

/-- `flatSimplex` is a left inverse of `simplexFlat`. -/
@[simp]
theorem Hurewicz.flatSimplex_simplexFlat (n : ℕ) (s : SingularChains.Simplex n) :
    flatSimplex n (simplexFlat n s) = s := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 1 - ∑ j : Fin n, s j.succ = s 0
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    linarith
  · rfl

/-- `flatSimplex` is a right inverse of `simplexFlat`. -/
@[simp]
theorem Hurewicz.simplexFlat_flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) :
    simplexFlat n (flatSimplex n v) = v := by
  apply Subtype.ext
  rfl

/-- The homeomorphism between the standard `n`-simplex and the flat simplex set. -/
def Hurewicz.simplexFlatHomeomorph (n : ℕ) : SingularChains.Simplex n ≃ₜ ↥(flatSimplexSet n)
    where
  toFun := simplexFlat n
  invFun := flatSimplex n
  left_inv := flatSimplex_simplexFlat n
  right_inv := simplexFlat_flatSimplex n
  continuous_toFun := continuous_simplexFlat n
  continuous_invFun := continuous_flatSimplex n

/-- The flat simplex is convex. -/
theorem Hurewicz.convex_flatSimplexSet (n : ℕ) : Convex ℝ (flatSimplexSet n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

/-- The flat simplex is closed. -/
theorem Hurewicz.isClosed_flatSimplexSet (n : ℕ) : IsClosed (flatSimplexSet n) := by
  have he : flatSimplexSet n = (⋂ i : Fin n, {v : Fin n → ℝ | 0 ≤ v i}) ∩ {v | ∑ i, v i ≤ 1} := by
    ext v
    simp only [flatSimplexSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (by fun_prop) continuous_const)

/-- The flat simplex is contained in the real cube `Set.Icc 0 1`. -/
theorem Hurewicz.flatSimplexSet_subset_Icc (n : ℕ) :
    flatSimplexSet n ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
  intro v hv
  refine ⟨hv.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)).trans hv.2

/-- The flat simplex is compact. -/
theorem Hurewicz.isCompact_flatSimplexSet (n : ℕ) : IsCompact (flatSimplexSet n) :=
  CompactIccSpace.isCompact_Icc.of_isClosed_subset (isClosed_flatSimplexSet n)
    (flatSimplexSet_subset_Icc n)

/-- The coordinate-sum functional `v ↦ ∑ i, v i` on `Fin n → ℝ`, as a continuous linear
map. -/
private def Hurewicz.flatCoordinateSum (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ
    where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' a v := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  cont := by fun_prop

/-- The coordinate-sum functional is nonzero in dimension `n + 1` (it maps the constant-`1`
vector to `n + 1`). -/
private theorem Hurewicz.flatCoordinateSum_succ_ne_zero (n : ℕ) :
    flatCoordinateSum (n + 1) ≠ 0 := by
  intro h
  have he := congrArg (fun f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => f 1) h
  have hn : (n : ℝ) + 1 = 0 := by simpa [flatCoordinateSum] using he
  exact (ne_of_gt (Nat.cast_add_one_pos n)) hn

/-- The strict flat simplex (positive coordinates, sum `< 1`) is open in `Fin n → ℝ`. -/
private theorem Hurewicz.isOpen_flatSimplexStrict (n : ℕ) :
    IsOpen {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  have he :
    {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} =
      (⋂ i : Fin n, {v : Fin n → ℝ | 0 < v i}) ∩ {v | ∑ i, v i < 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (by fun_prop) continuous_const)

/-- The interior of the flat simplex is the set of points with all coordinates
strictly positive and coordinate sum strictly less than `1`. -/
theorem Hurewicz.interior_flatSimplexSet (n : ℕ) :
    interior (flatSimplexSet n) = {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  apply Set.Subset.antisymm
  · intro v hv
    constructor
    · intro i
      have hi : v ∈ interior ((fun w : Fin n → ℝ => w i) ⁻¹' Set.Ici 0) :=
        interior_mono (fun w hw => hw.1 i) hv
      have h := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa only [Set.mem_preimage, interior_Ici, Set.mem_Ioi] using h
    · cases n with
      | zero => simp
      | succ
        n =>
        have hs : v ∈ interior (flatCoordinateSum (n + 1) ⁻¹' Set.Iic 1) :=
          interior_mono (fun w hw => hw.2) hv
        have h :=
          ((flatCoordinateSum (n + 1)).isOpenMap_of_ne_zero
                (flatCoordinateSum_succ_ne_zero
                  n)).interior_preimage_subset_preimage_interior
            hs
        simpa only [Set.mem_preimage, interior_Iic, Set.mem_Iio, flatCoordinateSum,
          ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using h
  · exact
      (isOpen_flatSimplexStrict n).subset_interior_iff.mpr
        (fun _ hv => ⟨fun i => (hv.1 i).le, hv.2.le⟩)

/-- The interior of the flat simplex is nonempty. -/
theorem Hurewicz.interior_flatSimplexSet_nonempty (n : ℕ) :
    (interior (flatSimplexSet n)).Nonempty := by
  rw [interior_flatSimplexSet]
  have hn : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), fun _ => one_div_pos.mpr hn, ?_⟩
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one_div] using (div_lt_one hn).mpr (lt_add_one (n : ℝ))

/-- A simplex point maps to the interior of the flat simplex iff all its barycentric
coordinates are strictly positive. -/
theorem Hurewicz.simplexFlatHomeomorph_mem_interior_iff (n : ℕ)
    (s : SingularChains.Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ interior (flatSimplexSet n) ↔ ∀ i, 0 < s i := by
  rw [interior_flatSimplexSet]
  change ((∀ i : Fin n, 0 < s i.succ) ∧ ∑ i : Fin n, s i.succ < 1) ↔ _
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨hpos, hsum⟩ i
    refine Fin.cases ?_ (fun j => hpos j) i
    linarith
  · intro hpos
    exact ⟨fun i => hpos i.succ, by linarith [hpos 0]⟩

/-- A simplex point maps to the frontier of the flat simplex iff some barycentric
coordinate vanishes, i.e. iff it lies on the simplex boundary. -/
theorem Hurewicz.simplexFlatHomeomorph_mem_frontier_iff (n : ℕ)
    (s : SingularChains.Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ frontier (flatSimplexSet n) ↔
      s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  rw [frontier, (isClosed_flatSimplexSet n).closure_eq]
  change (_ ∧ _) ↔ ∃ i : Fin (n + 1), s i = 0
  rw [simplexFlatHomeomorph_mem_interior_iff]
  constructor
  · rintro ⟨_, hnot⟩
    classical
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, le_antisymm hi (stdSimplex.zero_le s i)⟩
  · rintro ⟨i, hi⟩
    refine ⟨(simplexFlatHomeomorph n s).property, ?_⟩
    intro hpos
    have := hpos i
    rw [hi] at this
    exact (lt_irrefl 0) this

/-! ### Convex-body homeomorphism -/

/-- There exists a self-homeomorphism of `Fin n → ℝ` sending the flat simplex onto the
real cube and its frontier onto the cube's frontier, by the comparison of compact
convex bodies with nonempty interior. -/
theorem Hurewicz.exists_ambientSimplexCubeHomeomorph (n : ℕ) :
    ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      e '' flatSimplexSet n = realCubeSet n ∧
        e '' frontier (flatSimplexSet n) = frontier (realCubeSet n) := by
  obtain ⟨e, _, hclosed, hfrontier⟩ :=
    exists_homeomorph_image_eq (convex_flatSimplexSet n) (interior_flatSimplexSet_nonempty n)
      ((isCompact_flatSimplexSet n).isVonNBounded ℝ) (convex_realCubeSet n)
      (interior_realCubeSet_nonempty n) ((isCompact_realCubeSet n).isVonNBounded ℝ)
  refine ⟨e, ?_, hfrontier⟩
  simpa only [(isClosed_flatSimplexSet n).closure_eq, (isClosed_realCubeSet n).closure_eq] using
    hclosed

/-- A chosen ambient homeomorphism of `Fin n → ℝ` mapping the flat simplex onto the real
cube frontier-preservingly, provided by `exists_ambientSimplexCubeHomeomorph`. -/
def Hurewicz.ambientSimplexCubeHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_ambientSimplexCubeHomeomorph n)

/-- The ambient homeomorphism maps the flat simplex onto the real cube. -/
theorem Hurewicz.ambientSimplexCubeHomeomorph_image (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' flatSimplexSet n = realCubeSet n :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).1

/-- The ambient homeomorphism maps the flat simplex's frontier onto the real cube's
frontier. -/
theorem Hurewicz.ambientSimplexCubeHomeomorph_image_frontier (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' frontier (flatSimplexSet n) = frontier (realCubeSet n) :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).2

/-- A point lies in the flat simplex iff its image under the ambient homeomorphism lies
in the real cube. -/
theorem Hurewicz.ambientSimplexCubeHomeomorph_mem_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ flatSimplexSet n ↔ ambientSimplexCubeHomeomorph n v ∈ realCubeSet n := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

/-- A point lies on the flat simplex's frontier iff its image under the ambient
homeomorphism lies on the real cube's frontier. -/
theorem Hurewicz.ambientSimplexCubeHomeomorph_mem_frontier_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ frontier (flatSimplexSet n) ↔
      ambientSimplexCubeHomeomorph n v ∈ frontier (realCubeSet n) := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

/-- The homeomorphism between the flat simplex and the real cube obtained by
restricting the ambient homeomorphism. -/
def Hurewicz.flatCubeHomeomorph (n : ℕ) : ↥(flatSimplexSet n) ≃ₜ ↥(realCubeSet n) :=
  (ambientSimplexCubeHomeomorph n).subtype (ambientSimplexCubeHomeomorph_mem_iff n)

/-- The homeomorphism between the standard `n`-simplex and the unit `n`-cube
`Fin n → unitInterval`, composite of the flattening and convex-body homeomorphisms. -/
def Hurewicz.simplexCubeHomeomorph (n : ℕ) :
    SingularChains.Simplex n ≃ₜ (Fin n → (unitInterval)) :=
  (simplexFlatHomeomorph n).trans ((flatCubeHomeomorph n).trans (realCubeHomeomorph n))

/-! ### Boundary transport -/

/-- A simplex point maps to the cube boundary iff it lies on the simplex boundary:
the homeomorphism identifies the two boundaries. -/
theorem Hurewicz.simplexCubeHomeomorph_boundary_iff (n : ℕ) (s : SingularChains.Simplex n) :
    simplexCubeHomeomorph n s ∈ Cube.boundary (Fin n) ↔
      s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  change
    realCubeHomeomorph n (flatCubeHomeomorph n (simplexFlatHomeomorph n s)) ∈
        Cube.boundary (Fin n) ↔
      _
  rw [realCubeHomeomorph_mem_boundary_iff]
  change
    ambientSimplexCubeHomeomorph n (simplexFlatHomeomorph n s).val ∈ frontier (realCubeSet n) ↔ _
  rw [← ambientSimplexCubeHomeomorph_mem_frontier_iff, simplexFlatHomeomorph_mem_frontier_iff]

/-- A cube point maps under the inverse homeomorphism to the simplex boundary iff it
lies on the cube boundary. -/
theorem Hurewicz.simplexCubeHomeomorph_symm_boundary_iff (n : ℕ)
    (u : Fin n → (unitInterval)) :
    (simplexCubeHomeomorph n).symm u ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n ↔
      u ∈ Cube.boundary (Fin n) := by
  rw [← simplexCubeHomeomorph_boundary_iff, Homeomorph.apply_symm_apply]


