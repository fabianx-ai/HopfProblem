/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Subdividing a based square along its diagonal

For a based square `p : GenLoop (Fin 2) X x` that is constant on the diagonal, the two
triangles cut out by the diagonal are again based squares after reparametrization
(`subdivisionLowerTriangleLoop`, `subdivisionUpperTriangleLoop`), and `p` is homotopic rel
boundary to their concatenation in the second coordinate (`subdivision_homotopic`).  Hence
`⟦p⟧ = ⟦lower⟧ * ⟦upper⟧` in `π_2` (`subdivision_class`, additive form
`subdivision_additiveClass`).  This is the subdivision argument used in the proof of the
Hurewicz theorem to split the class of a square into the classes of its two triangles
(Hatcher, Thm 4.32, proof).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.SubdivisionSameSide`, `subdivisionLinearHomotopy`: linear
  homotopies between pullbacks along maps of the square that agree side by side.
* `Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleMap`,
  `subdivisionUpperTriangleMap`, `subdivisionWarpMap`: the reparametrizations.
* `Hurewicz.DegreeTwo.SimplyConnected.subdivision_homotopic`, `subdivision_class`,
  `subdivision_additiveClass`.
-/

open Set Function Topology

noncomputable section

/-! ### Subdivision of the square -/

/-- The subdivision square `Fin 2 → unitInterval`. -/
abbrev Hurewicz.DegreeTwo.SimplyConnected.SubdivisionSquare :=
  Fin 2 → (unitInterval)

/-- A boundary point of the subdivision square has some coordinate equal to `0` or `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

/-- Two square points share a `0`-coordinate, a `1`-coordinate, or lie on the diagonal. -/
inductive Hurewicz.DegreeTwo.SimplyConnected.SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

/-- The blend between subdivision square points. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend (t : (unitInterval))
    (a b : SubdivisionSquare) : SubdivisionSquare := fun i => Set.Icc.convexComb (a i) (b i) t

/-- At `t = 0` the subdivision blend is the first point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

/-- At `t = 1` the subdivision blend is the second point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

/-- The blend of two subdivision maps as a continuous map. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlendMap
    (f g : C(SubdivisionSquare, SubdivisionSquare)) :
    C((unitInterval) × SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := subdivisionBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

/-- A point on the subdivision diagonal. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionOnDiagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (a : SubdivisionSquare) (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

/-- For same-side maps, the blend stays based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    {a b : SubdivisionSquare} (h : SubdivisionSameSide a b) (t : (unitInterval)) :
    p (subdivisionBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
    apply p.property
    exact ⟨i, Or.inl (by simp [subdivisionBlend, ha, hb])⟩
  | one i ha hb =>
    apply p.property
    exact ⟨i, Or.inr (by simp [subdivisionBlend, ha, hb])⟩
  | diagonal ha hb =>
    apply subdivisionOnDiagonal p hd
    simp only [subdivisionBlend, ha, hb]

/-- The pullback of a based square along a subdivision map. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionPullbackLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

/-- The linear homotopy between subdivision pullbacks along same-side maps. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLinearHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (f g : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 2), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 2), SubdivisionSameSide (f u) (g u)) :
    (subdivisionPullbackLoop p f hf).val.HomotopyRel (subdivisionPullbackLoop p g hg).val
      (Cube.boundary (Fin 2))
    where
  toFun u := p (subdivisionBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (subdivisionBlendMap f g).continuous
  map_zero_left
    u := by
    change p (subdivisionBlend 0 (f u) (g u)) = p (f u)
    rw [subdivisionBlend_zero]
  map_one_left
    u := by
    change p (subdivisionBlend 1 (f u) (g u)) = p (g u)
    rw [subdivisionBlend_one]
  prop' t u hu := (subdivisionBlend_based p hd (hfg u hu) t).trans (hf u hu).symm

/-- `u - min (u, v)` as a point of the unit interval. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin (u v : (unitInterval)) : (unitInterval) :=
  ⟨(u : ℝ) - Min.min (u : ℝ) (v : ℝ), sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

/-- `subdivisionSubMin 0 v = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_zero_left (v : (unitInterval)) :
    subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

/-- `subdivisionSubMin u 0 = u`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_zero_right (u : (unitInterval)) :
    subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

/-- `subdivisionSubMin 1 v = 1 - v`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_one_left (v : (unitInterval)) :
    subdivisionSubMin 1 v = (unitInterval.symm) v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

/-- `subdivisionSubMin u 1 = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_one_right (u : (unitInterval)) :
    subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

/-- The product map onto the lower triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, u 0 * u 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => u 0 * u 1
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp (continuous_apply 0)).mul
          (continuous_subtype_val.comp (continuous_apply 1))

/-- The product map onto the upper triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

/-- The cone map onto the upper triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0 * (unitInterval.symm) (u 1), Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => u 0 * (unitInterval.symm) (u 1)
      apply Continuous.subtype_mk
      change Continuous fun u : SubdivisionSquare => (u 0 : ℝ) * (1 - (u 1 : ℝ))
      fun_prop
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

/-- The map `u ↦ ![u 0, min (u 0) (u 1)]` onto the lower triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Min.min (u 0) (u 1)]
  continuous_toFun := by fun_prop

/-- The map from the subdivision square onto the upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![subdivisionSubMin (u 0) (u 1), u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => subdivisionSubMin (u 0) (u 1)
      unfold subdivisionSubMin
      fun_prop
    · exact continuous_apply 0

/-- `p (subdivisionLowerProductMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

/-- `p (subdivisionUpperProductMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

/-- `p (subdivisionUpperConeMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

/-- `p (subdivisionLowerTriangleMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- `p (subdivisionUpperTriangleMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

/-- The pullback loop `p ∘ subdivisionLowerProductMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperProductMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperConeMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

/-- The pullback loop `p ∘ subdivisionLowerTriangleMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperTriangleMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

/-- The side restrictions of the lower product triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductTriangle_sides
    (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionLowerProductMap u) (subdivisionLowerTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .one 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .zero 1 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionLowerProductMap, h])
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- The side restrictions of the upper product/cone maps. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])

/-- The side restrictions of the upper cone and triangle maps. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperConeMap u) (subdivisionUpperTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact .one 1 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])

/-- The `HomotopyRel` between the lower product and lower triangle loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel (subdivisionLowerTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

/-- The `HomotopyRel` between the upper product and upper cone loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel (subdivisionUpperConeLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

/-- The `HomotopyRel` between the upper cone and upper triangle loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel (subdivisionUpperTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

/-- `toLoop` of a `transAt` concatenation is the `trans` of the `toLoop`s. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_toLoop_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- `transAt` respects homotopy in both arguments. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_transAt_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin 2) {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

/-- The warp coordinate interpolating between two subdivision maps. -/
noncomputable def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate :
    C((unitInterval) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

/-- `subdivisionWarpCoordinate (u, v)` is the `u`-blend between `2v - 1` and `2v` clamped to `I`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_apply (u v : (unitInterval)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
        (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u :=
  rfl

/-- `subdivisionWarpCoordinate (u, 0) = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_zero (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- `subdivisionWarpCoordinate (u, 1) = 1`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_one (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- For `v ≤ 1/2`, `subdivisionWarpCoordinate (u, v) = u * (2v)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_le_half (u v : (unitInterval))
    (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) = u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

/-- For `v ≥ 1/2`, `subdivisionWarpCoordinate` blends `u` toward `1` with parameter `2v - 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_half_le (u v : (unitInterval))
    (hv : 1 / 2 ≤ (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hone]
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  change (1 - (u : ℝ)) * _ + (u : ℝ) * 1 = (1 - _) * (u : ℝ) + _ * 1
  ring

/-- For `v > 1/2`, `subdivisionWarpCoordinate` blends `u` toward `1` with parameter `2v - 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (u v : (unitInterval))
    (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

/-- The warp map `u ↦ ![u 0, subdivisionWarpCoordinate (u 0, u 1)]`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, subdivisionWarpCoordinate (u 0, u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => subdivisionWarpCoordinate (u 0, u 1)
      exact
        subdivisionWarpCoordinate.continuous.comp
          (show Continuous (fun u : SubdivisionSquare => (u 0, u 1)) from
            (continuous_apply 0).prodMk (continuous_apply 1))

/-- Each boundary point is on the same side as its warp-map image. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

/-- `p (subdivisionWarpMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

/-- The pullback loop `p ∘ subdivisionWarpMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

/-- The `HomotopyRel` from `p` to `subdivisionWarpLoop p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap p.property
    (subdivisionWarpMap_based p) subdivisionWarpMap_sides

/-- The warp loop is the `transAt 1` concatenation of the lower and upper product loops. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpLoop_eq_transAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionWarpLoop p =
      GenLoop.transAt (1 : Fin 2) (subdivisionLowerProductLoop p hd)
        (subdivisionUpperProductLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, subdivisionWarpCoordinate (u 0, u 1)] =
      if (u 1 : ℝ) ≤ 1 / 2 then
        subdivisionLowerProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ))))
      else
        subdivisionUpperProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ) - 1)))
  split_ifs with h
  · simpa [subdivisionLowerProductLoop, subdivisionPullbackLoop, subdivisionLowerProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_le_half (u 0) (u 1) h)
  · simpa [subdivisionUpperProductLoop, subdivisionPullbackLoop, subdivisionUpperProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_half_lt (u 0) (u 1) (lt_of_not_ge h))

/-- `p` is homotopic to the `transAt 1` concatenation of its lower and upper triangle loops. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
        (subdivisionUpperTriangleLoop p hd)) := by
  have hw : GenLoop.Homotopic p (subdivisionWarpLoop p) := ⟨subdivisionWarpHomotopy p hd⟩
  rw [subdivisionWarpLoop_eq_transAt p hd] at hw
  apply hw.trans
  apply subdivision_transAt_homotopic
  · exact ⟨subdivisionLowerTriangleHomotopy p hd⟩
  · exact ⟨(subdivisionUpperConeHomotopy p hd).trans (subdivisionUpperTriangleHomotopy p hd)⟩

/-- `⟦p⟧ = ⟦subdivisionLowerTriangleLoop⟧ * ⟦subdivisionUpperTriangleLoop⟧` in `π_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦p⟧ : π_ 2 X x) =
      ((· * ·) : π_ 2 X x → π_ 2 X x → π_ 2 X x) ⟦subdivisionLowerTriangleLoop p hd⟧
        ⟦subdivisionUpperTriangleLoop p hd⟧ := by
  have h :
    (⟦p⟧ : π_ 2 X x) =
      (⟦GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
            (subdivisionUpperTriangleLoop p hd)⟧ :
        π_ 2 X x) :=
    Quotient.sound (subdivision_homotopic p hd)
  exact
    h.trans
      ((HomotopyGroup.mul_spec (i := (1 : Fin 2)) (p := subdivisionUpperTriangleLoop p hd) (q :=
            subdivisionLowerTriangleLoop p hd)).symm.trans
        (mul_comm _ _))

/-- The additive form of `subdivision_class`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)
