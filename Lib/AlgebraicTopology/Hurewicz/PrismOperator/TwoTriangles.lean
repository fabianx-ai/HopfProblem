/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
/-!
# The two-triangle decomposition of the square chain

The product `2`-chain of `I × I` is the signed sum of the two affine triangles below and above
the diagonal and two degenerate triangles (`productSquareChain_four_triangles`).  For a based
square `p` the degenerate terms are constant simplices at the basepoint, so
`squareChain p = p ∘ lowerSquareTriangle - p ∘ upperSquareTriangle`
(`squareChain_two_triangles`).  For the square of a based triangle `τ` the upper triangle is
constant and the lower one is `τ` itself (`squareChain_basedTriangleLoop`).  This identifies
the Hurewicz image of a based triangle with the class of `τ - const` in singular homology.

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle`, `lowerProductTriangle`,
  `upperProductTriangle`, `lowerSquareTriangle`, `upperSquareTriangle`.
* `Hurewicz.DegreeTwo.SimplyConnected.productSquareChain_four_triangles`,
  `squareChain_two_triangles`, `squareChain_basedTriangleLoop`.
-/

open Set Function Topology

noncomputable section

/-! ### The two-triangle decomposition of the square -/

/-- The affine `2`-simplex into `I × I` with vertices `v : Fin 3 → Fin 2 × Fin 2`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  ((SingularChains.pathSimplex Path.id).prodMap (SingularChains.pathSimplex Path.id)).comp
    (SingularHomology.productAffineSimplex
      (fun i =>
        (SingularMayerVietoris.stdVertices 1 (v i).1,
          SingularMayerVietoris.stdVertices 1 (v i).2)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The first coordinate of `squareAffineTriangle v` is `∑ i, s i * stdVertices 1 (v i).1 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).1 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).1) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The second coordinate of `squareAffineTriangle v` is `∑ i, s i * stdVertices 1 (v i).2 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).2 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).2) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The lower product triangle in `I × I`. -/
def Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The upper product triangle in `I × I`. -/
def Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degenerate left edge of the product square. -/
def Hurewicz.DegreeTwo.SimplyConnected.leftProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degenerate bottom edge of the product square. -/
def Hurewicz.DegreeTwo.SimplyConnected.bottomProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `lowerProductTriangle` is `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `lowerProductTriangle` is `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `upperProductTriangle` is `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `upperProductTriangle` is `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `leftProductDegenerate` is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.leftProductDegenerate_fst (s : SingularChains.Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `bottomProductDegenerate` is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.bottomProductDegenerate_snd (s : SingularChains.Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The lower triangle of the square's diagonal subdivision, as a singular
`2`-simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp lowerProductTriangle

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The upper triangle of the square's diagonal subdivision, as a singular
`2`-simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp upperProductTriangle

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `lowerSquareTriangle s` has coordinate `0` equal to `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by simp [lowerSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `lowerSquareTriangle s` has coordinate `1` equal to `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_one (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by simp [lowerSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `upperSquareTriangle s` has coordinate `0` equal to `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by simp [upperSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `upperSquareTriangle s` has coordinate `1` equal to `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_one (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by simp [upperSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `productSquareChain` decomposes as a sum of four signed triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.productSquareChain_four_triangles :
    Hurewicz.DegreeTwo.productSquareChain =
      SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
            SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle +
        SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 bottomProductDegenerate := by
  rw [Hurewicz.DegreeTwo.productSquareChain, Hurewicz.DegreeTwo.intervalChain, SingularChains.pathChain,
    SingularHomology.crossProductEdge_simplex,
    SingularHomology.formalEdgeCrossProduct_simplex_succ,
    SingularHomology.formalPointCrossProduct_edge_boundary,
    SingularHomology.formalBoundary_edge_simplex]
  simp only [map_sub, SingularHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    SingularHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex]
  change
    (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate) -
        (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2
            bottomProductDegenerate) =
      _
  abel

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `squareMap p ∘ leftProductDegenerate` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareMap_leftProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (Hurewicz.DegreeTwo.squareMap p).comp leftProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [Hurewicz.DegreeTwo.squareCoordinates_zero, leftProductDegenerate_fst]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `squareMap p ∘ bottomProductDegenerate` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareMap_bottomProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (Hurewicz.DegreeTwo.squareMap p).comp bottomProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [Hurewicz.DegreeTwo.squareCoordinates_one, bottomProductDegenerate_snd]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The square chain equals the signed sum of the two square triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareChain_two_triangles {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    Hurewicz.DegreeTwo.squareChain p =
      SingularChains.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
        SingularChains.simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [Hurewicz.DegreeTwo.squareChain, Hurewicz.DegreeTwo.suspensionOne_toLoop,
    productSquareChain_four_triangles]
  simp only [map_add, map_sub, SingularChains.inducedChain_simplex,
    squareMap_leftProductDegenerate, squareMap_bottomProductDegenerate]
  change
    (SingularChains.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x)) -
          SingularChains.simplexChain X 2 (p.val.comp upperSquareTriangle) +
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) =
      _
  abel

/-- `triangleQuotient ∘ lowerProductTriangle = id`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_lowerProductTriangle :
    triangleQuotient.comp lowerProductTriangle = ContinuousMap.id (SingularChains.Simplex 2) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + s 2) = 1 at hs
  have hle : s 2 ≤ s 1 + s 2 := le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  fin_cases i
  · change 1 - ((lowerProductTriangle s).1 : ℝ) = s 0
    rw [lowerProductTriangle_fst]
    linarith
  · change
      ((lowerProductTriangle s).1 : ℝ) -
          Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) =
        s 1
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]
    ring
  · change Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) = s 2
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]

/-- The triangle quotient of the upper product triangle lands on the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_upperProductTriangle_boundary
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

/-- The lower triangle of `basedTriangleLoop τ` under the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) : (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (Hurewicz.DegreeTwo.squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

/-- The upper triangle of `basedTriangleLoop τ` under the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  change (Hurewicz.DegreeTwo.squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

/-- The square chain of `basedTriangleLoop τ` expressed via the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareChain_basedTriangleLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTriangle x) :
    Hurewicz.DegreeTwo.squareChain (basedTriangleLoop τ) =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]
