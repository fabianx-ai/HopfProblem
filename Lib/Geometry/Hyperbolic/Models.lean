module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Basic

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order.OrderClosed

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Lib.LinearAlgebra.BilinearForm.Reflection
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Lib.Geometry.Manifold.Riemannian.CurveTransport
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Logic.Equiv.Fin.Basic
public import Lib.Analysis.Calculus.CurveVariation
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences
public import Mathlib.Order.WellFounded
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Constructions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Connected.PathConnected

/-!
# Upper-half-plane and hyperboloid coordinates

The rational map `(x,y) ↦ (x/y,(x²+y²-1)/(2y),(x²+y²+1)/(2y))`
identifies the open upper half-plane with the positive sheet of
`X²+Y²-T²=-1`. Its literal inverse is `(X/(T-Y),1/(T-Y))`.
We prove the domain inequalities, both auxiliary coordinates `T-Y` and
`T+Y`, and both inverse identities before packaging the same maps as an
equivalence. The subsequent real smooth-coordinate section identifies the
actual ambient tangent image with the Lorentz perpendicular kernel, with
the literal inverse differential. The displayed auxiliary-coordinate calculation
then gives the Lorentz tensor identity, positivity on all actual tangent fibers,
and smooth intrinsic tensor sections. Angle, curve-length and distance
preservation remain separate later results and are not asserted here.

Textbook source: the reviewed ideal-reflection model bridge, section 2,
coordinate formulas and inverse (G01.a/b/c, canonical lines 82–89).
-/

@[expose] public section
noncomputable section
namespace Hyperbolic

/-- The positive sheet of the Lorentz hyperboloid, with coordinates ordered `X,Y,T`. -/
abbrev Hyperboloid : Type :=
  {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 - p 2 ^ 2 = -1 ∧ 0 < p 2}

/-- The ambient rational formula for upper-half-plane to hyperboloid coordinates. -/
def upperHalfPlaneToHyperboloidCoords (z : ℂ) : Fin 3 → ℝ :=
  ![z.re / z.im,
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im),
    (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)]

/-- The literal inverse rational coordinates; on the positive sheet its height is positive. -/
def hyperboloidToUpperHalfPlaneCoords (p : Fin 3 → ℝ) : ℂ :=
  ⟨p 0 / (p 2 - p 1), 1 / (p 2 - p 1)⟩

/-- A point of positive height maps to the hyperboloid equation and the positive sheet. -/
theorem upperHalfPlaneToHyperboloidCoords_mem (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 0 ^ 2 +
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 ^ 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 ^ 2 = -1 ∧
    0 < (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 := by
  change (z.re / z.im) ^ 2 + ((z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im)) ^ 2 -
    ((z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)) ^ 2 = -1 ∧
    0 < (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)
  constructor
  · field_simp [z.im_ne_zero]
    <;> ring
  · exact div_pos (by nlinarith [sq_nonneg z.re, sq_nonneg z.im])
      (mul_pos (by norm_num) z.im_pos)

/-- The auxiliary null coordinate `T-Y` is the reciprocal of the original height. -/
theorem upperHalfPlaneToHyperboloidCoords_sub (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 = 1 / z.im := by
  change (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) -
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im) = 1 / z.im
  field_simp [z.im_ne_zero]
  <;> ring

/-- The other auxiliary coordinate `T+Y` is `(x²+y²)/y`. -/
theorem upperHalfPlaneToHyperboloidCoords_add (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 +
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 =
      (z.re ^ 2 + z.im ^ 2) / z.im := by
  change (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) +
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im) = (z.re ^ 2 + z.im ^ 2) / z.im
  field_simp [z.im_ne_zero]
  <;> ring

/-- The hyperboloid equation and positive sheet imply `|Y|<T`. -/
theorem hyperboloid_abs_y_lt_t (p : Hyperboloid) : |p.val 1| < p.val 2 := by
  apply abs_lt_of_sq_lt_sq ?_ p.property.2.le
  nlinarith [p.property.1, sq_nonneg (p.val 0)]

/-- The denominator of the literal inverse is strictly positive on the upper sheet. -/
theorem hyperboloid_denominator_pos (p : Hyperboloid) : 0 < p.val 2 - p.val 1 := by
  exact sub_pos.mpr ((le_abs_self (p.val 1)).trans_lt (hyperboloid_abs_y_lt_t p))

/-- The literal inverse coordinates have positive imaginary part. -/
theorem hyperboloidToUpperHalfPlaneCoords_im_pos (p : Hyperboloid) :
    0 < (hyperboloidToUpperHalfPlaneCoords p.val).im := by
  exact div_pos (by norm_num) (hyperboloid_denominator_pos p)

/-- Substitution of `T-Y=1/y` recovers both coordinates of every upper-half-plane point. -/
theorem hyperboloidCoords_left_inv (z : UpperHalfPlane) :
    hyperboloidToUpperHalfPlaneCoords
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) = (z : ℂ) := by
  apply Complex.ext
  · change (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 0 /
      ((upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
       (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1) = z.re
    rw [upperHalfPlaneToHyperboloidCoords_sub]
    change (z.re / z.im) / (1 / z.im) = z.re
    field_simp [z.im_ne_zero]
  · change 1 / ((upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1) = z.im
    rw [upperHalfPlaneToHyperboloidCoords_sub]
    simp

/-- Substitution of the inverse recovers all three coordinates on the entire positive sheet. -/
theorem hyperboloidCoords_right_inv (p : Hyperboloid) :
    upperHalfPlaneToHyperboloidCoords
      (hyperboloidToUpperHalfPlaneCoords p.val) = p.val := by
  have hd : p.val 2 - p.val 1 ≠ 0 := ne_of_gt (hyperboloid_denominator_pos p)
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · change (p.val 0 / (p.val 2 - p.val 1)) / (1 / (p.val 2 - p.val 1)) = p.val 0
    field_simp [hd]
  · change ((p.val 0 / (p.val 2 - p.val 1)) ^ 2 +
      (1 / (p.val 2 - p.val 1)) ^ 2 - 1) /
      (2 * (1 / (p.val 2 - p.val 1))) = p.val 1
    field_simp [hd]
    nlinarith [p.property.1]
  · change ((p.val 0 / (p.val 2 - p.val 1)) ^ 2 +
      (1 / (p.val 2 - p.val 1)) ^ 2 + 1) /
      (2 * (1 / (p.val 2 - p.val 1))) = p.val 2
    field_simp [hd]
    nlinarith [p.property.1]

/-- The rational forward map with its proved positive-sheet membership. -/
def toHyperboloid (z : UpperHalfPlane) : Hyperboloid :=
  ⟨upperHalfPlaneToHyperboloidCoords (z : ℂ),
    upperHalfPlaneToHyperboloidCoords_mem z⟩

/-- The literal rational inverse, with its proved positive imaginary part. -/
def fromHyperboloid (p : Hyperboloid) : UpperHalfPlane :=
  ⟨hyperboloidToUpperHalfPlaneCoords p.val,
    hyperboloidToUpperHalfPlaneCoords_im_pos p⟩

/-- The underlying forward coordinates are exactly the displayed ambient formula. -/
theorem toHyperboloid_val (z : UpperHalfPlane) :
    (toHyperboloid z).val = upperHalfPlaneToHyperboloidCoords (z : ℂ) := rfl

/-- The underlying inverse coordinates are exactly the displayed ambient formula. -/
theorem fromHyperboloid_coe (p : Hyperboloid) :
    (fromHyperboloid p : ℂ) = hyperboloidToUpperHalfPlaneCoords p.val := rfl

/-- The actual-domain inverse after the forward map is identity. -/
theorem fromHyperboloid_toHyperboloid (z : UpperHalfPlane) :
    fromHyperboloid (toHyperboloid z) = z :=
  UpperHalfPlane.coe_injective (hyperboloidCoords_left_inv z)

/-- The actual-domain forward map after the inverse is identity. -/
theorem toHyperboloid_fromHyperboloid (p : Hyperboloid) :
    toHyperboloid (fromHyperboloid p) = p :=
  Subtype.ext (hyperboloidCoords_right_inv p)

/-- The explicit coordinate equivalence between the upper half-plane and the positive hyperboloid. -/
def upperHalfPlaneEquivHyperboloid : UpperHalfPlane ≃ Hyperboloid where
  toFun := toHyperboloid
  invFun := fromHyperboloid
  left_inv := fromHyperboloid_toHyperboloid
  right_inv := toHyperboloid_fromHyperboloid

/-- The equivalence uses the literal forward coordinate map. -/
theorem upperHalfPlaneEquivHyperboloid_apply (z : UpperHalfPlane) :
    upperHalfPlaneEquivHyperboloid z = toHyperboloid z := rfl

/-- The inverse equivalence uses the literal backward coordinate map. -/
theorem upperHalfPlaneEquivHyperboloid_symm_apply (p : Hyperboloid) :
    upperHalfPlaneEquivHyperboloid.symm p = fromHyperboloid p := rfl

open scoped Manifold ContDiff Topology
local notation "V" => (Fin 3 → ℝ)
local notation "F" => upperHalfPlaneToHyperboloidCoords
local notation "B" => hyperboloidToUpperHalfPlaneCoords
local notation "I" => 𝓘(ℝ, ℂ)
local notation "J" => 𝓘(ℝ, V)

/-- The displayed forward coordinates are real smooth on positive height (G01.d). -/
theorem contDiffOn_upperHalfPlaneToHyperboloidCoords :
    ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im} := by
  apply contDiffOn_pi.mpr
  intro i
  have hr : ContDiffOn ℝ ∞ Complex.re {z : ℂ | 0 < z.im} := Complex.reCLM.contDiff.contDiffOn
  have hi : ContDiffOn ℝ ∞ Complex.im {z : ℂ | 0 < z.im} := Complex.imCLM.contDiff.contDiffOn
  have hn : ∀ z ∈ {z : ℂ | 0 < z.im}, z.im ≠ 0 := fun z hz => ne_of_gt hz
  have h2 : ∀ z ∈ {z : ℂ | 0 < z.im}, 2 * z.im ≠ 0 :=
    fun z hz => mul_ne_zero (by norm_num) (hn z hz)
  fin_cases i
  · exact hr.div hi hn
  · exact ((hr.pow 2).add (hi.pow 2) |>.sub contDiffOn_const).div
      (contDiffOn_const.mul hi) h2
  · exact ((hr.pow 2).add (hi.pow 2) |>.add contDiffOn_const).div
      (contDiffOn_const.mul hi) h2

/-- The displayed inverse coordinates are real smooth where their denominator is positive (G01.d). -/
theorem contDiffOn_hyperboloidToUpperHalfPlaneCoords :
    ContDiffOn ℝ ∞ B {p : V | 0 < p 2 - p 1} := by
  have hp (i : Fin 3) : ContDiffOn ℝ ∞ (fun p : V => p i) {p : V | 0 < p 2 - p 1} :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  have hd := (hp 2).sub (hp 1)
  have hn : ∀ p ∈ {p : V | 0 < p 2 - p 1}, p 2 - p 1 ≠ 0 := fun p hp => ne_of_gt hp
  have h := (Complex.equivRealProdCLM.symm.comp_contDiffOn_iff).mpr
    (((hp 0).div hd hn).prodMk ((contDiffOn_const (c := (1 : ℝ))).div hd hn))
  convert h using 1
  funext p
  apply Complex.ext <;> rfl

/-- The forward map is continuous for the ordinary hyperboloid subtype topology (G01.d). -/
theorem continuous_toHyperboloid : Continuous toHyperboloid := by
  apply Continuous.subtype_mk
  exact contDiffOn_upperHalfPlaneToHyperboloidCoords.continuousOn.comp_continuous
    UpperHalfPlane.continuous_coe (fun z => z.im_pos)

/-- The literal inverse is continuous for the existing upper-half-plane topology (G01.d). -/
theorem continuous_fromHyperboloid : Continuous fromHyperboloid := by
  apply UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.continuousOn.comp_continuous
    continuous_subtype_val hyperboloid_denominator_pos

/-- The literal coordinate equivalence is a homeomorphism for the ordinary topologies (G01.d). -/
def upperHalfPlaneHomeomorphHyperboloid : UpperHalfPlane ≃ₜ Hyperboloid where
  toEquiv := upperHalfPlaneEquivHyperboloid
  continuous_toFun := continuous_toHyperboloid
  continuous_invFun := continuous_fromHyperboloid

/-- The topological equivalence retains exactly the original two maps (G01.d). -/
theorem upperHalfPlaneHomeomorphHyperboloid_toEquiv :
    upperHalfPlaneHomeomorphHyperboloid.toEquiv = upperHalfPlaneEquivHyperboloid := rfl

/-- The inverse coordinates give a global open chart on the hyperboloid (G01.d). -/
theorem isOpenEmbedding_hyperboloidCoords :
    Topology.IsOpenEmbedding (fun p : Hyperboloid => B p.val) :=
  UpperHalfPlane.isOpenEmbedding_coe.comp upperHalfPlaneHomeomorphHyperboloid.symm.isOpenEmbedding

/-- The global coordinate chart has exactly the positive-height half-plane as target (G01.d). -/
theorem range_hyperboloidCoords :
    Set.range (fun p : Hyperboloid => B p.val) = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact hyperboloidToUpperHalfPlaneCoords_im_pos p
  · intro hz
    exact ⟨toHyperboloid ⟨z, hz⟩, hyperboloidCoords_left_inv ⟨z, hz⟩⟩

/-- The positive sheet contains the image of an upper-half-plane point (G01.d). -/
instance hyperboloidNonempty : Nonempty Hyperboloid := ⟨toHyperboloid default⟩
/-- The literal inverse coordinates define the singleton atlas on the ordinary subtype (G01.d). -/
instance hyperboloidChartedSpace : ChartedSpace ℂ Hyperboloid :=
  isOpenEmbedding_hyperboloidCoords.singletonChartedSpace
/-- The singleton atlas is a real smooth manifold atlas (G01.d). -/
instance hyperboloidIsManifoldReal : IsManifold I ∞ Hyperboloid :=
  isOpenEmbedding_hyperboloidCoords.isManifold_singleton
/-- The existing upper-half-plane atlas is used over the real scalar field (G01.d). -/
instance upperHalfPlaneIsManifoldReal : IsManifold I ∞ UpperHalfPlane :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- Every hyperboloid chart is the same prescribed inverse coordinate function (G01.d). -/
theorem hyperboloid_chartAt (p : Hyperboloid) :
    (chartAt ℂ p : Hyperboloid → ℂ) = fun q => B q.val := rfl
/-- The extended real chart retains the same inverse coordinates (G01.d). -/
theorem hyperboloid_extChartAt (p : Hyperboloid) :
    (extChartAt I p : Hyperboloid → ℂ) = fun q => B q.val := rfl
/-- On positive height the inverse chart has exactly the displayed ambient coordinates (G01.d). -/
theorem hyperboloid_extChartAt_symm_val (p : Hyperboloid) (z : ℂ) (hz : 0 < z.im) :
    ((extChartAt I p).symm z).val = F z := by
  have hr : z ∈ Set.range (fun q : Hyperboloid => B q.val) := by
    rw [range_hyperboloidCoords]
    exact hz
  have hq := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
    (fun q : Hyperboloid => B q.val) isOpenEmbedding_hyperboloidCoords hr
  change B ((extChartAt I p).symm z).val = z at hq
  exact (hyperboloidCoords_right_inv ((extChartAt I p).symm z)).symm.trans (congrArg F hq)

/-- The forward coordinate equivalence is real smooth in the stated atlases (G01.d). -/
theorem contMDiff_toHyperboloid : ContMDiff I I ∞ toHyperboloid := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  have h : (fun p : Hyperboloid => B p.val) ∘ toHyperboloid = ((↑) : UpperHalfPlane → ℂ) := by
    funext z
    exact hyperboloidCoords_left_inv z
  rw [h]
  exact contMDiff_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- The prescribed inverse is also real smooth, on the entire positive sheet (G01.d). -/
theorem contMDiff_fromHyperboloid : ContMDiff I I ∞ fromHyperboloid := by
  apply ContMDiff.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
  exact contMDiff_isOpenEmbedding isOpenEmbedding_hyperboloidCoords

/-- The ordinary ambient inclusion is real smooth in the explicit surface chart (G01.d). -/
theorem contMDiff_hyperboloid_val : ContMDiff I J ∞ (fun p : Hyperboloid => p.val) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [mfld_simps]
  change ContDiffWithinAt ℝ ∞ (fun z : ℂ => ((extChartAt I p).symm z).val)
    Set.univ (B p.val)
  have hp : {z : ℂ | 0 < z.im} ∈ nhds (B p.val) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (hyperboloidToUpperHalfPlaneCoords_im_pos p)
  have h := (contDiffOn_upperHalfPlaneToHyperboloidCoords (B p.val)
    (hyperboloidToUpperHalfPlaneCoords_im_pos p)).contDiffAt hp
  apply h.contDiffWithinAt.congr_of_eventuallyEq
  · rw [nhdsWithin_univ]
    exact Filter.mem_of_superset hp (fun z hz => hyperboloid_extChartAt_symm_val p z hz)
  · exact hyperboloid_extChartAt_symm_val p (B p.val) (hyperboloidToUpperHalfPlaneCoords_im_pos p)

/-- The real differential of the forward rational coordinates, component by component (G01.e). -/
theorem fderiv_upperHalfPlaneToHyperboloidCoords (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ F (z : ℂ) v =
      ![v.re / z.im - z.re * v.im / z.im ^ 2,
        z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2),
        z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)] := by
  have hr : HasFDerivAt Complex.re Complex.reCLM (z : ℂ) := Complex.reCLM.hasFDerivAt
  have hi : HasFDerivAt Complex.im Complex.imCLM (z : ℂ) := Complex.imCLM.hasFDerivAt
  have hden := (hasFDerivAt_const (2 : ℝ) (z : ℂ)).mul hi
  have hn : 2 * z.im ≠ 0 := mul_ne_zero (by norm_num) z.im_ne_zero
  have hrec := (hasFDerivAt_inv z.im_ne_zero).comp (z : ℂ) hi
  have hrec2 := (hasFDerivAt_inv hn).comp (z : ℂ) hden
  have h0 := hr.mul hrec
  have h1 := (((hr.pow 2).add (hi.pow 2)).sub (hasFDerivAt_const (1 : ℝ) (z : ℂ))).mul hrec2
  have h2 := (((hr.pow 2).add (hi.pow 2)).add (hasFDerivAt_const (1 : ℝ) (z : ℂ))).mul hrec2
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Function.comp_apply] at h0 h1 h2
  change HasFDerivAt (fun w : ℂ => w.re * w.im⁻¹) _ _ at h0
  change HasFDerivAt (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 - 1) * (2 * w.im)⁻¹) _ _ at h1
  change HasFDerivAt (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 + 1) * (2 * w.im)⁻¹) _ _ at h2
  have hf : DifferentiableAt ℝ F (z : ℂ) :=
    ((contDiffOn_upperHalfPlaneToHyperboloidCoords (z : ℂ) z.im_pos).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos)).differentiableAt (by simp)
  ext i
  have hc := (hasFDerivAt_pi'.mp hf.hasFDerivAt i).fderiv
  change ((ContinuousLinearMap.proj i).comp (fderiv ℝ F (z : ℂ))) v = _
  rw [← hc]
  fin_cases i
  · change fderiv ℝ (fun w : ℂ => w.re / w.im) (z : ℂ) v =
      v.re / z.im - z.re * v.im / z.im ^ 2
    simp only [div_eq_mul_inv]
    rw [h0.fderiv]
    simp
    ring
  · change fderiv ℝ (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 - 1) / (2 * w.im)) (z : ℂ) v =
      z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2)
    simp only [div_eq_mul_inv]
    rw [h1.fderiv]
    simp
    field_simp [z.im_ne_zero]
    ring
  · change fderiv ℝ (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 + 1) / (2 * w.im)) (z : ℂ) v =
      z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)
    simp only [div_eq_mul_inv]
    rw [h2.fderiv]
    simp
    field_simp [z.im_ne_zero]
    ring

/-- The real differential of the inverse rational coordinates (G01.e). -/
theorem fderiv_hyperboloidToUpperHalfPlaneCoords (p : Hyperboloid) (w : V) :
    fderiv ℝ B p.val w =
      (⟨w 0 / (p.val 2 - p.val 1) - p.val 0 * (w 2 - w 1) / (p.val 2 - p.val 1) ^ 2,
        -(w 2 - w 1) / (p.val 2 - p.val 1) ^ 2⟩ : ℂ) := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.val).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.val)
  have hn := ne_of_gt (hyperboloid_denominator_pos p)
  have hi := (hasFDerivAt_inv hn).comp p.val hd
  have hr := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.val).mul hi
  have h := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp p.val
    (hr.prodMk hi)
  change HasFDerivAt (fun q : V => Complex.equivRealProdCLM.symm
    (q 0 * (q 2 - q 1)⁻¹, (q 2 - q 1)⁻¹)) _ _ at h
  have he : B = fun q : V => Complex.equivRealProdCLM.symm
      (q 0 * (q 2 - q 1)⁻¹, (q 2 - q 1)⁻¹) := by
    funext q
    apply Complex.ext <;> simp [hyperboloidToUpperHalfPlaneCoords, div_eq_mul_inv]
  rw [he, h.fderiv]
  apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring

/-- The Lorentz pairing with a fixed ambient vector, as a continuous linear functional (G01.e). -/
def lorentzFunctional (p : V) : V →L[ℝ] ℝ :=
  p 0 • ContinuousLinearMap.proj 0 + p 1 • ContinuousLinearMap.proj 1 -
    p 2 • ContinuousLinearMap.proj 2

/-- Evaluation of the Lorentz functional in ambient coordinates (G01.e). -/
theorem lorentzFunctional_apply (p w : V) :
    lorentzFunctional p w = p 0 * w 0 + p 1 * w 1 - p 2 * w 2 := rfl

/-- Forward coordinate derivatives are Lorentz-perpendicular to the image point (G01.e). -/
theorem fderiv_toHyperboloid_mem_ker (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ F (z : ℂ) v ∈ (lorentzFunctional (toHyperboloid z).val).ker := by
  change lorentzFunctional (toHyperboloid z).val (fderiv ℝ F (z : ℂ) v) = 0
  rw [fderiv_upperHalfPlaneToHyperboloidCoords, lorentzFunctional_apply]
  simp [toHyperboloid, upperHalfPlaneToHyperboloidCoords]
  field_simp [z.im_ne_zero]
  ring

/-- The backward differential is a left inverse to the forward differential (G01.e). -/
theorem fderiv_hyperboloid_left_inv (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ B (toHyperboloid z).val (fderiv ℝ F (z : ℂ) v) = v := by
  rw [fderiv_hyperboloidToUpperHalfPlaneCoords, fderiv_upperHalfPlaneToHyperboloidCoords]
  simp only [toHyperboloid_val, upperHalfPlaneToHyperboloidCoords_sub]
  apply Complex.ext <;> simp [upperHalfPlaneToHyperboloidCoords] <;>
    field_simp [z.im_ne_zero] <;> ring

/-- On the Lorentz-perpendicular kernel, the forward differential inverts the same backward differential (G01.e). -/
theorem fderiv_hyperboloid_right_inv (p : Hyperboloid) (w : V)
    (hw : w ∈ (lorentzFunctional p.val).ker) :
    fderiv ℝ F (fromHyperboloid p : ℂ) (fderiv ℝ B p.val w) = w := by
  have hd : p.val 2 - p.val 1 ≠ 0 := ne_of_gt (hyperboloid_denominator_pos p)
  change p.val 0 * w 0 + p.val 1 * w 1 - p.val 2 * w 2 = 0 at hw
  rw [fderiv_upperHalfPlaneToHyperboloidCoords, fderiv_hyperboloidToUpperHalfPlaneCoords]
  ext i
  fin_cases i <;> simp [fromHyperboloid, hyperboloidToUpperHalfPlaneCoords] <;>
    field_simp [hd]
  · ring
  · nlinarith [congrArg (fun t : ℝ => t * w 1) p.property.1,
      congrArg (fun t : ℝ => t * w 2) p.property.1,
      congrArg (fun t : ℝ => t * p.val 1) hw,
      congrArg (fun t : ℝ => t * p.val 2) hw]
  · nlinarith [congrArg (fun t : ℝ => t * w 1) p.property.1,
      congrArg (fun t : ℝ => t * w 2) p.property.1,
      congrArg (fun t : ℝ => t * p.val 1) hw,
      congrArg (fun t : ℝ => t * p.val 2) hw]

/-- The forward differential has exactly the Lorentz-perpendicular kernel as its ambient image (G01.e). -/
theorem range_fderiv_toHyperboloid (p : Hyperboloid) :
    (fderiv ℝ F (fromHyperboloid p : ℂ)).range = (lorentzFunctional p.val).ker := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    have h := fderiv_toHyperboloid_mem_ker (fromHyperboloid p) v
    rw [toHyperboloid_fromHyperboloid] at h
    exact h
  · intro hw
    exact ⟨fderiv ℝ B p.val w, fderiv_hyperboloid_right_inv p w hw⟩

/-- The forward differential is injective because its literal backward differential is a left inverse (G01.e). -/
theorem injective_fderiv_toHyperboloid (z : UpperHalfPlane) :
    Function.Injective (fderiv ℝ F (z : ℂ)) :=
  Function.LeftInverse.injective (fderiv_hyperboloid_left_inv z)

/-- In the actual real singleton chart, the inclusion differential is the displayed forward derivative (G01.e). -/
theorem mfderiv_hyperboloid_val (p : Hyperboloid) :
    mfderiv I J (fun q : Hyperboloid => q.val) p = fderiv ℝ F (fromHyperboloid p : ℂ) := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [mfld_simps]
  change HasFDerivWithinAt (fun z : ℂ => ((extChartAt I p).symm z).val)
    (fderiv ℝ F (fromHyperboloid p : ℂ)) Set.univ (fromHyperboloid p : ℂ)
  have hp : {z : ℂ | 0 < z.im} ∈ nhds (fromHyperboloid p : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (fromHyperboloid p).im_pos
  have hf := ((contDiffOn_upperHalfPlaneToHyperboloidCoords _ (fromHyperboloid p).im_pos).contDiffAt
    hp).differentiableAt (by simp)
  apply HasFDerivAt.hasFDerivWithinAt
  apply hf.hasFDerivAt.congr_of_eventuallyEq
  exact Filter.mem_of_superset hp (fun z hz => hyperboloid_extChartAt_symm_val p z hz)

/-- The actual inclusion derivative has precisely the Lorentz-perpendicular image (G01.e). -/
theorem range_mfderiv_hyperboloid_val (p : Hyperboloid) :
    (mfderiv I J (fun q : Hyperboloid => q.val) p).range = (lorentzFunctional p.val).ker := by
  rw [mfderiv_hyperboloid_val]
  exact range_fderiv_toHyperboloid p

/-- Intrinsic backward-after-forward differentials compose to identity (G01.e). -/
theorem mfderiv_fromHyperboloid_comp_toHyperboloid (z : UpperHalfPlane) :
    (mfderiv I I fromHyperboloid (toHyperboloid z)).comp (mfderiv I I toHyperboloid z) =
      ContinuousLinearMap.id ℝ (TangentSpace I z) := by
  rw [← mfderiv_comp z
    (contMDiff_fromHyperboloid.mdifferentiable (by simp) (toHyperboloid z))
    (contMDiff_toHyperboloid.mdifferentiable (by simp) z)]
  have h : fromHyperboloid ∘ toHyperboloid = id := funext fromHyperboloid_toHyperboloid
  rw [h, mfderiv_id]

/-- Intrinsic forward-after-backward differentials compose to identity (G01.e). -/
theorem mfderiv_toHyperboloid_comp_fromHyperboloid (p : Hyperboloid) :
    (mfderiv I I toHyperboloid (fromHyperboloid p)).comp (mfderiv I I fromHyperboloid p) =
      ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  rw [← mfderiv_comp p
    (contMDiff_toHyperboloid.mdifferentiable (by simp) (fromHyperboloid p))
    (contMDiff_fromHyperboloid.mdifferentiable (by simp) p)]
  have h : toHyperboloid ∘ fromHyperboloid = id := funext toHyperboloid_fromHyperboloid
  rw [h, mfderiv_id]

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic tangent vectors identify continuously and linearly with the ambient Lorentz kernel,
with inverse the restriction of the literal backward differential (G01.e). -/
def hyperboloidTangentEquivKer (p : Hyperboloid) :
    TangentSpace I p ≃L[ℝ] (lorentzFunctional p.val).ker :=
  { (mfderiv I J (fun q : Hyperboloid => q.val) p).codRestrict
      (lorentzFunctional p.val).ker (fun v => by
        rw [← range_mfderiv_hyperboloid_val p]
        exact ⟨v, rfl⟩) with
    invFun := (fderiv ℝ B p.val).domRestrict (lorentzFunctional p.val).ker
    continuous_toFun := ((mfderiv I J (fun q : Hyperboloid => q.val) p).codRestrict
      (lorentzFunctional p.val).ker (fun v => by
        rw [← range_mfderiv_hyperboloid_val p]
        exact ⟨v, rfl⟩)).continuous
    continuous_invFun := ((fderiv ℝ B p.val).domRestrict (lorentzFunctional p.val).ker).continuous
    left_inv := fun v => by
      change fderiv ℝ B p.val (mfderiv I J (fun q : Hyperboloid => q.val) p v) = v
      rw [mfderiv_hyperboloid_val]
      have h := fderiv_hyperboloid_left_inv (fromHyperboloid p) v
      rw [toHyperboloid_fromHyperboloid] at h
      exact h
    right_inv := fun w => by
      apply Subtype.ext
      change mfderiv I J (fun q : Hyperboloid => q.val) p (fderiv ℝ B p.val w.val) = w.val
      rw [mfderiv_hyperboloid_val]
      exact fderiv_hyperboloid_right_inv p w.val w.property }

/-- The forward tangent identification is exactly the actual inclusion derivative (G01.e). -/
theorem hyperboloidTangentEquivKer_apply (p : Hyperboloid) (v : TangentSpace I p) :
    (hyperboloidTangentEquivKer p v).val = mfderiv I J (fun q : Hyperboloid => q.val) p v := rfl

/-- The inverse tangent identification is exactly the same restricted backward derivative (G01.e). -/
theorem hyperboloidTangentEquivKer_symm_apply (p : Hyperboloid)
    (w : (lorentzFunctional p.val).ker) :
    (hyperboloidTangentEquivKer p).symm w = fderiv ℝ B p.val w.val := rfl

/-- The actual inverse chart agrees locally with the ambient forward coordinates (G01.d/e). -/
theorem hyperboloid_chart_inverse_eventually (p : Hyperboloid) :
    (fun z : ℂ => ((extChartAt I p).symm z).val) =ᶠ[nhds (fromHyperboloid p : ℂ)] F :=
  Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (fromHyperboloid p).im_pos) (fun z hz => hyperboloid_extChartAt_symm_val p z hz)

/-! ## The displayed Lorentz calculation and the actual positive smooth tensors

This section follows G01.f/g, canonical lines 89–98: auxiliary coordinates,
quadratic identity, polarization, positivity, intrinsic restriction and smooth sections.
-/

open scoped Bundle
local notation "K" => (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)

/-- The continuous symmetric Lorentz form with coordinates ordered X,Y,T. (G01.f/g) -/
def lorentzBilinear : V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3) : V →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3) : V →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3) : V →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3) : V →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3) : V →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3) : V →L[ℝ] ℝ)

/-- The upper-half-plane form, the Euclidean coordinate form divided by height squared. (G01.f/g) -/
def upperHalfPlaneCoordinateTensor (z : UpperHalfPlane) : K :=
  (z.im ^ 2)⁻¹ •
    (Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM)

/-- Evaluation of the literal Lorentz form in the three ambient coordinates. (G01.f/g) -/
theorem lorentzBilinear_apply (v w : V) :
  lorentzBilinear v w = v 0 * w 0 + v 1 * w 1 - v 2 * w 2 := by
  rfl

/-- Fixing the first Lorentz argument gives the same constraint functional as the tangent kernel. (G01.f/g) -/
theorem lorentzBilinear_eq_functional (p : V) :
  lorentzBilinear p = lorentzFunctional p := by
  ext w
  rfl

/-- Evaluation of the source metric is the displayed height-weighted scalar product. (G01.f/g) -/
theorem upperHalfPlaneCoordinateTensor_apply (z : UpperHalfPlane) (v w : ℂ) :
  upperHalfPlaneCoordinateTensor z v w = (v.re * w.re + v.im * w.im) / z.im ^ 2 := by
  change (z.im ^ 2)⁻¹ * (v.re * w.re + v.im * w.im) = _
  rw [div_eq_mul_inv, mul_comm]

/-- The displayed differential dX of X=x/y. (G01.f/g) -/
theorem fderiv_upperHalfPlaneToHyperboloidCoords_x (z : UpperHalfPlane) (v : ℂ) :
  fderiv ℝ F (z : ℂ) v 0 = v.re / z.im - z.re * v.im / z.im ^ 2 := by
  rw [fderiv_upperHalfPlaneToHyperboloidCoords]
  rfl


/-- The displayed differential dA of A=T-Y=1/y. (G01.f/g) -/
theorem fderiv_upperHalfPlaneToHyperboloidCoords_sub (z : UpperHalfPlane) (v : ℂ) :
  fderiv ℝ F (z : ℂ) v 2 - fderiv ℝ F (z : ℂ) v 1 = -v.im / z.im ^ 2 := by
  rw [fderiv_upperHalfPlaneToHyperboloidCoords]
  change (z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)) -
    (z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2)) = _
  field_simp
  <;> ring


/-- The displayed differential dB of B=T+Y=(x²+y²)/y. (G01.f/g) -/
theorem fderiv_upperHalfPlaneToHyperboloidCoords_add (z : UpperHalfPlane) (v : ℂ) :
  fderiv ℝ F (z : ℂ) v 2 + fderiv ℝ F (z : ℂ) v 1 =
    2 * z.re * v.re / z.im + (1 - z.re ^ 2 / z.im ^ 2) * v.im := by
  rw [fderiv_upperHalfPlaneToHyperboloidCoords]
  change (z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)) +
    (z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2)) = _
  field_simp
  <;> ring


/-- Rewrite the Lorentz quadratic differential as dX²-dA dB. (G01.f/g) -/
theorem lorentz_fderiv_eq_auxiliary (z : UpperHalfPlane) (v : ℂ) :
  lorentzBilinear (fderiv ℝ F (z : ℂ) v) (fderiv ℝ F (z : ℂ) v) =
    (fderiv ℝ F (z : ℂ) v 0) ^ 2 -
      (fderiv ℝ F (z : ℂ) v 2 - fderiv ℝ F (z : ℂ) v 1) *
      (fderiv ℝ F (z : ℂ) v 2 + fderiv ℝ F (z : ℂ) v 1) := by
  rw [lorentzBilinear_apply]
  ring


/-- Substitute the three displayed differentials into dX²-dA dB. (G01.f/g) -/
theorem auxiliary_fderiv_quadratic (z : UpperHalfPlane) (v : ℂ) :
  (fderiv ℝ F (z : ℂ) v 0) ^ 2 -
      (fderiv ℝ F (z : ℂ) v 2 - fderiv ℝ F (z : ℂ) v 1) *
      (fderiv ℝ F (z : ℂ) v 2 + fderiv ℝ F (z : ℂ) v 1) =
    (v.re ^ 2 + v.im ^ 2) / z.im ^ 2 := by
  rw [fderiv_upperHalfPlaneToHyperboloidCoords_x,
    fderiv_upperHalfPlaneToHyperboloidCoords_sub,
    fderiv_upperHalfPlaneToHyperboloidCoords_add]
  field_simp
  <;> ring


/-- The Lorentz quadratic form pulls back to the height-weighted Euclidean form. (G01.f/g) -/
theorem lorentz_fderiv_quadratic (z : UpperHalfPlane) (v : ℂ) :
  lorentzBilinear (fderiv ℝ F (z : ℂ) v) (fderiv ℝ F (z : ℂ) v) =
    (v.re ^ 2 + v.im ^ 2) / z.im ^ 2 := by
  exact (lorentz_fderiv_eq_auxiliary z v).trans (auxiliary_fderiv_quadratic z v)


/-- Symmetry of the ambient Lorentz form. (G01.f/g) -/
theorem lorentzBilinear_symm (v w : V) : lorentzBilinear v w = lorentzBilinear w v
 := by
  simp only [lorentzBilinear_apply]
  ring
/-- Symmetry of the height-weighted coordinate form. (G01.f/g) -/
theorem upperHalfPlaneCoordinateTensor_symm (z : UpperHalfPlane) (v w : ℂ) :
  upperHalfPlaneCoordinateTensor z v w = upperHalfPlaneCoordinateTensor z w v := by
  simp only [upperHalfPlaneCoordinateTensor_apply]
  ring


/-- Polarization of the computed quadratic identity gives the full tensor identity. (G01.f/g) -/
theorem lorentz_fderiv_bilinear (z : UpperHalfPlane) (v w : ℂ) :
  lorentzBilinear (fderiv ℝ F (z : ℂ) v) (fderiv ℝ F (z : ℂ) w) =
    upperHalfPlaneCoordinateTensor z v w := by
  let L : LinearMap.BilinForm ℝ V :=
    (ContinuousLinearMap.coeLM ℝ).comp lorentzBilinear.toLinearMap
  let U : LinearMap.BilinForm ℝ ℂ :=
    (ContinuousLinearMap.coeLM ℝ).comp (upperHalfPlaneCoordinateTensor z).toLinearMap
  let P := L.comp (fderiv ℝ F (z : ℂ)).toLinearMap (fderiv ℝ F (z : ℂ)).toLinearMap
  have hdiag (a : ℂ) : P a a = U a a := by
    change lorentzBilinear (fderiv ℝ F (z : ℂ) a) (fderiv ℝ F (z : ℂ) a) =
      upperHalfPlaneCoordinateTensor z a a
    rw [lorentz_fderiv_quadratic, upperHalfPlaneCoordinateTensor_apply]
    simp only [pow_two]
  have heq : P = U := LinearMap.BilinForm.ext_of_isSymm
    ⟨fun a b => lorentzBilinear_symm _ _⟩
    ⟨fun a b => upperHalfPlaneCoordinateTensor_symm z a b⟩ hdiag
  exact congrArg (fun Q : LinearMap.BilinForm ℝ ℂ => Q v w) heq


/-- The source coordinate form is strictly positive on every nonzero real vector. (G01.f/g) -/
theorem upperHalfPlaneCoordinateTensor_pos (z : UpperHalfPlane) (v : ℂ) (hv : v ≠ 0) :
  0 < upperHalfPlaneCoordinateTensor z v v := by
  rw [upperHalfPlaneCoordinateTensor_apply]
  have hp : 0 < v.re ^ 2 + v.im ^ 2 := by
    have hr := sq_nonneg v.re
    have hi := sq_nonneg v.im
    by_contra h
    have hz : v = 0 := by
      apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
      · nlinarith
      · nlinarith
    exact hv hz
  simpa only [pow_two] using div_pos hp (sq_pos_of_pos z.im_pos)


/-- The Lorentz form is positive on every nonzero tangent-kernel vector, using the same inverse differential. (G01.f/g) -/
theorem lorentzBilinear_pos_on_ker (p : Hyperboloid) (w : V)
    (hw : w ∈ (lorentzFunctional p.val).ker) (hwn : w ≠ 0) :
  0 < lorentzBilinear w w := by
  let v := fderiv ℝ B p.val w
  have heq : fderiv ℝ F (fromHyperboloid p : ℂ) v = w :=
    fderiv_hyperboloid_right_inv p w hw
  have hv : v ≠ 0 := by
    intro h
    apply hwn
    simpa only [h, map_zero] using heq.symm
  rw [← heq, lorentz_fderiv_bilinear]
  exact upperHalfPlaneCoordinateTensor_pos (fromHyperboloid p) v hv


/-- The source tensor on intrinsic tangents, defined through the actual coordinate inclusion differential. (G01.f/g) -/
def upperHalfPlaneTangentTensor (z : UpperHalfPlane) :
    TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ :=
  let c : TangentSpace I z →L[ℝ] ℂ :=
    mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z
  let r := Complex.reCLM.comp c
  let s := Complex.imCLM.comp c
  (z.im ^ 2)⁻¹ • (r.smulRight r + s.smulRight s)

/-- The Lorentz restriction on intrinsic hyperboloid tangents through the actual ambient inclusion. (G01.f/g) -/
def hyperboloidTangentTensor (p : Hyperboloid) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let d : TangentSpace I p →L[ℝ] V := mfderiv I J (fun q : Hyperboloid => q.val) p
  let x := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3)).comp d
  let y := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)).comp d
  let t := (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)).comp d
  x.smulRight x + y.smulRight y - t.smulRight t

/-- The source intrinsic tensor evaluates as its coordinate form on the inclusion differential. (G01.f/g) -/
theorem upperHalfPlaneTangentTensor_apply (z : UpperHalfPlane) (v w : TangentSpace I z) :
  upperHalfPlaneTangentTensor z v w = upperHalfPlaneCoordinateTensor z
    (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v)
    (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w) := by
  rfl

/-- The target intrinsic tensor evaluates as the Lorentz form on ambient inclusion differentials. (G01.f/g) -/
theorem hyperboloidTangentTensor_apply (p : Hyperboloid) (v w : TangentSpace I p) :
  hyperboloidTangentTensor p v w = lorentzBilinear
    (mfderiv I J (fun q : Hyperboloid => q.val) p v)
    (mfderiv I J (fun q : Hyperboloid => q.val) p w) := by
  rfl

private theorem z_tangent_coordinates (z₀ z : UpperHalfPlane) (v : TangentSpace I z) :
    (trivializationAt ℂ (fun q : UpperHalfPlane => TangentSpace I q) z₀
      (Bundle.TotalSpace.mk' ℂ z v)).2 =
      mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v := by
  have hs : z ∈ (chartAt ℂ z₀).source := by
    change z ∈ Set.univ
    trivial
  have hb : z ∈ (trivializationAt ℂ (TangentSpace I) z₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hs
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hb,
    TangentBundle.continuousLinearMapAt_trivializationAt hs]
  rfl

private theorem p_tangent_coordinates (p₀ p : Hyperboloid) (v : TangentSpace I p) :
    (trivializationAt ℂ (fun q : Hyperboloid => TangentSpace I q) p₀
      (Bundle.TotalSpace.mk' ℂ p v)).2 =
      mfderiv I I (fun q : Hyperboloid => hyperboloidToUpperHalfPlaneCoords q.val) p v := by
  have hs : p ∈ (chartAt ℂ p₀).source := by
    change p ∈ Set.univ
    trivial
  have hb : p ∈ (trivializationAt ℂ (TangentSpace I) p₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hs
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hb,
    TangentBundle.continuousLinearMapAt_trivializationAt hs]
  rfl

private theorem source_chart_derivative (z : UpperHalfPlane) :
    mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z =
      ContinuousLinearMap.id ℝ ℂ := by
  change mfderiv I I (extChartAt I z) z = _
  exact mfderiv_extChartAt_self

private theorem target_chart_derivative (p : Hyperboloid) :
    mfderiv I I (fun q : Hyperboloid => hyperboloidToUpperHalfPlaneCoords q.val) p =
      ContinuousLinearMap.id ℝ ℂ := by
  change mfderiv I I (extChartAt I p) p = _
  exact mfderiv_extChartAt_self

private theorem actual_chain (z : UpperHalfPlane) (v : TangentSpace I z) :
    (mfderiv I J (fun p : Hyperboloid => p.val) (toHyperboloid z))
      (mfderiv I I toHyperboloid z v) =
    fderiv ℝ F (z : ℂ) (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v) := by
  have hc : MDifferentiableAt I I (fun q : UpperHalfPlane => (q : ℂ)) z := by
    change MDifferentiableAt I I (extChartAt I z) z
    exact mdifferentiableAt_extChartAt (mem_chart_source ℂ z)
  have hn : {w : ℂ | 0 < w.im} ∈ nhds (z : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos
  have hf : DifferentiableAt ℝ F (z : ℂ) :=
    ((contDiffOn_upperHalfPlaneToHyperboloidCoords _ z.im_pos).contDiffAt hn).differentiableAt
      (by simp)
  have hleft := mfderiv_comp z
    (contMDiff_hyperboloid_val.mdifferentiable (by simp) (toHyperboloid z))
    (contMDiff_toHyperboloid.mdifferentiable (by simp) z)
  have hright := mfderiv_comp z hf.mdifferentiableAt hc
  have heq : (fun p : Hyperboloid => p.val) ∘ toHyperboloid =
      F ∘ (fun q : UpperHalfPlane => (q : ℂ)) := rfl
  rw [heq] at hleft
  rw [mfderiv_eq_fderiv] at hright
  exact congrArg (fun L => L v) (hleft.symm.trans hright)

/-- Symmetry of the actual source tangent tensor. (G01.f/g) -/
theorem upperHalfPlaneTangentTensor_symm (z : UpperHalfPlane) (v w : TangentSpace I z) :
  upperHalfPlaneTangentTensor z v w = upperHalfPlaneTangentTensor z w v
 := by
  simp only [upperHalfPlaneTangentTensor_apply]
  exact upperHalfPlaneCoordinateTensor_symm z _ _
/-- Symmetry of the actual target tangent tensor. (G01.f/g) -/
theorem hyperboloidTangentTensor_symm (p : Hyperboloid) (v w : TangentSpace I p) :
  hyperboloidTangentTensor p v w = hyperboloidTangentTensor p w v := by
  simp only [hyperboloidTangentTensor_apply]
  exact lorentzBilinear_symm _ _


/-- Strict positivity for all nonzero intrinsic source tangents. (G01.f/g) -/
theorem upperHalfPlaneTangentTensor_pos (z : UpperHalfPlane) (v : TangentSpace I z)
    (hv : v ≠ 0) : 0 < upperHalfPlaneTangentTensor z v v
 := by
  rw [upperHalfPlaneTangentTensor_apply, source_chart_derivative]
  exact upperHalfPlaneCoordinateTensor_pos z v hv
/-- Strict positivity for all nonzero intrinsic target tangents, via the actual tangent-kernel equivalence. (G01.f/g) -/
theorem hyperboloidTangentTensor_pos (p : Hyperboloid) (v : TangentSpace I p)
    (hv : v ≠ 0) : 0 < hyperboloidTangentTensor p v v := by
  rw [hyperboloidTangentTensor_apply]
  let e := hyperboloidTangentEquivKer p
  have he : (e v).val = mfderiv I J (fun q : Hyperboloid => q.val) p v :=
    hyperboloidTangentEquivKer_apply p v
  rw [← he]
  apply lorentzBilinear_pos_on_ker p (e v).val (e v).property
  intro hz
  apply hv
  apply e.injective
  apply Subtype.ext
  simpa only [map_zero, ZeroMemClass.coe_zero] using hz


/-- The actual manifold differential of the forward map preserves the two intrinsic tensors. (G01.f/g) -/
theorem toHyperboloid_preserves_tangentTensor (z : UpperHalfPlane) (v w : TangentSpace I z) :
  hyperboloidTangentTensor (toHyperboloid z)
    (mfderiv I I toHyperboloid z v) (mfderiv I I toHyperboloid z w) =
      upperHalfPlaneTangentTensor z v w := by
  rw [hyperboloidTangentTensor_apply, upperHalfPlaneTangentTensor_apply,
    actual_chain, actual_chain]
  exact lorentz_fderiv_bilinear z _ _


/-- The source tensor coefficients in every preferred singleton-chart hom trivialization. (G01.f/g) -/
theorem upperHalfPlaneTangentTensor_inCoordinates (z₀ z : UpperHalfPlane) :
  (trivializationAt K
    (fun q : UpperHalfPlane => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) z₀
    (Bundle.TotalSpace.mk' K z (upperHalfPlaneTangentTensor z))).2 =
      upperHalfPlaneCoordinateTensor z := by
  let e := trivializationAt ℂ (fun q : UpperHalfPlane => TangentSpace I q) z₀
  have hs : z ∈ (chartAt ℂ z₀).source := by
    change z ∈ Set.univ
    trivial
  have hb : z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hs
  have hr : z ∈ (trivializationAt ℝ (fun _ : UpperHalfPlane => ℝ) z₀).baseSet := by
    change z ∈ Set.univ
    trivial
  have hforward (a : TangentSpace I z) : e.continuousLinearMapAt ℝ z a = a := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb]
    rw [z_tangent_coordinates, source_chart_derivative]
    rfl
  have hback (a : ℂ) : e.symm z a = a := by
    rw [← e.symmL_apply (R := ℝ) hb]
    exact (hforward (e.symmL ℝ z a)).symm.trans
      (e.continuousLinearMapAt_symmL (R := ℝ) hb a)
  ext v w
  change ContinuousLinearMap.inCoordinates ℂ (TangentSpace I)
    (ℂ →L[ℝ] ℝ) (fun q : UpperHalfPlane => TangentSpace I q →L[ℝ] ℝ)
    z₀ z z₀ z (upperHalfPlaneTangentTensor z) v w = _
  rw [inCoordinates_apply_eq₂ hb hb hr]
  simp only [Bundle.Trivial.eq_trivialization UpperHalfPlane ℝ
    (trivializationAt ℝ (Bundle.Trivial UpperHalfPlane ℝ) z₀),
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  change upperHalfPlaneTangentTensor z (e.symm z v) (e.symm z w) = _
  rw [upperHalfPlaneTangentTensor_apply, source_chart_derivative]
  change upperHalfPlaneCoordinateTensor z (e.symm z v) (e.symm z w) = _
  rw [hback, hback]


/-- The target tensor coefficients are the same source coefficients at the inverse coordinate point. (G01.f/g) -/
theorem hyperboloidTangentTensor_inCoordinates (p₀ p : Hyperboloid) :
  (trivializationAt K
    (fun q : Hyperboloid => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) p₀
    (Bundle.TotalSpace.mk' K p (hyperboloidTangentTensor p))).2 =
      upperHalfPlaneCoordinateTensor (fromHyperboloid p) := by
  let e := trivializationAt ℂ (fun q : Hyperboloid => TangentSpace I q) p₀
  have hs : p ∈ (chartAt ℂ p₀).source := by
    change p ∈ Set.univ
    trivial
  have hb : p ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hs
  have hr : p ∈ (trivializationAt ℝ (fun _ : Hyperboloid => ℝ) p₀).baseSet := by
    change p ∈ Set.univ
    trivial
  have hforward (a : TangentSpace I p) : e.continuousLinearMapAt ℝ p a = a := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb]
    rw [p_tangent_coordinates, target_chart_derivative]
    rfl
  have hback (a : ℂ) : e.symm p a = a := by
    rw [← e.symmL_apply (R := ℝ) hb]
    exact (hforward (e.symmL ℝ p a)).symm.trans
      (e.continuousLinearMapAt_symmL (R := ℝ) hb a)
  ext v w
  change ContinuousLinearMap.inCoordinates ℂ (TangentSpace I)
    (ℂ →L[ℝ] ℝ) (fun q : Hyperboloid => TangentSpace I q →L[ℝ] ℝ)
    p₀ p p₀ p (hyperboloidTangentTensor p) v w = _
  rw [inCoordinates_apply_eq₂ hb hb hr]
  simp only [Bundle.Trivial.eq_trivialization Hyperboloid ℝ
    (trivializationAt ℝ (Bundle.Trivial Hyperboloid ℝ) p₀),
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  change hyperboloidTangentTensor p (e.symm p v) (e.symm p w) = _
  rw [hyperboloidTangentTensor_apply, mfderiv_hyperboloid_val]
  rw [hback, hback]
  exact lorentz_fderiv_bilinear (fromHyperboloid p) v w



set_option synthInstance.maxHeartbeats 80000 in
/-- The height-weighted coordinate bilinear form varies smoothly in real coordinates. (G01.f/g) -/
theorem contMDiff_upperHalfPlaneCoordinateTensor :
  ContMDiff I 𝓘(ℝ, K) ∞ upperHalfPlaneCoordinateTensor := by
  let coefficientBase : K :=
    Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM
  let L : ℝ →L[ℝ] K := (ContinuousLinearMap.id ℝ ℝ).smulRight coefficientBase
  have hL : ContDiff ℝ ∞ (L : ℝ → K) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ) («F» := K) L
  let Q : ℂ → K := fun z => (z.im ^ 2)⁻¹ •
    (Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM)
  have hQ : ContDiffOn ℝ ∞ Q {z : ℂ | 0 < z.im} := by
    have hi : ContDiffOn ℝ ∞ (fun z : ℂ => (z.im ^ 2)⁻¹) {z : ℂ | 0 < z.im} :=
      (Complex.imCLM.contDiff.contDiffOn.pow 2).inv
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    exact hL.comp_contDiffOn hi
  intro z
  have hc : ContMDiffAt I I ∞ (fun q : UpperHalfPlane => (q : ℂ)) z := by
    change ContMDiffAt I I ∞ (extChartAt I z) z
    exact contMDiffAt_extChartAt
  have hn : {w : ℂ | 0 < w.im} ∈ nhds (z : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos
  exact ((hQ (z : ℂ) z.im_pos).contDiffAt hn).contMDiffAt.comp z hc


/-- The actual source tangent tensor is a smooth section of the bilinear hom bundle. (G01.f/g) -/
theorem contMDiff_upperHalfPlaneTangentTensor :
  ContMDiff I ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, K)) ∞
    (fun z : UpperHalfPlane => Bundle.TotalSpace.mk' K z (upperHalfPlaneTangentTensor z)) := by
  intro z₀
  apply (Bundle.contMDiffAt_section z₀).2
  have heq : (fun z : UpperHalfPlane =>
      (trivializationAt K
        (fun q : UpperHalfPlane => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) z₀
        (Bundle.TotalSpace.mk' K z (upperHalfPlaneTangentTensor z))).2) =
      upperHalfPlaneCoordinateTensor := funext (upperHalfPlaneTangentTensor_inCoordinates z₀)
  rw [heq]
  exact contMDiff_upperHalfPlaneCoordinateTensor z₀


/-- The actual target Lorentz tangent tensor is a smooth section of the bilinear hom bundle. (G01.f/g) -/
theorem contMDiff_hyperboloidTangentTensor :
  ContMDiff I ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, K)) ∞
    (fun p : Hyperboloid => Bundle.TotalSpace.mk' K p (hyperboloidTangentTensor p))
 := by
  intro p₀
  apply (Bundle.contMDiffAt_section p₀).2
  have heq : (fun p : Hyperboloid =>
      (trivializationAt K
        (fun q : Hyperboloid => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) p₀
        (Bundle.TotalSpace.mk' K p (hyperboloidTangentTensor p))).2) =
      upperHalfPlaneCoordinateTensor ∘ fromHyperboloid :=
    funext (hyperboloidTangentTensor_inCoordinates p₀)
  rw [heq]
  exact (contMDiff_upperHalfPlaneCoordinateTensor.comp contMDiff_fromHyperboloid) p₀

/-! ## Actual model metric, angle, speed and finite-length transport (G01.k) -/

open scoped ENNReal BigOperators
open Set MeasureTheory Filter Manifold

/-- The real smooth equivalence between the upper half-plane and the positive
Lorentz hyperboloid, with the literal coordinate maps in both directions
(textbook G01.d/e/k). -/
def upperHalfPlaneDiffeomorphHyperboloid : UpperHalfPlane ≃ₘ⟮I, I⟯ Hyperboloid :=
  { upperHalfPlaneEquivHyperboloid with
    contMDiff_toFun := contMDiff_toHyperboloid
    contMDiff_invFun := contMDiff_fromHyperboloid }

/-- The smooth upper-half-plane metric is the actual positive coordinate
tensor (dx² + dy²)/y² on intrinsic tangent vectors (textbook G01.f/g/k). -/
def upperHalfPlaneMetric :
    Bundle.ContMDiffRiemannianMetric I ∞ ℂ (fun z : UpperHalfPlane => TangentSpace I z) :=
  letI : ∀ z : UpperHalfPlane, T2Space (TangentSpace I z) :=
    fun z => FiberBundle.t2Space ℂ (fun z : UpperHalfPlane => TangentSpace I z) z
  Bundle.smoothMetricOfPositive upperHalfPlaneTangentTensor
    upperHalfPlaneTangentTensor_symm upperHalfPlaneTangentTensor_pos
    contMDiff_upperHalfPlaneTangentTensor

/-- The hyperboloid's smooth metric is the Lorentz form restricted through
the actual ambient inclusion to its tangent planes (textbook G01.f/g/k). -/
def hyperboloidMetric :
    Bundle.ContMDiffRiemannianMetric I ∞ ℂ (fun p : Hyperboloid => TangentSpace I p) :=
  letI : ∀ p : Hyperboloid, T2Space (TangentSpace I p) :=
    fun p => FiberBundle.t2Space ℂ (fun p : Hyperboloid => TangentSpace I p) p
  Bundle.smoothMetricOfPositive hyperboloidTangentTensor
    hyperboloidTangentTensor_symm hyperboloidTangentTensor_pos
    contMDiff_hyperboloidTangentTensor


/-- The smooth model equivalence has exactly the forward and inverse coordinate functions (G01.d/e/k). -/
theorem upperHalfPlaneDiffeomorphHyperboloid_coe :
    (⇑upperHalfPlaneDiffeomorphHyperboloid : UpperHalfPlane → Hyperboloid) = toHyperboloid ∧
    (⇑upperHalfPlaneDiffeomorphHyperboloid.symm : Hyperboloid → UpperHalfPlane) = fromHyperboloid := by
  exact ⟨rfl, rfl⟩

/-- The constructed source metric has exactly the previously identified intrinsic coordinate tensor (G01.f/g/k). -/
theorem upperHalfPlaneMetric_inner (x : UpperHalfPlane) (v w : TangentSpace I x) :
    upperHalfPlaneMetric.inner x v w = upperHalfPlaneTangentTensor x v w := by
  rfl

/-- The constructed target metric has exactly the actual Lorentz tangent restriction, not an ambient Euclidean inner product (G01.f/g/k). -/
theorem hyperboloidMetric_inner (x : Hyperboloid) (v w : TangentSpace I x) :
    hyperboloidMetric.inner x v w = hyperboloidTangentTensor x v w := by
  rfl

/-- The actual forward differential preserves the two stated model metrics (G01.g/k). -/
theorem toHyperboloid_preserves_metric (z : UpperHalfPlane) (v w : TangentSpace I z) :
    hyperboloidMetric.inner (toHyperboloid z)
      (mfderiv I I toHyperboloid z v) (mfderiv I I toHyperboloid z w) =
        upperHalfPlaneMetric.inner z v w := by
  exact toHyperboloid_preserves_tangentTensor z v w

/-- The actual inverse differential preserves the same metrics, by the smooth inverse identities (G01.j.1/k). -/
theorem fromHyperboloid_preserves_metric (p : Hyperboloid) (v w : TangentSpace I p) :
    upperHalfPlaneMetric.inner (fromHyperboloid p)
      (mfderiv I I fromHyperboloid p v) (mfderiv I I fromHyperboloid p w) =
        hyperboloidMetric.inner p v w := by
  exact symm_tensorPreserving_of_diffeomorph upperHalfPlaneMetric hyperboloidMetric
    upperHalfPlaneDiffeomorphHyperboloid toHyperboloid_preserves_tangentTensor p v w

/-- The forward differential preserves real and extended tangent norms and nonzero-direction unoriented angles, and is injective (G01.h/k). -/
theorem toHyperboloid_norm_angle (x : UpperHalfPlane) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    (∀ v : TangentSpace I x, ‖mfderiv I I toHyperboloid x v‖ = ‖v‖) ∧
    (∀ v : TangentSpace I x, ‖mfderiv I I toHyperboloid x v‖ₑ = ‖v‖ₑ) ∧
    Function.Injective (mfderiv I I toHyperboloid x) ∧
    (∀ v w : TangentSpace I x, v ≠ 0 → w ≠ 0 →
      InnerProductGeometry.angle (mfderiv I I toHyperboloid x v) (mfderiv I I toHyperboloid x w) =
        InnerProductGeometry.angle v w) := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := (mfderiv I I toHyperboloid x).toLinearMap.isometryOfInner (toHyperboloid_preserves_tangentTensor x)
  exact ⟨L.norm_map, L.enorm_map, L.injective, fun v w _ _ => L.angle_map v w⟩

/-- The forward coordinate map preserves ordinary real and extended C1 speeds for the stated metrics (G01.i/k). -/
theorem toHyperboloid_speed (γ : ℝ → UpperHalfPlane) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I (toHyperboloid ∘ γ) t (1 : ℝ)‖ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
    ‖mfderiv 𝓘(ℝ, ℝ) I (toHyperboloid ∘ γ) t (1 : ℝ)‖ₑ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  exact speed_comp_of_tensorPreserving
    upperHalfPlaneMetric hyperboloidMetric toHyperboloid contMDiff_toHyperboloid
    toHyperboloid_preserves_tangentTensor γ t hγ

/-- The forward map preserves within speeds on the same parameter set, including strict-piece one-sided endpoints (G01.i/k). -/
theorem toHyperboloid_speedWithin (γ : ℝ → UpperHalfPlane) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (toHyperboloid ∘ γ) s t (1 : ℝ)‖ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (toHyperboloid ∘ γ) s t (1 : ℝ)‖ₑ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  exact speedWithin_comp_of_tensorPreserving
    upperHalfPlaneMetric hyperboloidMetric toHyperboloid contMDiff_toHyperboloid
    toHyperboloid_preserves_tangentTensor γ s t hγ hs

/-- The inverse differential preserves real and extended tangent norms and nonzero-direction unoriented angles, and is injective (G01.h/k). -/
theorem fromHyperboloid_norm_angle (x : Hyperboloid) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    (∀ v : TangentSpace I x, ‖mfderiv I I fromHyperboloid x v‖ = ‖v‖) ∧
    (∀ v : TangentSpace I x, ‖mfderiv I I fromHyperboloid x v‖ₑ = ‖v‖ₑ) ∧
    Function.Injective (mfderiv I I fromHyperboloid x) ∧
    (∀ v w : TangentSpace I x, v ≠ 0 → w ≠ 0 →
      InnerProductGeometry.angle (mfderiv I I fromHyperboloid x v) (mfderiv I I fromHyperboloid x w) =
        InnerProductGeometry.angle v w) := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := (mfderiv I I fromHyperboloid x).toLinearMap.isometryOfInner (fromHyperboloid_preserves_metric x)
  exact ⟨L.norm_map, L.enorm_map, L.injective, fun v w _ _ => L.angle_map v w⟩

/-- The inverse coordinate map preserves ordinary real and extended C1 speeds for the stated metrics (G01.i/k). -/
theorem fromHyperboloid_speed (γ : ℝ → Hyperboloid) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I (fromHyperboloid ∘ γ) t (1 : ℝ)‖ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
    ‖mfderiv 𝓘(ℝ, ℝ) I (fromHyperboloid ∘ γ) t (1 : ℝ)‖ₑ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  exact speed_comp_of_tensorPreserving
    hyperboloidMetric upperHalfPlaneMetric fromHyperboloid contMDiff_fromHyperboloid
    fromHyperboloid_preserves_metric γ t hγ

/-- The inverse map preserves within speeds on the same parameter set, including strict-piece one-sided endpoints (G01.i/k). -/
theorem fromHyperboloid_speedWithin (γ : ℝ → Hyperboloid) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (fromHyperboloid ∘ γ) s t (1 : ℝ)‖ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (fromHyperboloid ∘ γ) s t (1 : ℝ)‖ₑ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  exact speedWithin_comp_of_tensorPreserving
    hyperboloidMetric upperHalfPlaneMetric fromHyperboloid contMDiff_fromHyperboloid
    fromHyperboloid_preserves_metric γ s t hγ hs

/-- Every upper-half-plane finite-piece C1 curve has a forward image with the same cuts, exact endpoints and equal finite real and extended whole and piece lengths (G01.j.7/k). -/
theorem toHyperboloid_length {γ : ℝ → UpperHalfPlane} {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let q : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)‖
    let q' : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I (toHyperboloid ∘ γ) (P i) t (1 : ℝ)‖
    IsPiecewiseC1On I (toHyperboloid ∘ γ) a b n cut ∧
    (toHyperboloid ∘ γ) a = toHyperboloid (γ a) ∧ (toHyperboloid ∘ γ) b = toHyperboloid (γ b) ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, q' i t) =
      ∫ t in cut i.castSucc..cut i.succ, q i t) ∧
    piecewiseC1Length hyperboloidMetric (toHyperboloid ∘ γ) cut = piecewiseC1Length upperHalfPlaneMetric γ cut ∧
    0 ≤ piecewiseC1Length upperHalfPlaneMetric γ cut ∧ 0 ≤ piecewiseC1Length hyperboloidMetric (toHyperboloid ∘ γ) cut ∧
    pathELength I (toHyperboloid ∘ γ) a b = pathELength I γ a b ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) ∧
    pathELength I (toHyperboloid ∘ γ) a b < (⊤ : ℝ≥0∞) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length upperHalfPlaneMetric γ cut) ∧
    pathELength I (toHyperboloid ∘ γ) a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric (toHyperboloid ∘ γ) cut) ∧
    (∀ i : Fin n,
      (∫⁻ t in P i, ENNReal.ofReal (q' i t)) =
        ∫⁻ t in P i, ENNReal.ofReal (q i t)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q i t)) < (⊤ : ℝ≥0∞)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) < (⊤ : ℝ≥0∞))
 := by
  exact hγ.length_comp_of_tensorPreserving upperHalfPlaneMetric hyperboloidMetric
    toHyperboloid contMDiff_toHyperboloid toHyperboloid_preserves_tangentTensor

/-- Every hyperboloid finite-piece C1 curve has an inverse image with the same cuts, exact endpoints and equal finite real and extended whole and piece lengths (G01.j.8/k). -/
theorem fromHyperboloid_length {γ : ℝ → Hyperboloid} {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let q : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)‖
    let q' : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I (fromHyperboloid ∘ γ) (P i) t (1 : ℝ)‖
    IsPiecewiseC1On I (fromHyperboloid ∘ γ) a b n cut ∧
    (fromHyperboloid ∘ γ) a = fromHyperboloid (γ a) ∧ (fromHyperboloid ∘ γ) b = fromHyperboloid (γ b) ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, q' i t) =
      ∫ t in cut i.castSucc..cut i.succ, q i t) ∧
    piecewiseC1Length upperHalfPlaneMetric (fromHyperboloid ∘ γ) cut = piecewiseC1Length hyperboloidMetric γ cut ∧
    0 ≤ piecewiseC1Length hyperboloidMetric γ cut ∧ 0 ≤ piecewiseC1Length upperHalfPlaneMetric (fromHyperboloid ∘ γ) cut ∧
    pathELength I (fromHyperboloid ∘ γ) a b = pathELength I γ a b ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) ∧
    pathELength I (fromHyperboloid ∘ γ) a b < (⊤ : ℝ≥0∞) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ cut) ∧
    pathELength I (fromHyperboloid ∘ γ) a b = ENNReal.ofReal (piecewiseC1Length upperHalfPlaneMetric (fromHyperboloid ∘ γ) cut) ∧
    (∀ i : Fin n,
      (∫⁻ t in P i, ENNReal.ofReal (q' i t)) =
        ∫⁻ t in P i, ENNReal.ofReal (q i t)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q i t)) < (⊤ : ℝ≥0∞)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) < (⊤ : ℝ≥0∞))
 := by
  exact hγ.length_comp_of_tensorPreserving hyperboloidMetric upperHalfPlaneMetric
    fromHyperboloid contMDiff_fromHyperboloid fromHyperboloid_preserves_metric

/-- The actual model equivalence bijects fixed-endpoint finite-piece curve families with unchanged subdivisions and equal finite lengths in both directions (G01.j.8/k). -/
theorem upperHalfPlaneDiffeomorphHyperboloid_curveFamily_length {a b : ℝ} {n : ℕ}
    {cut : Fin (n+1) → ℝ} {p q : UpperHalfPlane} :
    letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let Φ := PiecewiseC1CurveOn.mapEquiv (a := a) (b := b) (cut := cut) (p := p) (q := q) upperHalfPlaneDiffeomorphHyperboloid
    Function.Bijective Φ ∧
    (∀ γ : PiecewiseC1CurveOn I a b n cut p q,
      piecewiseC1Length hyperboloidMetric (Φ γ).val cut = piecewiseC1Length upperHalfPlaneMetric γ.val cut ∧
      pathELength I (Φ γ).val a b = pathELength I γ.val a b ∧
      pathELength I γ.val a b < (⊤ : ℝ≥0∞) ∧
      pathELength I (Φ γ).val a b < (⊤ : ℝ≥0∞) ∧
      (Φ γ).val a = upperHalfPlaneDiffeomorphHyperboloid p ∧ (Φ γ).val b = upperHalfPlaneDiffeomorphHyperboloid q) ∧
    (∀ η : PiecewiseC1CurveOn I a b n cut (upperHalfPlaneDiffeomorphHyperboloid p) (upperHalfPlaneDiffeomorphHyperboloid q),
      piecewiseC1Length upperHalfPlaneMetric (Φ.symm η).val cut = piecewiseC1Length hyperboloidMetric η.val cut ∧
      pathELength I (Φ.symm η).val a b = pathELength I η.val a b ∧
      pathELength I η.val a b < (⊤ : ℝ≥0∞) ∧
      pathELength I (Φ.symm η).val a b < (⊤ : ℝ≥0∞) ∧
      (Φ.symm η).val a = p ∧ (Φ.symm η).val b = q) ∧
    (∀ γ t, (Φ γ).val t = upperHalfPlaneDiffeomorphHyperboloid (γ.val t)) ∧
    (∀ η t, (Φ.symm η).val t = upperHalfPlaneDiffeomorphHyperboloid.symm (η.val t)) ∧
    (∀ γ, Φ.symm (Φ γ) = γ) ∧
    (∀ η, Φ (Φ.symm η) = η)
 := by
  exact PiecewiseC1CurveOn.mapEquiv_length upperHalfPlaneMetric hyperboloidMetric
    upperHalfPlaneDiffeomorphHyperboloid toHyperboloid_preserves_tangentTensor


/-! ## Intrinsic distance correspondence and actual finite witnesses (G01.l) -/

private theorem modelSegment_pos (u v : UpperHalfPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (AffineMap.lineMap (u : ℂ) (v : ℂ) t).im := by
  have hc : Convex ℝ {z : ℂ | 0 < z.im} :=
    (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).linear_preimage Complex.imLm
  exact hc.lineMap_mem u.im_pos v.im_pos ht


private theorem modelSegment_onePiece {γ : ℝ → UpperHalfPlane}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    IsPiecewiseC1On I γ 0 1 1 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) := by
  refine ⟨?_, by simp, by simp, hγ.continuousOn, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i hi
    fin_cases i
    simpa using hγ

/-- The canonical upper-half-plane segment is the real affine coordinate segment on the unit interval (G01.l). Values outside that interval are arbitrary chart-inverse values. -/
def upperHalfPlaneSegment (u v : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex (AffineMap.lineMap (u : ℂ) (v : ℂ) t)

/-- The canonical segment has literal affine coordinates, exact endpoints and real C1 regularity on the closed unit interval (G01.l); no global C1 extension is asserted. -/
theorem upperHalfPlaneSegment_properties (u v : UpperHalfPlane) :
  (∀ t ∈ Icc (0 : ℝ) 1, (upperHalfPlaneSegment u v t : ℂ) =
    AffineMap.lineMap (u : ℂ) (v : ℂ) t) ∧
  upperHalfPlaneSegment u v 0 = u ∧ upperHalfPlaneSegment u v 1 = v ∧
  ContMDiffOn 𝓘(ℝ, ℝ) I 1 (upperHalfPlaneSegment u v) (Icc 0 1) := by
  have hs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (upperHalfPlaneSegment u v) (Icc 0 1) := by
    have hg : ContMDiffOn I I 1 UpperHalfPlane.ofComplex
        (range (UpperHalfPlane.coe : UpperHalfPlane → ℂ)) :=
      contMDiffOn_isOpenEmbedding_symm UpperHalfPlane.isOpenEmbedding_coe
    have hf : ContMDiff 𝓘(ℝ, ℝ) I 1 (AffineMap.lineMap (u : ℂ) (v : ℂ) : ℝ → ℂ) :=
      (AffineMap.contDiff_lineMap (𝕜 := ℝ) (u : ℂ) (v : ℂ)).contMDiff
    exact hg.comp hf.contMDiffOn (fun t ht => ⟨⟨_, modelSegment_pos u v ht⟩, rfl⟩)
  refine ⟨?_, ?_, ?_, hs⟩
  · intro t ht
    simp only [upperHalfPlaneSegment, UpperHalfPlane.ofComplex_apply_of_im_pos (modelSegment_pos u v ht)]
  · simp [upperHalfPlaneSegment]
  · simp [upperHalfPlaneSegment]

/-- Every upper-half-plane pair admits the literal one-piece segment as a finite-length curve for the actual coordinate metric (G01.l). -/
theorem upperHalfPlane_exists_finiteCurve (u v : UpperHalfPlane) :
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  ∃ γ : PiecewiseC1CurveOn I 0 1 1 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) u v,
    γ.val = upperHalfPlaneSegment u v ∧
    0 ≤ piecewiseC1Length upperHalfPlaneMetric γ.val (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ∧
    pathELength I γ.val 0 1 =
      ENNReal.ofReal (piecewiseC1Length upperHalfPlaneMetric γ.val (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)) ∧
    pathELength I γ.val 0 1 < (⊤ : ℝ≥0∞) := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  rcases upperHalfPlaneSegment_properties u v with ⟨hcoe, h0, h1, hc⟩
  let γ : PiecewiseC1CurveOn I 0 1 1 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) u v :=
    ⟨upperHalfPlaneSegment u v, modelSegment_onePiece hc, h0, h1⟩
  rcases γ.property.1.speed_length upperHalfPlaneMetric with
    ⟨hi, hii, hm, hint, hr, hs, hn, hpi, hpf, hsum, hwhole, hpath, hfinite⟩
  exact ⟨γ, rfl, hn, hpath, hfinite⟩

/-- Every hyperboloid pair admits the forward image of the segment between its inverse coordinates, with exact endpoints and finite Lorentz-restriction length (G01.l). -/
theorem hyperboloid_exists_finiteCurve (p q : Hyperboloid) :
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  ∃ γ : PiecewiseC1CurveOn I 0 1 1 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) p q,
    γ.val = toHyperboloid ∘ upperHalfPlaneSegment (fromHyperboloid p) (fromHyperboloid q) ∧
    0 ≤ piecewiseC1Length hyperboloidMetric γ.val (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ∧
    pathELength I γ.val 0 1 =
      ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ.val (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)) ∧
    pathELength I γ.val 0 1 < (⊤ : ℝ≥0∞) := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  rcases upperHalfPlane_exists_finiteCurve (fromHyperboloid p) (fromHyperboloid q) with
    ⟨γ, hval, hn, hpath, hfinite⟩
  rcases toHyperboloid_length γ.property.1 with
    ⟨hc, ha, hb, hp, hr, hnU, hnQ, he, hfU, hfQ, hbrU, hbrQ, hpe, hpfU, hpfQ⟩
  let η : PiecewiseC1CurveOn I 0 1 1 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) p q :=
    ⟨toHyperboloid ∘ γ.val, hc, by simp [γ.property.2.1, toHyperboloid_fromHyperboloid],
      by simp [γ.property.2.2, toHyperboloid_fromHyperboloid]⟩
  exact ⟨η, congrArg (fun f => toHyperboloid ∘ f) hval, hnQ, hbrQ, hfQ⟩

/-- Forward transport of every admissible curve with unchanged interval and subdivision gives the first intrinsic finite-piece-distance inequality (G01.l). -/
theorem toHyperboloid_piecewiseC1EDist_le (u v : UpperHalfPlane) :
  piecewiseC1EDist hyperboloidMetric (toHyperboloid u) (toHyperboloid v) ≤
    piecewiseC1EDist upperHalfPlaneMetric u v := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  unfold piecewiseC1EDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun n => le_iInf fun cut =>
    le_iInf fun γ => ?_
  rcases toHyperboloid_length γ.property.1 with
    ⟨hc, ha, hb, hp, hr, hnU, hnQ, he, hfU, hfQ, hbrU, hbrQ, hpe, hpfU, hpfQ⟩
  let η : PiecewiseC1CurveOn I a b n cut (toHyperboloid u) (toHyperboloid v) :=
    ⟨toHyperboloid ∘ γ.val, hc, by simp [γ.property.2.1], by simp [γ.property.2.2]⟩
  exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le n
    (iInf_le_of_le cut (iInf_le_of_le η (le_of_eq (congrArg ENNReal.ofReal hr))))))

/-- Backward transport of every arbitrary target curve gives the inverse intrinsic finite-piece-distance inequality for the same metrics and curve family (G01.l). -/
theorem fromHyperboloid_piecewiseC1EDist_le (p q : Hyperboloid) :
  piecewiseC1EDist upperHalfPlaneMetric (fromHyperboloid p) (fromHyperboloid q) ≤
    piecewiseC1EDist hyperboloidMetric p q := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  unfold piecewiseC1EDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun n => le_iInf fun cut =>
    le_iInf fun γ => ?_
  rcases fromHyperboloid_length γ.property.1 with
    ⟨hc, ha, hb, hp, hr, hnQ, hnU, he, hfQ, hfU, hbrQ, hbrU, hpe, hpfQ, hpfU⟩
  let η : PiecewiseC1CurveOn I a b n cut (fromHyperboloid p) (fromHyperboloid q) :=
    ⟨fromHyperboloid ∘ γ.val, hc, by simp [γ.property.2.1], by simp [γ.property.2.2]⟩
  exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le n
    (iInf_le_of_le cut (iInf_le_of_le η (le_of_eq (congrArg ENNReal.ofReal hr))))))

/-- The actual segment witness makes both intrinsic distance conventions finite for every upper-half-plane pair (G01.l). -/
theorem upperHalfPlane_intrinsicEDist_finite (u v : UpperHalfPlane) :
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  piecewiseC1EDist upperHalfPlaneMetric u v < (⊤ : ℝ≥0∞) ∧
  riemannianEDist I u v < (⊤ : ℝ≥0∞) := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  rcases upperHalfPlane_exists_finiteCurve u v with ⟨γ, hγ⟩
  exact (piecewiseC1EDist_finite_of_curve upperHalfPlaneMetric γ).2.2

/-- The actual transported segment witness makes both intrinsic distance conventions finite for every hyperboloid pair (G01.l). -/
theorem hyperboloid_intrinsicEDist_finite (p q : Hyperboloid) :
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  piecewiseC1EDist hyperboloidMetric p q < (⊤ : ℝ≥0∞) ∧
  riemannianEDist I p q < (⊤ : ℝ≥0∞) := by
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  rcases hyperboloid_exists_finiteCurve p q with ⟨γ, hγ⟩
  exact (piecewiseC1EDist_finite_of_curve hyperboloidMetric γ).2.2

/-- The actual forward coordinates preserve the all-family finite-piece and C1 intrinsic extended distances, with both values finite and equal real values (G01.l). -/
theorem toHyperboloid_intrinsicEDist (u v : UpperHalfPlane) :
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  piecewiseC1EDist hyperboloidMetric (toHyperboloid u) (toHyperboloid v) =
    piecewiseC1EDist upperHalfPlaneMetric u v ∧
  riemannianEDist I (toHyperboloid u) (toHyperboloid v) = riemannianEDist I u v ∧
  riemannianEDist I u v < (⊤ : ℝ≥0∞) ∧
  riemannianEDist I (toHyperboloid u) (toHyperboloid v) < (⊤ : ℝ≥0∞) ∧
  (riemannianEDist I (toHyperboloid u) (toHyperboloid v)).toReal =
    (riemannianEDist I u v).toReal := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  have hle := toHyperboloid_piecewiseC1EDist_le u v
  have hge := fromHyperboloid_piecewiseC1EDist_le (toHyperboloid u) (toHyperboloid v)
  simp only [fromHyperboloid_toHyperboloid] at hge
  have hp := le_antisymm hle hge
  have he : riemannianEDist I (toHyperboloid u) (toHyperboloid v) = riemannianEDist I u v := by
    simpa only [piecewiseC1EDist_eq_riemannianEDist] using hp
  exact ⟨hp, he, (upperHalfPlane_intrinsicEDist_finite u v).2,
    (hyperboloid_intrinsicEDist_finite (toHyperboloid u) (toHyperboloid v)).2,
    congrArg ENNReal.toReal he⟩

/-- The actual inverse coordinates preserve both intrinsic distance conventions for arbitrary hyperboloid endpoints, with finite and equal real values (G01.l). -/
theorem fromHyperboloid_intrinsicEDist (p q : Hyperboloid) :
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  piecewiseC1EDist upperHalfPlaneMetric (fromHyperboloid p) (fromHyperboloid q) =
    piecewiseC1EDist hyperboloidMetric p q ∧
  riemannianEDist I (fromHyperboloid p) (fromHyperboloid q) = riemannianEDist I p q ∧
  riemannianEDist I p q < (⊤ : ℝ≥0∞) ∧
  riemannianEDist I (fromHyperboloid p) (fromHyperboloid q) < (⊤ : ℝ≥0∞) ∧
  (riemannianEDist I (fromHyperboloid p) (fromHyperboloid q)).toReal =
    (riemannianEDist I p q).toReal := by
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  have hle := fromHyperboloid_piecewiseC1EDist_le p q
  have hge := toHyperboloid_piecewiseC1EDist_le (fromHyperboloid p) (fromHyperboloid q)
  simp only [toHyperboloid_fromHyperboloid] at hge
  have hp := le_antisymm hle hge
  have he : riemannianEDist I (fromHyperboloid p) (fromHyperboloid q) = riemannianEDist I p q := by
    simpa only [piecewiseC1EDist_eq_riemannianEDist] using hp
  exact ⟨hp, he, (hyperboloid_intrinsicEDist_finite p q).2,
    (upperHalfPlane_intrinsicEDist_finite (fromHyperboloid p) (fromHyperboloid q)).2,
    congrArg ENNReal.toReal he⟩



/-! ## Independent positive Lorentz tangent plane (G02.a) -/

/-- The Lorentz-perpendicular equation gives the time component in terms of the spatial coordinates (G02.a/A01). -/
theorem lorentzKer_time_eq (p : Hyperboloid) (v : V)
    (hv : v ∈ (lorentzFunctional p.val).ker) :
    p.val 2 * v 2 = p.val 0 * v 0 + p.val 1 * v 1 := by
  have h : p.val 0 * v 0 + p.val 1 * v 1 - p.val 2 * v 2 = 0 := hv
  linarith

/-- Independent Cauchy–Schwarz on the two spatial coordinates gives a quantitative lower bound for the Lorentz quadratic form on the perpendicular plane (G02.a/A02). -/
theorem lorentzKer_quadratic_lowerBound (p : Hyperboloid) (v : V)
    (hv : v ∈ (lorentzFunctional p.val).ker) :
    (v 0 ^ 2 + v 1 ^ 2) / p.val 2 ^ 2 ≤ lorentzBilinear v v := by
  have hcs : (p.val 0 * v 0 + p.val 1 * v 1)^2 ≤
      (p.val 0^2 + p.val 1^2) * (v 0^2 + v 1^2) := by
    simpa [Fin.sum_univ_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 2 => p.val i.castSucc) (fun i : Fin 2 => v i.castSucc))
  rw [← lorentzKer_time_eq p v hv] at hcs
  have hmodel : p.val 2^2 = 1 + p.val 0^2 + p.val 1^2 := by
    nlinarith [p.property.1]
  apply (div_le_iff₀ (sq_pos_of_pos p.property.2)).2
  rw [lorentzBilinear_apply]
  nlinarith [congrArg (fun x : ℝ => x * (v 0^2 + v 1^2)) hmodel]

/-- The Lorentz quadratic form is nonnegative on the perpendicular plane, by its independent quantitative bound (G02.a/A03). -/
theorem lorentzKer_quadratic_nonneg (p : Hyperboloid) (v : V)
    (hv : v ∈ (lorentzFunctional p.val).ker) :
    0 ≤ lorentzBilinear v v := by
  exact (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)).trans
    (lorentzKer_quadratic_lowerBound p v hv)

/-- The independent bound and perpendicular equation show that only the zero perpendicular vector has zero Lorentz square (G02.a/A04). -/
theorem lorentzKer_quadratic_eq_zero_iff (p : Hyperboloid) (v : V)
    (hv : v ∈ (lorentzFunctional p.val).ker) :
    lorentzBilinear v v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have hdiv := lorentzKer_quadratic_lowerBound p v hv
    rw [hz] at hdiv
    have hsum : v 0^2 + v 1^2 ≤ 0 := by
      simpa using (div_le_iff₀ (sq_pos_of_pos p.property.2)).mp hdiv
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    have ht := lorentzKer_time_eq p v hv
    rw [h0, h1, mul_zero, mul_zero, add_zero] at ht
    have h2 : v 2 = 0 := (mul_eq_zero.mp ht).resolve_left (ne_of_gt p.property.2)
    ext i
    fin_cases i <;> assumption
  · rintro rfl
    simp

/-- The Lorentz restriction is strictly positive on nonzero perpendicular vectors, by the independent equality criterion (G02.a/A05). -/
theorem lorentzKer_quadratic_pos (p : Hyperboloid) (v : V)
    (hv : v ∈ (lorentzFunctional p.val).ker) (hne : v ≠ 0) :
    0 < lorentzBilinear v v := by
  exact lt_of_le_of_ne (lorentzKer_quadratic_nonneg p v hv)
    (fun he => hne ((lorentzKer_quadratic_eq_zero_iff p v hv).mp he.symm))

/-- The Lorentz functional is onto the real line because it takes the unit timelike center to minus one; rank-nullity gives a two-dimensional kernel (G02.a/A06). -/
theorem finrank_lorentzKer (p : Hyperboloid) :
    Module.finrank ℝ (lorentzFunctional p.val).ker = 2 := by
  have hself : lorentzFunctional p.val p.val = -1 := by
    simpa only [lorentzFunctional_apply, pow_two] using p.property.1
  have hsurj : Function.Surjective (lorentzFunctional p.val).toLinearMap := by
    intro r
    refine ⟨(-r) • p.val, ?_⟩
    change lorentzFunctional p.val ((-r) • p.val) = r
    rw [map_smul, hself]
    simp
  have hrange : (lorentzFunctional p.val).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrank : Module.finrank ℝ (lorentzFunctional p.val).toLinearMap.range +
      Module.finrank ℝ (lorentzFunctional p.val).ker = 3 := by
    simpa using (lorentzFunctional p.val).toLinearMap.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (lorentzFunctional p.val).toLinearMap.range = 1 := by
    rw [hrange]
    simp
  omega

/-- The same continuous Lorentz bilinear form restricted through both actual kernel inclusions; no norm or frame is chosen (G02.a/A07). -/
def lorentzKerBilinear (p : Hyperboloid) :
    (lorentzFunctional p.val).ker →L[ℝ] (lorentzFunctional p.val).ker →L[ℝ] ℝ :=
  lorentzBilinear.bilinearComp (lorentzFunctional p.val).ker.subtypeL
    (lorentzFunctional p.val).ker.subtypeL

/-- The actual perpendicular restriction is symmetric, nonnegative and positive definite, with its literal ambient evaluation (G02.a/A08). -/
theorem lorentzKerBilinear_properties (p : Hyperboloid) :
    (∀ v w, lorentzKerBilinear p v w = lorentzBilinear v.val w.val) ∧
    (∀ v w, lorentzKerBilinear p v w = lorentzKerBilinear p w v) ∧
    (∀ v, 0 ≤ lorentzKerBilinear p v v) ∧
    (∀ v, lorentzKerBilinear p v v = 0 ↔ v = 0) ∧
    (∀ v, v ≠ 0 → 0 < lorentzKerBilinear p v v) := by
  refine ⟨fun _ _ => rfl, fun _ _ => lorentzBilinear_symm _ _,
    fun v => lorentzKer_quadratic_nonneg p v.val v.property, ?_, ?_⟩
  · intro v
    exact (lorentzKer_quadratic_eq_zero_iff p v.val v.property).trans
      Submodule.coe_eq_zero
  · intro v hv
    exact lorentzKer_quadratic_pos p v.val v.property
      (fun h => hv (Subtype.val_injective h))

/-- The actual tangent inclusion identifies the perpendicular plane of dimension two, and carries the independent quantitative Lorentz bound and positive-definiteness to the stated intrinsic tensor (G02.a/A09). -/
theorem hyperboloid_tangent_lorentz_positive (p : Hyperboloid) :
    (mfderiv I J (fun q : Hyperboloid => q.val) p).range =
      (lorentzFunctional p.val).ker ∧
    Module.finrank ℝ (lorentzFunctional p.val).ker = 2 ∧
    (∀ v : TangentSpace I p,
      let w := (hyperboloidTangentEquivKer p v).val
      (w 0 ^ 2 + w 1 ^ 2) / p.val 2 ^ 2 ≤ hyperboloidTangentTensor p v v) ∧
    (∀ v : TangentSpace I p, 0 ≤ hyperboloidTangentTensor p v v) ∧
    (∀ v : TangentSpace I p, hyperboloidTangentTensor p v v = 0 ↔ v = 0) ∧
    (∀ v : TangentSpace I p, v ≠ 0 → 0 < hyperboloidTangentTensor p v v) := by
  have hTensor (v : TangentSpace I p) :
      hyperboloidTangentTensor p v v =
        lorentzBilinear (hyperboloidTangentEquivKer p v).val
          (hyperboloidTangentEquivKer p v).val := by
    rw [hyperboloidTangentTensor_apply]
    simp only [hyperboloidTangentEquivKer_apply]
  have hzero (v : TangentSpace I p) :
      (hyperboloidTangentEquivKer p v).val = 0 ↔ v = 0 := by
    rw [Submodule.coe_eq_zero]
    exact (hyperboloidTangentEquivKer p).map_eq_zero_iff
  refine ⟨range_mfderiv_hyperboloid_val p, finrank_lorentzKer p, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [hTensor]
    exact lorentzKer_quadratic_lowerBound p _ (hyperboloidTangentEquivKer p v).property
  · intro v
    rw [hTensor]
    exact lorentzKer_quadratic_nonneg p _ (hyperboloidTangentEquivKer p v).property
  · intro v
    rw [hTensor]
    exact (lorentzKer_quadratic_eq_zero_iff p _
      (hyperboloidTangentEquivKer p v).property).trans (hzero v)
  · intro v hv
    rw [hTensor]
    exact lorentzKer_quadratic_pos p _ (hyperboloidTangentEquivKer p v).property
      (fun h => hv ((hzero v).mp h))



/-! ## Lorentz frames and algebraic changes of center (G02.b/c) -/

/-- Positive Core of the actual independent Lorentz restriction (G02.b/F01). -/
def lorentzPlaneCore (p : Hyperboloid) :
    InnerProductSpace.Core ℝ (lorentzFunctional p.val).ker where
  inner := fun v w => lorentzKerBilinear p v w
  conj_inner_symm := fun v w => (lorentzKerBilinear_properties p).2.1 w v
  re_inner_nonneg := (lorentzKerBilinear_properties p).2.2.1
  add_left := fun v w z => congrArg
    (fun f : (lorentzFunctional p.val).ker →L[ℝ] ℝ => f z)
    (map_add (lorentzKerBilinear p) v w)
  smul_left := fun v w r => congrArg
    (fun f : (lorentzFunctional p.val).ker →L[ℝ] ℝ => f w)
    (map_smul (lorentzKerBilinear p) r v)
  definite := fun v hv => (lorentzKerBilinear_properties p).2.2.2.1 v |>.mp hv

/-- Ordinary orthogonalization in the positive perpendicular plane, exported as an algebraic two-vector basis (G02.b/F02). -/
def lorentzPlaneBasis (p : Hyperboloid) :
    Module.Basis (Fin 2) ℝ (lorentzFunctional p.val).ker := by
  let c := lorentzPlaneCore p
  letI : InnerProductSpace.Core ℝ (lorentzFunctional p.val).ker := c
  let n : NormedAddCommGroup (lorentzFunctional p.val).ker :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup (lorentzFunctional p.val).ker := n
  letI : SeminormedAddCommGroup (lorentzFunctional p.val).ker :=
    n.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (lorentzFunctional p.val).ker :=
    InnerProductSpace.ofCore c.toCore
  exact (stdOrthonormalBasis ℝ (lorentzFunctional p.val).ker).toBasis.reindex
    (finCongr (finrank_lorentzKer p))

/-- The selected positive-plane basis is orthonormal for the same Lorentz form (G02.b/F03). -/
theorem lorentzPlaneBasis_gram (p : Hyperboloid) (i j : Fin 2) :
    lorentzBilinear (lorentzPlaneBasis p i).val (lorentzPlaneBasis p j).val =
      if i = j then 1 else 0 := by
  let c := lorentzPlaneCore p
  letI : InnerProductSpace.Core ℝ (lorentzFunctional p.val).ker := c
  let n : NormedAddCommGroup (lorentzFunctional p.val).ker :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup (lorentzFunctional p.val).ker := n
  letI : SeminormedAddCommGroup (lorentzFunctional p.val).ker := n.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (lorentzFunctional p.val).ker :=
    InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℝ (lorentzFunctional p.val).ker
  let e := finCongr (finrank_lorentzKer p)
  have h := b.inner_eq_ite (e.symm i) (e.symm j)
  change lorentzBilinear (b (e.symm i)).val (b (e.symm j)).val =
    (if e.symm i = e.symm j then 1 else 0) at h
  simpa only [lorentzPlaneBasis, Module.Basis.reindex_apply,
    OrthonormalBasis.coe_toBasis, Equiv.apply_eq_iff_eq] using h

/-- The actual sum map adjoining the timelike center to its perpendicular plane (G02.b/F04). -/
def lorentzSumMap (p : Hyperboloid) :
    ((lorentzFunctional p.val).ker × ℝ) →ₗ[ℝ] V :=
  (lorentzFunctional p.val).ker.subtype.coprod (LinearMap.toSpanSingleton ℝ V p.val)

/-- The perpendicular plane and center line are complementary, with unique decomposition and explicit projection and scalar components (G02.b/F05). -/
theorem lorentz_directSum (p : Hyperboloid) :
    IsCompl (lorentzFunctional p.val).ker (Submodule.span ℝ {p.val}) ∧
    (∀ w : V, ∃! z : (lorentzFunctional p.val).ker × ℝ,
      z.1.val + z.2 • p.val = w) ∧
    (∀ (w : V) (z : (lorentzFunctional p.val).ker × ℝ),
      z.1.val + z.2 • p.val = w →
      z.1.val = w + lorentzBilinear p.val w • p.val ∧
      z.2 = -lorentzBilinear p.val w) := by
  have hself : lorentzFunctional p.val p.val = -1 := by
    simpa only [lorentzFunctional_apply, pow_two] using p.property.1
  have hmem (w : V) :
      w + lorentzBilinear p.val w • p.val ∈ (lorentzFunctional p.val).ker := by
    change lorentzFunctional p.val (w + lorentzBilinear p.val w • p.val) = 0
    rw [map_add, map_smul, hself, lorentzBilinear_eq_functional]
    simp
  have hcomponents (w : V) (z : (lorentzFunctional p.val).ker × ℝ)
      (hz : z.1.val + z.2 • p.val = w) :
      z.1.val = w + lorentzBilinear p.val w • p.val ∧
      z.2 = -lorentzBilinear p.val w := by
    have hzker : lorentzFunctional p.val z.1.val = 0 := z.1.property
    have ht := congrArg (lorentzFunctional p.val) hz
    rw [map_add, map_smul, hzker, hself] at ht
    have hc : z.2 = -lorentzBilinear p.val w := by
      rw [lorentzBilinear_eq_functional]
      simpa using congrArg Neg.neg ht
    refine ⟨?_, hc⟩
    calc
      z.1.val = (z.1.val + z.2 • p.val) + lorentzBilinear p.val w • p.val := by
        rw [hc]
        simp
      _ = w + lorentzBilinear p.val w • p.val := by rw [hz]
  have hex (w : V) : ∃! z : (lorentzFunctional p.val).ker × ℝ,
      z.1.val + z.2 • p.val = w := by
    let z : (lorentzFunctional p.val).ker × ℝ :=
      (⟨w + lorentzBilinear p.val w • p.val, hmem w⟩, -lorentzBilinear p.val w)
    have hz : z.1.val + z.2 • p.val = w := by
      dsimp [z]
      simp
    refine ⟨z, hz, ?_⟩
    intro z' hz'
    obtain ⟨hv, ht⟩ := hcomponents w z' hz'
    exact Prod.ext (Subtype.ext hv) ht
  have hd : Disjoint (lorentzFunctional p.val).ker (Submodule.span ℝ {p.val}) := by
    rw [Submodule.disjoint_def]
    intro w hw hs
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hs
    change lorentzFunctional p.val (r • p.val) = 0 at hw
    rw [map_smul, hself] at hw
    have hr : r = 0 := by simpa using hw
    simp [hr]
  have hs : (lorentzFunctional p.val).ker ⊔ Submodule.span ℝ {p.val} = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨z, hz, _⟩ := hex w
    exact Submodule.mem_sup.mpr ⟨z.1.val, z.1.property, z.2 • p.val,
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)), hz⟩
  exact ⟨⟨hd, codisjoint_iff.mpr hs⟩, hex, hcomponents⟩

/-- Unique decomposition makes the actual sum map bijective (G02.b/F06). -/
theorem lorentzSumMap_bijective (p : Hyperboloid) :
    Function.Bijective (lorentzSumMap p) := by
  apply (Function.bijective_iff_existsUnique _).mpr
  exact (lorentz_directSum p).2.1

/-- The linear equivalence of the actual perpendicular-plane and scalar direct sum (G02.b/F07). -/
def lorentzSumEquiv (p : Hyperboloid) :
    ((lorentzFunctional p.val).ker × ℝ) ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (lorentzSumMap p) (lorentzSumMap_bijective p)

/-- The same orthonormal plane basis, with the center adjoined in the third position (G02.b/F08). -/
def lorentzFrameBasis (p : Hyperboloid) : Module.Basis (Fin 3) ℝ V :=
  (((lorentzPlaneBasis p).prod (Module.Basis.singleton (Fin 1) ℝ)).map
    (lorentzSumEquiv p)).reindex finSumFinEquiv

/-- The adjoined ambient basis has exactly the two selected plane vectors followed by the center (G02.b/F09). -/
theorem lorentzFrameBasis_apply (p : Hyperboloid) :
    (∀ i : Fin 2, lorentzFrameBasis p i.castSucc = (lorentzPlaneBasis p i).val) ∧
    lorentzFrameBasis p 2 = p.val := by
  constructor
  · intro i
    simp [lorentzFrameBasis, Module.Basis.reindex_apply,
      Module.Basis.map_apply, lorentzSumEquiv, lorentzSumMap,
      Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd]
  · have he : finSumFinEquiv.symm (2 : Fin 3) = Sum.inr (0 : Fin 1) := by decide
    simp only [lorentzFrameBasis, Module.Basis.reindex_apply, he]
    simp [Module.Basis.map_apply, lorentzSumEquiv, lorentzSumMap]

/-- The ambient frame has Lorentz Gram matrix diag(1,1,-1), without an orientation condition (G02.b/F10). -/
theorem lorentzFrameBasis_gram (p : Hyperboloid) (i j : Fin 3) :
    lorentzBilinear (lorentzFrameBasis p i) (lorentzFrameBasis p j) =
      if i = j then (if i = 2 then -1 else 1) else 0 := by
  have h0 : lorentzFrameBasis p 0 = (lorentzPlaneBasis p 0).val := by
    simpa using (lorentzFrameBasis_apply p).1 0
  have h1 : lorentzFrameBasis p 1 = (lorentzPlaneBasis p 1).val := by
    simpa using (lorentzFrameBasis_apply p).1 1
  have h2 := (lorentzFrameBasis_apply p).2
  have hcross (i : Fin 2) : lorentzBilinear p.val (lorentzPlaneBasis p i).val = 0 := by
    rw [lorentzBilinear_eq_functional]
    exact (lorentzPlaneBasis p i).property
  have hcross' (i : Fin 2) : lorentzBilinear (lorentzPlaneBasis p i).val p.val = 0 := by
    rw [lorentzBilinear_symm]
    exact hcross i
  have hself : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  fin_cases i <;> fin_cases j <;>
    simp [h0, h1, h2, lorentzPlaneBasis_gram, hcross, hcross', hself]

/-- Linear coordinates in the same actual Lorentz frame (G02.c/F11). -/
def lorentzCenterCoordinates (p : Hyperboloid) : V ≃ₗ[ℝ] V :=
  (lorentzFrameBasis p).equivFun

/-- Same-frame coordinates have the explicit inverse sum, all basis images, exact center and both inverse laws (G02.c/F12). -/
theorem lorentzCenterCoordinates_properties (p : Hyperboloid) :
    (∀ w : V, (lorentzCenterCoordinates p).symm w =
      w 0 • (lorentzPlaneBasis p 0).val +
      w 1 • (lorentzPlaneBasis p 1).val + w 2 • p.val) ∧
    (∀ i : Fin 3, lorentzCenterCoordinates p (lorentzFrameBasis p i) =
      Pi.single i 1) ∧
    (∀ i : Fin 3, (lorentzCenterCoordinates p).symm (Pi.single i 1) =
      lorentzFrameBasis p i) ∧
    lorentzCenterCoordinates p p.val = ![0, 0, 1] ∧
    (lorentzCenterCoordinates p).symm ![0, 0, 1] = p.val ∧
    (∀ w : V, (lorentzCenterCoordinates p).symm (lorentzCenterCoordinates p w) = w) ∧
    (∀ w : V, lorentzCenterCoordinates p ((lorentzCenterCoordinates p).symm w) = w) := by
  have material_inverse (p : Hyperboloid) (w : V) :
      (lorentzCenterCoordinates p).symm w =
        w 0 • (lorentzPlaneBasis p 0).val +
        w 1 • (lorentzPlaneBasis p 1).val + w 2 • p.val := by
    unfold lorentzCenterCoordinates
    rw [(lorentzFrameBasis p).equivFun_symm_apply]
    simp only [Fin.sum_univ_three]
    have h0 : lorentzFrameBasis p 0 = (lorentzPlaneBasis p 0).val := by
      simpa using (lorentzFrameBasis_apply p).1 0
    have h1 : lorentzFrameBasis p 1 = (lorentzPlaneBasis p 1).val := by
      simpa using (lorentzFrameBasis_apply p).1 1
    rw [h0, h1, (lorentzFrameBasis_apply p).2]

  have material_basis (p : Hyperboloid) (i : Fin 3) :
      lorentzCenterCoordinates p (lorentzFrameBasis p i) = Pi.single i 1 := by
    ext j
    simp [lorentzCenterCoordinates, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

  have material_basisInverse (p : Hyperboloid) (i : Fin 3) :
      (lorentzCenterCoordinates p).symm (Pi.single i 1) = lorentzFrameBasis p i := by
    apply (lorentzCenterCoordinates p).injective
    ext j
    simp [lorentzCenterCoordinates, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hsingle : (Pi.single (2 : Fin 3) (1 : ℝ)) = ![0,0,1] := by
    ext i
    fin_cases i <;> simp [Pi.single_apply]
  have hCenter : lorentzCenterCoordinates p p.val = ![0,0,1] := by
    rw [← (lorentzFrameBasis_apply p).2, material_basis, hsingle]
  have hCenterInv : (lorentzCenterCoordinates p).symm ![0,0,1] = p.val := by
    rw [← hsingle, material_basisInverse, (lorentzFrameBasis_apply p).2]
  exact ⟨material_inverse p, material_basis p, material_basisInverse p, hCenter, hCenterInv,
    (lorentzCenterCoordinates p).symm_apply_apply,
    (lorentzCenterCoordinates p).apply_symm_apply⟩

/-- The time coordinate of the centering map is minus pairing with the original center (G02.c/F13). -/
theorem lorentzCenterCoordinates_time (p : Hyperboloid) (w : V) :
    lorentzCenterCoordinates p w 2 = -lorentzBilinear p.val w := by
  have hcross (i : Fin 2) : lorentzBilinear p.val (lorentzPlaneBasis p i).val = 0 := by
    rw [lorentzBilinear_eq_functional]
    exact (lorentzPlaneBasis p i).property
  have hself : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hw := (lorentzCenterCoordinates_properties p).1 (lorentzCenterCoordinates p w)
  rw [(lorentzCenterCoordinates p).symm_apply_apply] at hw
  have h := congrArg (lorentzBilinear p.val) hw
  simp only [map_add, map_smul, smul_eq_mul, hcross, hself, mul_zero,
    zero_add, mul_neg, mul_one] at h
  linarith

/-- The same-frame centering coordinates preserve the full Lorentz bilinear form (G02.c/F14). -/
theorem lorentzCenterCoordinates_preserves (p : Hyperboloid) (u v : V) :
    lorentzBilinear (lorentzCenterCoordinates p u) (lorentzCenterCoordinates p v) =
      lorentzBilinear u v := by
  have hexpand (r s : V) :
      lorentzBilinear (∑ i : Fin 3, r i • lorentzFrameBasis p i)
        (∑ j : Fin 3, s j • lorentzFrameBasis p j) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        r i * s j * lorentzBilinear (lorentzFrameBasis p i) (lorentzFrameBasis p j) := by
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    ring
  have hgram (r s : V) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        r i * s j * lorentzBilinear (lorentzFrameBasis p i) (lorentzFrameBasis p j)) =
      lorentzBilinear r s := by
    simp_rw [lorentzFrameBasis_gram]
    simp [Fin.sum_univ_three, lorentzBilinear_apply]
    ring
  have h := (hexpand (lorentzCenterCoordinates p u) (lorentzCenterCoordinates p v)).trans
    (hgram (lorentzCenterCoordinates p u) (lorentzCenterCoordinates p v))
  have hu : ∑ i, lorentzCenterCoordinates p u i • lorentzFrameBasis p i = u :=
    (lorentzFrameBasis p).sum_equivFun u
  have hv : ∑ i, lorentzCenterCoordinates p v i • lorentzFrameBasis p i = v :=
    (lorentzFrameBasis p).sum_equivFun v
  rw [hu, hv] at h
  exact h.symm

/-- The inverse centering coordinates preserve the full Lorentz bilinear form (G02.c/F15). -/
theorem lorentzCenterCoordinates_symm_preserves (p : Hyperboloid) (u v : V) :
    lorentzBilinear ((lorentzCenterCoordinates p).symm u)
      ((lorentzCenterCoordinates p).symm v) = lorentzBilinear u v := by
  simpa using (lorentzCenterCoordinates_preserves p
    ((lorentzCenterCoordinates p).symm u) ((lorentzCenterCoordinates p).symm v)).symm



/-! ## Upper-sheet changes of center (G02.d/e) -/

/-- The time coordinate of a unit timelike vector on either sheet is nonzero (G02.d/D01). -/
theorem lorentzUnit_time_ne_zero (q : V)
    (hq : lorentzBilinear q q = -1) : q 2 ≠ 0 := by
  intro ht
  have he : q 0^2 + q 1^2 - q 2^2 = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using hq
  rw [ht] at he
  nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]

/-- Independent spatial Cauchy–Schwarz gives the strict time-product bound on the upper sheet (G02.d/D02). -/
theorem hyperboloid_spatial_dot_lt_time_mul (p q : Hyperboloid) :
    p.val 0 * q.val 0 + p.val 1 * q.val 1 < p.val 2 * q.val 2 := by
  have hcs :
      (p.val 0*q.val 0+p.val 1*q.val 1)^2 ≤
        (p.val 0^2+p.val 1^2)*(q.val 0^2+q.val 1^2) := by
    simpa [Fin.sum_univ_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 2 => p.val i.castSucc)
        (fun i : Fin 2 => q.val i.castSucc))
  have hp : p.val 2^2 = p.val 0^2+p.val 1^2+1 := by
    linarith [p.property.1]
  have hq : q.val 2^2 = q.val 0^2+q.val 1^2+1 := by
    linarith [q.property.1]
  have hgap :
      (p.val 2*q.val 2)^2 -
        (p.val 0^2+p.val 1^2)*(q.val 0^2+q.val 1^2) =
      p.val 0^2+p.val 1^2+q.val 0^2+q.val 1^2+1 := by
    rw [mul_pow, hp, hq]
    ring
  have hstrict :
      (p.val 0*q.val 0+p.val 1*q.val 1)^2 < (p.val 2*q.val 2)^2 := by
    nlinarith [sq_nonneg (p.val 0), sq_nonneg (p.val 1),
      sq_nonneg (q.val 0), sq_nonneg (q.val 1)]
  exact (abs_lt_of_sq_lt_sq' hstrict (mul_pos p.property.2 q.property.2).le).2

/-- Two upper-sheet points have strictly negative Lorentz pairing (G02.d/D03). -/
theorem hyperboloid_neg_lorentz_pos (p q : Hyperboloid) :
    0 < -lorentzBilinear p.val q.val := by
  have h := hyperboloid_spatial_dot_lt_time_mul p q
  rw [lorentzBilinear_apply]
  linarith

/-- A fixed upper-sheet point detects the time sign on either unit sheet, with both nonzeros (G02.d/D04). -/
theorem lorentzUnit_time_sign (p : Hyperboloid) (q : V)
    (hq : lorentzBilinear q q = -1) :
    q 2 ≠ 0 ∧ -lorentzBilinear p.val q ≠ 0 ∧
      (0 < q 2 ↔ 0 < -lorentzBilinear p.val q) := by
  have hn := lorentzUnit_time_ne_zero q hq
  by_cases ht : 0 < q 2
  · let r : Hyperboloid :=
      ⟨q, by simpa only [lorentzBilinear_apply, pow_two] using hq, ht⟩
    have hl : 0 < -lorentzBilinear p.val q := hyperboloid_neg_lorentz_pos p r
    exact ⟨hn, ne_of_gt hl, iff_of_true ht hl⟩
  · have hlt : q 2 < 0 := lt_of_le_of_ne (le_of_not_gt ht) hn
    let r : Hyperboloid :=
      ⟨-q, by
        simpa only [Pi.neg_apply, neg_sq, lorentzBilinear_apply, pow_two,
          neg_mul_neg] using hq, neg_pos.mpr hlt⟩
    have hneg : 0 < -lorentzBilinear p.val (-q) := hyperboloid_neg_lorentz_pos p r
    rw [map_neg] at hneg
    have hl : -lorentzBilinear p.val q < 0 := by linarith
    exact ⟨hn, ne_of_lt hl, iff_of_false ht (not_lt_of_ge hl.le)⟩

/-- The actual frame coordinates carry the upper unit sheet into itself (G02.e/E01). -/
theorem lorentzCenterCoordinates_mem (p q : Hyperboloid) :
    (lorentzCenterCoordinates p q.val) 0 ^ 2 +
      (lorentzCenterCoordinates p q.val) 1 ^ 2 -
      (lorentzCenterCoordinates p q.val) 2 ^ 2 = -1 ∧
    0 < (lorentzCenterCoordinates p q.val) 2 := by
  constructor
  · have hu : lorentzBilinear (lorentzCenterCoordinates p q.val)
        (lorentzCenterCoordinates p q.val) = -1 := by
      rw [lorentzCenterCoordinates_preserves]
      simpa only [lorentzBilinear_apply, pow_two] using q.property.1
    simpa only [lorentzBilinear_apply, pow_two] using hu
  · rw [lorentzCenterCoordinates_time]
    exact (lorentzUnit_time_sign p q.val
      (by simpa only [lorentzBilinear_apply, pow_two] using q.property.1)).2.2.mp
        q.property.2

/-- The same inverse frame coordinates carry the upper unit sheet into itself (G02.e/E02). -/
theorem lorentzCenterCoordinates_symm_mem (p q : Hyperboloid) :
    ((lorentzCenterCoordinates p).symm q.val) 0 ^ 2 +
      ((lorentzCenterCoordinates p).symm q.val) 1 ^ 2 -
      ((lorentzCenterCoordinates p).symm q.val) 2 ^ 2 = -1 ∧
    0 < ((lorentzCenterCoordinates p).symm q.val) 2 := by
  have hu : lorentzBilinear ((lorentzCenterCoordinates p).symm q.val)
      ((lorentzCenterCoordinates p).symm q.val) = -1 := by
    rw [lorentzCenterCoordinates_symm_preserves]
    simpa only [lorentzBilinear_apply, pow_two] using q.property.1
  constructor
  · simpa only [lorentzBilinear_apply, pow_two] using hu
  · apply (lorentzUnit_time_sign p _ hu).2.2.mpr
    rw [← lorentzCenterCoordinates_time, LinearEquiv.apply_symm_apply]
    exact q.property.2

/-- Change of center on the actual upper sheet, by restriction of the selected frame coordinates (G02.e/E03). -/
def centerHyperboloid (p q : Hyperboloid) : Hyperboloid :=
  ⟨lorentzCenterCoordinates p q.val, lorentzCenterCoordinates_mem p q⟩

/-- Inverse change of center on the actual upper sheet, using the same ambient inverse (G02.e/E04). -/
def uncenterHyperboloid (p q : Hyperboloid) : Hyperboloid :=
  ⟨(lorentzCenterCoordinates p).symm q.val, lorentzCenterCoordinates_symm_mem p q⟩

/-- The two sheet restrictions retain their literal ambient values, inverse and center laws, and are onto (G02.e/E05). -/
theorem centerHyperboloid_properties (p : Hyperboloid) :
    (∀ q, (centerHyperboloid p q).val = lorentzCenterCoordinates p q.val) ∧
    (∀ q, (uncenterHyperboloid p q).val = (lorentzCenterCoordinates p).symm q.val) ∧
    (∀ q, uncenterHyperboloid p (centerHyperboloid p q) = q) ∧
    (∀ q, centerHyperboloid p (uncenterHyperboloid p q) = q) ∧
    (centerHyperboloid p p).val = ![0,0,1] ∧
    uncenterHyperboloid p ⟨![0,0,1], by change (0:ℝ)^2+0^2-1^2=-1; norm_num, by change (0:ℝ)<1; norm_num⟩ = p ∧
    Function.Surjective (centerHyperboloid p) ∧
    Function.Surjective (uncenterHyperboloid p) := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    apply Subtype.ext
    exact (lorentzCenterCoordinates p).symm_apply_apply q.val
  · intro q
    apply Subtype.ext
    exact (lorentzCenterCoordinates p).apply_symm_apply q.val
  · exact (lorentzCenterCoordinates_properties p).2.2.2.1
  · apply Subtype.ext
    exact (lorentzCenterCoordinates_properties p).2.2.2.2.1
  · intro q
    refine ⟨uncenterHyperboloid p q, ?_⟩
    apply Subtype.ext
    exact (lorentzCenterCoordinates p).apply_symm_apply q.val
  · intro q
    refine ⟨centerHyperboloid p q, ?_⟩
    apply Subtype.ext
    exact (lorentzCenterCoordinates p).symm_apply_apply q.val

/-- The same two sheet restrictions form an equivalence (G02.e/E06). -/
def centerHyperboloidEquiv (p : Hyperboloid) : Hyperboloid ≃ Hyperboloid where
  toFun := centerHyperboloid p
  invFun := uncenterHyperboloid p
  left_inv := (centerHyperboloid_properties p).2.2.1
  right_inv := (centerHyperboloid_properties p).2.2.2.1

/-- For a fixed center, its actual sheet change is smooth in the existing singleton atlas (G02.e/E07). -/
theorem contMDiff_centerHyperboloid (p : Hyperboloid) :
    ContMDiff I I ∞ (centerHyperboloid p) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  have hA : ContMDiff I J ∞ (fun q : Hyperboloid => lorentzCenterCoordinates p q.val) :=
    (lorentzCenterCoordinates p).toContinuousLinearEquiv.contDiff.comp_contMDiff
      contMDiff_hyperboloid_val
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.contMDiffOn.comp_contMDiff hA
    (fun q => hyperboloid_denominator_pos (centerHyperboloid p q))

/-- For a fixed center, the same inverse sheet change is smooth in the existing singleton atlas (G02.e/E08). -/
theorem contMDiff_uncenterHyperboloid (p : Hyperboloid) :
    ContMDiff I I ∞ (uncenterHyperboloid p) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  have hA : ContMDiff I J ∞ (fun q : Hyperboloid => (lorentzCenterCoordinates p).symm q.val) :=
    (lorentzCenterCoordinates p).symm.toContinuousLinearEquiv.contDiff.comp_contMDiff
      contMDiff_hyperboloid_val
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.contMDiffOn.comp_contMDiff hA
    (fun q => hyperboloid_denominator_pos (uncenterHyperboloid p q))

/-! ## Intrinsic metric and finite-piece curve transport under change of center -/

/-- Changing center is a smooth equivalence of the upper hyperboloid, for a fixed center. -/
def centerHyperboloidDiffeomorph (p : Hyperboloid) : Hyperboloid ≃ₘ⟮I, I⟯ Hyperboloid :=
  { centerHyperboloidEquiv p with
    contMDiff_toFun := contMDiff_centerHyperboloid p
    contMDiff_invFun := contMDiff_uncenterHyperboloid p }

/-- The intrinsic differential of the center change agrees with its ambient Lorentz-linear map. -/
theorem mfderiv_centerHyperboloid_val (p q : Hyperboloid) (v : TangentSpace I q) :
    mfderiv I J (fun r : Hyperboloid => r.val) (centerHyperboloid p q)
      (mfderiv I I (centerHyperboloid p) q v) =
    lorentzCenterCoordinates p (mfderiv I J (fun r : Hyperboloid => r.val) q v) := by
  let A : V ≃L[ℝ] V := (lorentzCenterCoordinates p).toContinuousLinearEquiv
  have hf := (contMDiff_centerHyperboloid p).mdifferentiable (by simp)
  have hi := contMDiff_hyperboloid_val.mdifferentiable (by simp)
  have hA : MDifferentiable J J (A : V → V) :=
    (A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hleft := mfderiv_comp_apply q (hi (centerHyperboloid p q)) (hf q) v
  have hright := mfderiv_comp_apply q (hA q.val) (hi q) v
  have hfun : (fun r : Hyperboloid => r.val) ∘ centerHyperboloid p =
      (A : V → V) ∘ (fun r : Hyperboloid => r.val) := rfl
  have hcongr :
      mfderiv I J ((fun r : Hyperboloid => r.val) ∘ centerHyperboloid p) q =
      mfderiv I J ((A : V → V) ∘ (fun r : Hyperboloid => r.val)) q :=
    mfderiv_congr hfun
  have hderiv : mfderiv J J (A : V → V) q.val = A.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact A.toContinuousLinearMap.fderiv
  have heq := hleft.symm.trans ((congrArg (fun L => L v) hcongr).trans hright)
  rw [hderiv] at heq
  exact heq

/-- The inverse center change has the ambient inverse Lorentz-linear differential. -/
theorem mfderiv_uncenterHyperboloid_val (p q : Hyperboloid) (v : TangentSpace I q) :
    mfderiv I J (fun r : Hyperboloid => r.val) (uncenterHyperboloid p q)
      (mfderiv I I (uncenterHyperboloid p) q v) =
    (lorentzCenterCoordinates p).symm (mfderiv I J (fun r : Hyperboloid => r.val) q v) := by
  let A : V ≃L[ℝ] V := (lorentzCenterCoordinates p).symm.toContinuousLinearEquiv
  have hf := (contMDiff_uncenterHyperboloid p).mdifferentiable (by simp)
  have hi := contMDiff_hyperboloid_val.mdifferentiable (by simp)
  have hA : MDifferentiable J J (A : V → V) :=
    (A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hleft := mfderiv_comp_apply q (hi (uncenterHyperboloid p q)) (hf q) v
  have hright := mfderiv_comp_apply q (hA q.val) (hi q) v
  have hfun : (fun r : Hyperboloid => r.val) ∘ uncenterHyperboloid p =
      (A : V → V) ∘ (fun r : Hyperboloid => r.val) := rfl
  have hcongr :
      mfderiv I J ((fun r : Hyperboloid => r.val) ∘ uncenterHyperboloid p) q =
      mfderiv I J ((A : V → V) ∘ (fun r : Hyperboloid => r.val)) q :=
    mfderiv_congr hfun
  have hderiv : mfderiv J J (A : V → V) q.val = A.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact A.toContinuousLinearMap.fderiv
  have heq := hleft.symm.trans ((congrArg (fun L => L v) hcongr).trans hright)
  rw [hderiv] at heq
  exact heq

/-- The two intrinsic differentials are mutual inverses at their actual image bases. -/
theorem centerHyperboloid_mfderiv_inverse (p q : Hyperboloid) :
    uncenterHyperboloid p (centerHyperboloid p q) = q ∧
    (mfderiv I I (uncenterHyperboloid p) (centerHyperboloid p q)).comp
      (mfderiv I I (centerHyperboloid p) q) = ContinuousLinearMap.id ℝ (TangentSpace I q) ∧
    centerHyperboloid p (uncenterHyperboloid p q) = q ∧
    (mfderiv I I (centerHyperboloid p) (uncenterHyperboloid p q)).comp
      (mfderiv I I (uncenterHyperboloid p) q) = ContinuousLinearMap.id ℝ (TangentSpace I q) ∧
    Function.Bijective (mfderiv I I (centerHyperboloid p) q) ∧
    Function.Bijective (mfderiv I I (uncenterHyperboloid p) q) := by
  let e := centerHyperboloidDiffeomorph p
  have hl := mfderiv_symm_comp_of_diffeomorph e q
  have hr := mfderiv_comp_symm_of_diffeomorph e q
  have hrf := (mfderiv_comp_symm_of_diffeomorph e (e q)).2
  have hlg := (mfderiv_symm_comp_of_diffeomorph e (e.symm q)).2
  rw [e.symm_apply_apply] at hrf
  rw [e.apply_symm_apply] at hlg
  have lf : Function.LeftInverse (mfderiv I I e.symm (e q)) (mfderiv I I e q) :=
    fun v => congrArg (fun L => L v) hl.2
  have rf : Function.RightInverse (mfderiv I I e.symm (e q)) (mfderiv I I e q) :=
    fun v => congrArg (fun L => L v) hrf
  have lg : Function.LeftInverse (mfderiv I I e (e.symm q)) (mfderiv I I e.symm q) :=
    fun v => congrArg (fun L => L v) hr.2
  have rg : Function.RightInverse (mfderiv I I e (e.symm q)) (mfderiv I I e.symm q) :=
    fun v => congrArg (fun L => L v) hlg
  exact ⟨hl.1, hl.2, hr.1, hr.2, ⟨lf.injective, rf.surjective⟩, ⟨lg.injective, rg.surjective⟩⟩

/-- Center change transports the actual Lorentz-perpendicular tangent kernels bijectively. -/
theorem centerHyperboloid_kernel_transport (p q : Hyperboloid) :
    (∀ w : (lorentzFunctional q.val).ker,
      (hyperboloidTangentEquivKer (centerHyperboloid p q)
        (mfderiv I I (centerHyperboloid p) q ((hyperboloidTangentEquivKer q).symm w))).val =
      lorentzCenterCoordinates p w.val) ∧
    (∀ w : (lorentzFunctional q.val).ker,
      (hyperboloidTangentEquivKer (uncenterHyperboloid p q)
        (mfderiv I I (uncenterHyperboloid p) q ((hyperboloidTangentEquivKer q).symm w))).val =
      (lorentzCenterCoordinates p).symm w.val) ∧
    Function.Bijective (fun w : (lorentzFunctional q.val).ker =>
      hyperboloidTangentEquivKer (centerHyperboloid p q)
        (mfderiv I I (centerHyperboloid p) q ((hyperboloidTangentEquivKer q).symm w))) ∧
    Function.Bijective (fun w : (lorentzFunctional q.val).ker =>
      hyperboloidTangentEquivKer (uncenterHyperboloid p q)
        (mfderiv I I (uncenterHyperboloid p) q ((hyperboloidTangentEquivKer q).symm w))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    rw [hyperboloidTangentEquivKer_apply, mfderiv_centerHyperboloid_val]
    rw [← hyperboloidTangentEquivKer_apply, ContinuousLinearEquiv.apply_symm_apply]
  · intro w
    rw [hyperboloidTangentEquivKer_apply, mfderiv_uncenterHyperboloid_val]
    rw [← hyperboloidTangentEquivKer_apply, ContinuousLinearEquiv.apply_symm_apply]
  · exact (hyperboloidTangentEquivKer _).bijective.comp
      (((centerHyperboloid_mfderiv_inverse p q).2.2.2.2.1).comp
        (hyperboloidTangentEquivKer q).symm.bijective)
  · exact (hyperboloidTangentEquivKer _).bijective.comp
      (((centerHyperboloid_mfderiv_inverse p q).2.2.2.2.2).comp
        (hyperboloidTangentEquivKer q).symm.bijective)

/-- Center change preserves the Lorentz restriction on every pair of intrinsic tangent vectors. -/
theorem centerHyperboloid_preserves_tangentTensor (p q : Hyperboloid) (v w : TangentSpace I q) :
    hyperboloidTangentTensor (centerHyperboloid p q)
      (mfderiv I I (centerHyperboloid p) q v) (mfderiv I I (centerHyperboloid p) q w) =
    hyperboloidTangentTensor q v w := by
  simp only [hyperboloidTangentTensor_apply, mfderiv_centerHyperboloid_val]
  exact lorentzCenterCoordinates_preserves p _ _

/-- The inverse center change preserves the Lorentz restriction on every tangent pair. -/
theorem uncenterHyperboloid_preserves_tangentTensor (p q : Hyperboloid) (v w : TangentSpace I q) :
    hyperboloidTangentTensor (uncenterHyperboloid p q)
      (mfderiv I I (uncenterHyperboloid p) q v) (mfderiv I I (uncenterHyperboloid p) q w) =
    hyperboloidTangentTensor q v w := by
  simp only [hyperboloidTangentTensor_apply, mfderiv_uncenterHyperboloid_val]
  exact lorentzCenterCoordinates_symm_preserves p _ _

/-- Center change preserves the genuine hyperboloid Riemannian metric. -/
theorem centerHyperboloid_preserves_metric (p q : Hyperboloid) (v w : TangentSpace I q) :
    hyperboloidMetric.inner (centerHyperboloid p q)
      (mfderiv I I (centerHyperboloid p) q v) (mfderiv I I (centerHyperboloid p) q w) =
    hyperboloidMetric.inner q v w := by
  simp only [hyperboloidMetric_inner]
  exact centerHyperboloid_preserves_tangentTensor p q v w

/-- The inverse center change preserves the same hyperboloid Riemannian metric. -/
theorem uncenterHyperboloid_preserves_metric (p q : Hyperboloid) (v w : TangentSpace I q) :
    hyperboloidMetric.inner (uncenterHyperboloid p q)
      (mfderiv I I (uncenterHyperboloid p) q v) (mfderiv I I (uncenterHyperboloid p) q w) =
    hyperboloidMetric.inner q v w := by
  simp only [hyperboloidMetric_inner]
  exact uncenterHyperboloid_preserves_tangentTensor p q v w

/-- Center change preserves real and extended tangent norms for the hyperboloid metric. -/
theorem centerHyperboloid_norm_enorm (p q : Hyperboloid) :
    letI : Bundle.RiemannianBundle (fun r : Hyperboloid => TangentSpace I r) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    (∀ v : TangentSpace I q, ‖mfderiv I I (centerHyperboloid p) q v‖ = ‖v‖) ∧
    (∀ v : TangentSpace I q, ‖mfderiv I I (centerHyperboloid p) q v‖ₑ = ‖v‖ₑ) := by
  letI : Bundle.RiemannianBundle (fun r : Hyperboloid => TangentSpace I r) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := (mfderiv I I (centerHyperboloid p) q).toLinearMap.isometryOfInner
    (centerHyperboloid_preserves_metric p q)
  exact ⟨L.norm_map, L.enorm_map⟩

/-- The inverse center change preserves real and extended tangent norms for the same metric. -/
theorem uncenterHyperboloid_norm_enorm (p q : Hyperboloid) :
    letI : Bundle.RiemannianBundle (fun r : Hyperboloid => TangentSpace I r) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    (∀ v : TangentSpace I q, ‖mfderiv I I (uncenterHyperboloid p) q v‖ = ‖v‖) ∧
    (∀ v : TangentSpace I q, ‖mfderiv I I (uncenterHyperboloid p) q v‖ₑ = ‖v‖ₑ) := by
  letI : Bundle.RiemannianBundle (fun r : Hyperboloid => TangentSpace I r) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := (mfderiv I I (uncenterHyperboloid p) q).toLinearMap.isometryOfInner
    (uncenterHyperboloid_preserves_metric p q)
  exact ⟨L.norm_map, L.enorm_map⟩

/-- Center change preserves the ordinary real and extended speed of a differentiable curve. -/
theorem centerHyperboloid_speed (p : Hyperboloid) (γ : ℝ → Hyperboloid) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ) t (1 : ℝ)‖ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
    ‖mfderiv 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ) t (1 : ℝ)‖ₑ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  exact speed_comp_of_tensorPreserving
    hyperboloidMetric hyperboloidMetric (centerHyperboloid p) (contMDiff_centerHyperboloid p)
    (centerHyperboloid_preserves_metric p) γ t hγ

/-- Center change preserves within-set speed on the same uniquely differentiable parameter set. -/
theorem centerHyperboloid_speedWithin (p : Hyperboloid) (γ : ℝ → Hyperboloid) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ) s t (1 : ℝ)‖ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
    ‖mfderivWithin 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ) s t (1 : ℝ)‖ₑ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  exact speedWithin_comp_of_tensorPreserving
    hyperboloidMetric hyperboloidMetric (centerHyperboloid p) (contMDiff_centerHyperboloid p)
    (centerHyperboloid_preserves_metric p) γ s t hγ hs

/-- The inverse center change preserves ordinary real and extended curve speed. -/
theorem uncenterHyperboloid_speed (p : Hyperboloid) (γ : ℝ → Hyperboloid) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I ((uncenterHyperboloid p) ∘ γ) t (1 : ℝ)‖ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
    ‖mfderiv 𝓘(ℝ, ℝ) I ((uncenterHyperboloid p) ∘ γ) t (1 : ℝ)‖ₑ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  exact speed_comp_of_tensorPreserving
    hyperboloidMetric hyperboloidMetric (uncenterHyperboloid p) (contMDiff_uncenterHyperboloid p)
    (uncenterHyperboloid_preserves_metric p) γ t hγ

/-- The inverse center change preserves within-set speed with the same parameter hypotheses. -/
theorem uncenterHyperboloid_speedWithin (p : Hyperboloid) (γ : ℝ → Hyperboloid) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) I ((uncenterHyperboloid p) ∘ γ) s t (1 : ℝ)‖ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
    ‖mfderivWithin 𝓘(ℝ, ℝ) I ((uncenterHyperboloid p) ∘ γ) s t (1 : ℝ)‖ₑ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  exact speedWithin_comp_of_tensorPreserving
    hyperboloidMetric hyperboloidMetric (uncenterHyperboloid p) (contMDiff_uncenterHyperboloid p)
    (uncenterHyperboloid_preserves_metric p) γ s t hγ hs

/-- Center change preserves each finite curve piece, its integral, and the full real and extended
length, retaining the original weak subdivision and exact endpoint values. -/
theorem centerHyperboloid_length (p : Hyperboloid) {γ : ℝ → Hyperboloid} {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let q : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)‖
    let q' : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ) (P i) t (1 : ℝ)‖
    IsPiecewiseC1On I ((centerHyperboloid p) ∘ γ) a b n cut ∧
    ((centerHyperboloid p) ∘ γ) a = (centerHyperboloid p) (γ a) ∧ ((centerHyperboloid p) ∘ γ) b = (centerHyperboloid p) (γ b) ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, q' i t) =
      ∫ t in cut i.castSucc..cut i.succ, q i t) ∧
    piecewiseC1Length hyperboloidMetric ((centerHyperboloid p) ∘ γ) cut = piecewiseC1Length hyperboloidMetric γ cut ∧
    0 ≤ piecewiseC1Length hyperboloidMetric γ cut ∧ 0 ≤ piecewiseC1Length hyperboloidMetric ((centerHyperboloid p) ∘ γ) cut ∧
    pathELength I ((centerHyperboloid p) ∘ γ) a b = pathELength I γ a b ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) ∧
    pathELength I ((centerHyperboloid p) ∘ γ) a b < (⊤ : ℝ≥0∞) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ cut) ∧
    pathELength I ((centerHyperboloid p) ∘ γ) a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric ((centerHyperboloid p) ∘ γ) cut) ∧
    (∀ i : Fin n,
      (∫⁻ t in P i, ENNReal.ofReal (q' i t)) =
        ∫⁻ t in P i, ENNReal.ofReal (q i t)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q i t)) < (⊤ : ℝ≥0∞)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) < (⊤ : ℝ≥0∞)) := by
  exact hγ.length_comp_of_tensorPreserving hyperboloidMetric hyperboloidMetric
    (centerHyperboloid p) (contMDiff_centerHyperboloid p) (centerHyperboloid_preserves_metric p)

/-- The inverse center change preserves every finite piece and both total lengths, including
zero pieces and repeated cuts, with the same subdivision and exact endpoints. -/
theorem uncenterHyperboloid_length (p : Hyperboloid) {γ : ℝ → Hyperboloid} {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let q : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)‖
    let q' : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I ((uncenterHyperboloid p) ∘ γ) (P i) t (1 : ℝ)‖
    IsPiecewiseC1On I ((uncenterHyperboloid p) ∘ γ) a b n cut ∧
    ((uncenterHyperboloid p) ∘ γ) a = (uncenterHyperboloid p) (γ a) ∧ ((uncenterHyperboloid p) ∘ γ) b = (uncenterHyperboloid p) (γ b) ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, q' i t) =
      ∫ t in cut i.castSucc..cut i.succ, q i t) ∧
    piecewiseC1Length hyperboloidMetric ((uncenterHyperboloid p) ∘ γ) cut = piecewiseC1Length hyperboloidMetric γ cut ∧
    0 ≤ piecewiseC1Length hyperboloidMetric γ cut ∧ 0 ≤ piecewiseC1Length hyperboloidMetric ((uncenterHyperboloid p) ∘ γ) cut ∧
    pathELength I ((uncenterHyperboloid p) ∘ γ) a b = pathELength I γ a b ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) ∧
    pathELength I ((uncenterHyperboloid p) ∘ γ) a b < (⊤ : ℝ≥0∞) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ cut) ∧
    pathELength I ((uncenterHyperboloid p) ∘ γ) a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric ((uncenterHyperboloid p) ∘ γ) cut) ∧
    (∀ i : Fin n,
      (∫⁻ t in P i, ENNReal.ofReal (q' i t)) =
        ∫⁻ t in P i, ENNReal.ofReal (q i t)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q i t)) < (⊤ : ℝ≥0∞)) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) < (⊤ : ℝ≥0∞)) := by
  exact hγ.length_comp_of_tensorPreserving hyperboloidMetric hyperboloidMetric
    (uncenterHyperboloid p) (contMDiff_uncenterHyperboloid p) (uncenterHyperboloid_preserves_metric p)

/-- Center change gives a length-preserving equivalence of complete endpoint-constrained
piecewise-smooth curve families, in both directions on the same interval and subdivision. -/
theorem centerHyperboloid_curveFamily_length (c : Hyperboloid) {a b : ℝ} {n : ℕ}
    {cut : Fin (n+1) → ℝ} {x y : Hyperboloid} :
    letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let Φ := PiecewiseC1CurveOn.mapEquiv (a := a) (b := b) (cut := cut) (p := x) (q := y) (centerHyperboloidDiffeomorph c)
    Function.Bijective Φ ∧
    (∀ γ : PiecewiseC1CurveOn I a b n cut x y,
      piecewiseC1Length hyperboloidMetric (Φ γ).val cut = piecewiseC1Length hyperboloidMetric γ.val cut ∧
      pathELength I (Φ γ).val a b = pathELength I γ.val a b ∧
      pathELength I γ.val a b < (⊤ : ℝ≥0∞) ∧
      pathELength I (Φ γ).val a b < (⊤ : ℝ≥0∞) ∧
      (Φ γ).val a = (centerHyperboloidDiffeomorph c) x ∧ (Φ γ).val b = (centerHyperboloidDiffeomorph c) y) ∧
    (∀ η : PiecewiseC1CurveOn I a b n cut ((centerHyperboloidDiffeomorph c) x) ((centerHyperboloidDiffeomorph c) y),
      piecewiseC1Length hyperboloidMetric (Φ.symm η).val cut = piecewiseC1Length hyperboloidMetric η.val cut ∧
      pathELength I (Φ.symm η).val a b = pathELength I η.val a b ∧
      pathELength I η.val a b < (⊤ : ℝ≥0∞) ∧
      pathELength I (Φ.symm η).val a b < (⊤ : ℝ≥0∞) ∧
      (Φ.symm η).val a = x ∧ (Φ.symm η).val b = y) ∧
    (∀ γ t, (Φ γ).val t = (centerHyperboloidDiffeomorph c) (γ.val t)) ∧
    (∀ η t, (Φ.symm η).val t = (centerHyperboloidDiffeomorph c).symm (η.val t)) ∧
    (∀ γ, Φ.symm (Φ γ) = γ) ∧
    (∀ η, Φ (Φ.symm η) = η) := by
  exact PiecewiseC1CurveOn.mapEquiv_length hyperboloidMetric hyperboloidMetric
    (centerHyperboloidDiffeomorph c) (centerHyperboloid_preserves_metric c)


section PolarRadial

open Set MeasureTheory Filter
open scoped Manifold Topology BigOperators ENNReal NNReal ContDiff Bundle
local notation "K" => 𝓘(ℝ, ℝ × ℝ)

/-- The two spatial coordinates as a complex number, with their ordinary Euclidean norm. (G03.a) -/
def hyperboloidSpatial (q : Hyperboloid) : ℂ := ⟨q.val 0, q.val 1⟩

/-- The nonnegative radial coordinate is arsinh of the spatial norm. (G03.a) -/
def hyperboloidRadius (q : Hyperboloid) : ℝ :=
  Real.arsinh ‖hyperboloidSpatial q‖

/-- Signed polar coordinates in the ambient Lorentz space; geometric radii are nonnegative. (G03.a) -/
def hyperboloidPolarCoords (r θ : ℝ) : Fin 3 → ℝ :=
  ![Real.sinh r * Real.cos θ, Real.sinh r * Real.sin θ, Real.cosh r]

/-- The polar formula lies on the positive unit hyperboloid, by the circular and hyperbolic identities. (G03.a) -/
theorem hyperboloidPolarCoords_mem (r θ : ℝ) :
  (hyperboloidPolarCoords r θ 0) ^ 2 +
      (hyperboloidPolarCoords r θ 1) ^ 2 -
      (hyperboloidPolarCoords r θ 2) ^ 2 = -1 ∧
    0 < hyperboloidPolarCoords r θ 2 := by
  constructor
  · change (Real.sinh r * Real.cos θ)^2 + (Real.sinh r * Real.sin θ)^2 -
      Real.cosh r ^ 2 = -1
    calc
      _ = Real.sinh r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) - Real.cosh r ^ 2 := by ring
      _ = -1 := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
        nlinarith [Real.cosh_sq_sub_sinh_sq r]
  · exact Real.cosh_pos r

/-- The actual hyperboloid point represented by signed polar coordinates. (G03.a) -/
def hyperboloidPolar (r θ : ℝ) : Hyperboloid :=
  ⟨hyperboloidPolarCoords r θ, hyperboloidPolarCoords_mem r θ⟩

/-- The radius recovers the spatial norm and positive time; zero radius is precisely the center. (G03.a) -/
theorem hyperboloidRadius_properties (q : Hyperboloid) :
  0 ≤ hyperboloidRadius q ∧
  Real.sinh (hyperboloidRadius q) = ‖hyperboloidSpatial q‖ ∧
  Real.cosh (hyperboloidRadius q) = q.val 2 ∧
  (hyperboloidRadius q = 0 ↔ q.val = ![0, 0, 1]) ∧
  (hyperboloidSpatial q = 0 ↔ hyperboloidRadius q = 0) := by
  have hs : Real.sinh (hyperboloidRadius q) = ‖hyperboloidSpatial q‖ := Real.sinh_arsinh _
  have hn : ‖hyperboloidSpatial q‖ ^ 2 = q.val 0 ^ 2 + q.val 1 ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    rfl
  have ht : Real.cosh (hyperboloidRadius q) = q.val 2 := by
    have h := Real.cosh_sq_sub_sinh_sq (hyperboloidRadius q)
    rw [hs, hn] at h
    nlinarith [q.property.1, q.property.2, Real.cosh_pos (hyperboloidRadius q)]
  have hz : hyperboloidRadius q = 0 ↔ hyperboloidSpatial q = 0 := by
    constructor
    · intro h
      apply norm_eq_zero.mp
      rw [← hs, h, Real.sinh_zero]
    · intro h
      simp [hyperboloidRadius, h]
  refine ⟨Real.arsinh_nonneg_iff.mpr (norm_nonneg _), hs, ht, ?_, hz.symm⟩
  constructor
  · intro h
    have hx := congrArg Complex.re (hz.mp h)
    have hy := congrArg Complex.im (hz.mp h)
    have htt : q.val 2 = 1 := by simpa [h] using ht.symm
    funext i
    fin_cases i
    · exact hx
    · exact hy
    · exact htt
  · intro h
    apply hz.mpr
    apply Complex.ext <;> simp [hyperboloidSpatial, h]

/-- The nonnegative polar parameter is the actual radial coordinate. (G03.a) -/
theorem hyperboloidPolar_radius {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
  hyperboloidRadius (hyperboloidPolar r θ) = r := by
  have he : hyperboloidSpatial (hyperboloidPolar r θ) =
      (Real.sinh r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp only [hyperboloidSpatial, hyperboloidPolar, hyperboloidPolarCoords,
        Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;> ring
  have hn : ‖hyperboloidSpatial (hyperboloidPolar r θ)‖ = |Real.sinh r| := by
    rw [he, norm_mul]
    simpa only [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, mul_one] using
      congrArg (fun x : ℝ => |Real.sinh r| * x) (Complex.norm_cos_add_sin_mul_I θ)
  have hs : 0 ≤ Real.sinh r :=
    Real.arsinh_nonneg_iff.mp (by simpa only [Real.arsinh_sinh] using hr)
  unfold hyperboloidRadius
  rw [hn, abs_of_nonneg hs, Real.arsinh_sinh]

/-- Pointwise complex argument reconstructs every point, including the center. (G03.a) -/
theorem hyperboloidPolar_arg (q : Hyperboloid) :
  hyperboloidPolar (hyperboloidRadius q) (Complex.arg (hyperboloidSpatial q)) = q := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change Real.sinh (hyperboloidRadius q) * Real.cos (Complex.arg (hyperboloidSpatial q)) = q.val 0
    rw [(hyperboloidRadius_properties q).2.1]
    exact Complex.norm_mul_cos_arg _
  · change Real.sinh (hyperboloidRadius q) * Real.sin (Complex.arg (hyperboloidSpatial q)) = q.val 1
    rw [(hyperboloidRadius_properties q).2.1]
    exact Complex.norm_mul_sin_arg _
  · exact (hyperboloidRadius_properties q).2.2.1

/-- Polar parameters are unique modulo turns away from the center; all center angles coincide. (G03.a) -/
theorem hyperboloidPolar_eq_iff {r s θ φ : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
  hyperboloidPolar r θ = hyperboloidPolar s φ ↔
    r = s ∧ (r = 0 ∨ (θ : Real.Angle) = (φ : Real.Angle)) := by
  have harg {t : ℝ} (ht : 0 < t) (α : ℝ) :
      (Complex.arg (hyperboloidSpatial (hyperboloidPolar t α)) : Real.Angle) =
        (α : Real.Angle) := by
    have he : hyperboloidSpatial (hyperboloidPolar t α) =
        (Real.sinh t : ℂ) * ((Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I) := by
      apply Complex.ext <;>
        simp only [hyperboloidSpatial, hyperboloidPolar, hyperboloidPolarCoords,
          Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im] <;> ring
    rw [he]
    have hsinh : 0 < Real.sinh t :=
      Real.arsinh_pos_iff.mp (by simpa only [Real.arsinh_sinh] using ht)
    simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using
      Complex.arg_mul_cos_add_sin_mul_I_coe_angle hsinh (α : Real.Angle)
  constructor
  · intro h
    have hrs : r = s := by
      rw [← hyperboloidPolar_radius hr θ, h, hyperboloidPolar_radius hs φ]
    refine ⟨hrs, ?_⟩
    by_cases hz : r = 0
    · exact Or.inl hz
    · right
      have hpos := lt_of_le_of_ne hr (Ne.symm hz)
      rw [← harg hpos θ, ← harg (hrs ▸ hpos) φ, h]
  · rintro ⟨hrs, h | h⟩
    ·
      apply Subtype.ext
      simp [hyperboloidPolar, hyperboloidPolarCoords, ← hrs, h]
    · have hc : Real.cos θ = Real.cos φ := congrArg Real.Angle.cos h
      have hs : Real.sin θ = Real.sin φ := congrArg Real.Angle.sin h
      apply Subtype.ext
      simp only [hyperboloidPolar, hyperboloidPolarCoords, ← hrs, hc, hs]

/-- The center is independent of angle, and positive radius has the displayed unit direction. (G03.a) -/
theorem hyperboloidPolar_center_direction (θ : ℝ) (q : Hyperboloid) :
  (hyperboloidPolar 0 θ).val = ![0, 0, 1] ∧
  (0 < hyperboloidRadius q →
    hyperboloidSpatial q / (‖hyperboloidSpatial q‖ : ℂ) =
      (Real.cos (Complex.arg (hyperboloidSpatial q)) : ℂ) +
        (Real.sin (Complex.arg (hyperboloidSpatial q)) : ℂ) * Complex.I) := by
  constructor
  · simp [hyperboloidPolar, hyperboloidPolarCoords]
  · intro hq
    have hz : hyperboloidSpatial q ≠ 0 := by
      intro hz
      exact (ne_of_gt hq) ((hyperboloidRadius_properties q).2.2.2.2.mp hz)
    have hn : (‖hyperboloidSpatial q‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [div_eq_iff hn]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_comm] using
      (Complex.norm_mul_cos_add_sin_mul_I (hyperboloidSpatial q)).symm

private theorem contMDiff_hyperboloidSpatial : ContMDiff I I ∞ hyperboloidSpatial := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℂ :=
    Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ))
  have hL (q : Hyperboloid) : L q.val = hyperboloidSpatial q := by
    apply Complex.ext <;> simp [L, hyperboloidSpatial]
  simpa only [Function.comp_def, hL] using
    L.contDiff.comp_contMDiff contMDiff_hyperboloid_val

/-- Away from the center the spatial norm, hence the radius, is smooth. (G03.b) -/
theorem contMDiffAt_hyperboloidRadius {q : Hyperboloid}
    (hq : 0 < hyperboloidRadius q) :
  ContMDiffAt I 𝓘(ℝ, ℝ) ∞ hyperboloidRadius q := by
  have hz : hyperboloidSpatial q ≠ 0 := by
    intro hz
    exact (ne_of_gt hq) ((hyperboloidRadius_properties q).2.2.2.2.mp hz)
  exact Real.contDiff_arsinh.contDiffAt.comp_contMDiffAt
    ((contDiffAt_norm ℝ hz).comp_contMDiffAt contMDiff_hyperboloidSpatial.contMDiffAt)

/-- Each noncentral point has a smooth real angle on a neighborhood; either slit branch may be used. (G03.b) -/
theorem hyperboloidPolar_local_coordinates {q : Hyperboloid}
    (hq : 0 < hyperboloidRadius q) :
  ∃ (U : Set Hyperboloid) (θ : Hyperboloid → ℝ),
    IsOpen U ∧ q ∈ U ∧
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ hyperboloidRadius U ∧
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ θ U ∧
    (∀ x ∈ U, 0 < hyperboloidRadius x) ∧
    (∀ x ∈ U, hyperboloidPolar (hyperboloidRadius x) (θ x) = x) := by
  let θp : Hyperboloid → ℝ := fun x => (Complex.log (hyperboloidSpatial x)).im
  let θm : Hyperboloid → ℝ := fun x => (Complex.log (-hyperboloidSpatial x)).im + Real.pi
  let Up : Set Hyperboloid :=
    {x | 0 < hyperboloidRadius x} ∩ hyperboloidSpatial ⁻¹' Complex.slitPlane
  let Um : Set Hyperboloid :=
    {x | 0 < hyperboloidRadius x} ∩ (fun x => -hyperboloidSpatial x) ⁻¹' Complex.slitPlane
  have hr : Continuous hyperboloidRadius :=
    Real.continuous_arsinh.comp contMDiff_hyperboloidSpatial.continuous.norm
  have hop : IsOpen Up := (isOpen_lt continuous_const hr).inter
    (Complex.isOpen_slitPlane.preimage contMDiff_hyperboloidSpatial.continuous)
  have hom : IsOpen Um := (isOpen_lt continuous_const hr).inter
    (Complex.isOpen_slitPlane.preimage contMDiff_hyperboloidSpatial.continuous.neg)
  have hz : hyperboloidSpatial q ≠ 0 := by
    intro hz
    exact (ne_of_gt hq) ((hyperboloidRadius_properties q).2.2.2.2.mp hz)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hp | hm
  · refine ⟨Up, θp, hop, ⟨hq, hp⟩, ?_, ?_, (fun x hx => hx.1), ?_⟩
    · intro x hx
      exact (contMDiffAt_hyperboloidRadius hx.1).contMDiffWithinAt
    · intro x hx
      have hl : ContDiffAt ℝ ∞ Complex.log (hyperboloidSpatial x) :=
        (Complex.contDiffAt_log hx.2).restrict_scalars ℝ
      exact ((Complex.imCLM.contDiff.contDiffAt.comp _ hl).comp_contMDiffAt
        contMDiff_hyperboloidSpatial.contMDiffAt).contMDiffWithinAt
    · intro x hx
      simpa only [θp, Complex.log_im] using hyperboloidPolar_arg x
  · refine ⟨Um, θm, hom, ⟨hq, hm⟩, ?_, ?_, (fun x hx => hx.1), ?_⟩
    · intro x hx
      exact (contMDiffAt_hyperboloidRadius hx.1).contMDiffWithinAt
    · intro x hx
      have hl : ContDiffAt ℝ ∞ Complex.log (-hyperboloidSpatial x) :=
        (Complex.contDiffAt_log hx.2).restrict_scalars ℝ
      have hn : ContDiffAt ℝ ∞ (fun z : ℂ => -z) (hyperboloidSpatial x) := contDiffAt_id.neg
      have ha := ((Complex.imCLM.contDiff.contDiffAt.comp _ hl).comp _ hn).add
        (contDiffAt_const (c := Real.pi))
      exact (ha.comp_contMDiffAt contMDiff_hyperboloidSpatial.contMDiffAt).contMDiffWithinAt
    · intro x hx
      apply Subtype.ext
      have hrs := (hyperboloidRadius_properties x).2.1
      have htt := (hyperboloidRadius_properties x).2.2.1
      have hc := Complex.norm_mul_cos_arg (-hyperboloidSpatial x)
      have hs := Complex.norm_mul_sin_arg (-hyperboloidSpatial x)
      simp only [norm_neg, Complex.neg_re, Complex.neg_im] at hc hs
      funext i
      fin_cases i
      · change Real.sinh (hyperboloidRadius x) * Real.cos (θm x) = x.val 0
        simp only [θm, Complex.log_im, Real.cos_add_pi, hrs]
        change ‖hyperboloidSpatial x‖ * Real.cos (-hyperboloidSpatial x).arg = -x.val 0 at hc
        nlinarith
      · change Real.sinh (hyperboloidRadius x) * Real.sin (θm x) = x.val 1
        simp only [θm, Complex.log_im, Real.sin_add_pi, hrs]
        change ‖hyperboloidSpatial x‖ * Real.sin (-hyperboloidSpatial x).arg = -x.val 1 at hs
        nlinarith
      · exact htt

/-- The signed polar parametrization is smooth in the actual hyperboloid atlas, including at radius zero. (G03.b) -/
theorem contMDiff_hyperboloidPolar :
  ContMDiff K I ∞ (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ × ℝ => hyperboloidPolarCoords x.1 x.2) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun x : ℝ × ℝ => Real.sinh x.1 * Real.cos x.2)
      fun_prop
    · change ContDiff ℝ ∞ (fun x : ℝ × ℝ => Real.sinh x.1 * Real.sin x.2)
      fun_prop
    · change ContDiff ℝ ∞ (fun x : ℝ × ℝ => Real.cosh x.1)
      fun_prop
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.contMDiffOn.comp_contMDiff
    hc.contMDiff (fun x => hyperboloid_denominator_pos (hyperboloidPolar x.1 x.2))

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic polar differential, followed by the actual inclusion, is its displayed ambient derivative. (G03.b) -/
theorem mfderiv_hyperboloidPolar_val (r θ : ℝ) (u : ℝ × ℝ) :
  mfderiv I J (fun q : Hyperboloid => q.val) (hyperboloidPolar r θ)
    (mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) u) =
  ![Real.cosh r * Real.cos θ * u.1 - Real.sinh r * Real.sin θ * u.2,
    Real.cosh r * Real.sin θ * u.1 + Real.sinh r * Real.cos θ * u.2,
    Real.sinh r * u.1] := by
  let D : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![Real.sinh r • (-Real.sin θ • ContinuousLinearMap.snd ℝ ℝ ℝ) +
        Real.cos θ • (Real.cosh r • ContinuousLinearMap.fst ℝ ℝ ℝ),
      Real.sinh r • (Real.cos θ • ContinuousLinearMap.snd ℝ ℝ ℝ) +
        Real.sin θ • (Real.cosh r • ContinuousLinearMap.fst ℝ ℝ ℝ),
      Real.sinh r • ContinuousLinearMap.fst ℝ ℝ ℝ]
  have hd : HasFDerivAt (fun x : ℝ × ℝ => hyperboloidPolarCoords x.1 x.2) D (r, θ) := by
    have hf : HasFDerivAt (fun x : ℝ × ℝ => x.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (r, θ) := hasFDerivAt_fst
    have hg : HasFDerivAt (fun x : ℝ × ℝ => x.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (r, θ) := hasFDerivAt_snd
    have h0 := hf.sinh.mul hg.cos
    have h1 := hf.sinh.mul hg.sin
    have h2 := hf.cosh
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have he : (mfderiv K J (fun x : ℝ × ℝ => (hyperboloidPolar x.1 x.2).val)
      (r, θ) : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) = D :=
    mfderiv_eq_fderiv.trans hd.fderiv
  have hi := mfderiv_comp_apply (r, θ)
    (contMDiff_hyperboloid_val.mdifferentiable (by simp) _)
    (contMDiff_hyperboloidPolar.mdifferentiable (by simp) _) u
  have hv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) => L u) he
  calc
    _ = D u := hi.symm.trans hv
    _ = _ := by
      ext i
      fin_cases i <;> simp [D] <;> ring

/-- The Lorentz restriction in polar coordinates has radial coefficient one and angular coefficient sinh squared. (G03.b) -/
theorem hyperboloidPolar_tangentTensor (r θ : ℝ) (u v : ℝ × ℝ) :
  hyperboloidTangentTensor (hyperboloidPolar r θ)
    (mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) u)
    (mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) v) =
      u.1 * v.1 + (Real.sinh r) ^ 2 * u.2 * v.2 := by
  rw [hyperboloidTangentTensor_apply, mfderiv_hyperboloidPolar_val,
    mfderiv_hyperboloidPolar_val]
  change
    (Real.cosh r * Real.cos θ * u.1 - Real.sinh r * Real.sin θ * u.2) *
      (Real.cosh r * Real.cos θ * v.1 - Real.sinh r * Real.sin θ * v.2) +
    (Real.cosh r * Real.sin θ * u.1 + Real.sinh r * Real.cos θ * u.2) *
      (Real.cosh r * Real.sin θ * v.1 + Real.sinh r * Real.cos θ * v.2) -
    (Real.sinh r * u.1) * (Real.sinh r * v.1) = _
  calc
    _ = (Real.cosh r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) - Real.sinh r ^ 2) *
          u.1 * v.1 + Real.sinh r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) * u.2 * v.2 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one, mul_one,
      Real.cosh_sq_sub_sinh_sq, one_mul]

/-- The same smooth metric has the computed polar bilinear form. (G03.b) -/
theorem hyperboloidPolar_metric (r θ : ℝ) (u v : ℝ × ℝ) :
  hyperboloidMetric.inner (hyperboloidPolar r θ)
    (mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) u)
    (mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) v) =
      u.1 * v.1 + (Real.sinh r) ^ 2 * u.2 * v.2 := by
  rw [hyperboloidMetric_inner]
  exact hyperboloidPolar_tangentTensor r θ u v

/-- The actual intrinsic metric norm is the square root of the polar quadratic form. (G03.b) -/
theorem hyperboloidPolar_norm (r θ : ℝ) (u : ℝ × ℝ) :
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  ‖mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) u‖ =
    Real.sqrt (u.1 ^ 2 + (Real.sinh r) ^ 2 * u.2 ^ 2) := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let v := mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (r, θ) u
  have hn : ‖v‖ ^ 2 = u.1 ^ 2 + Real.sinh r ^ 2 * u.2 ^ 2 := by
    have hi := hyperboloidPolar_metric r θ u u
    have hs : ‖v‖ ^ 2 = hyperboloidMetric.inner (hyperboloidPolar r θ) v v :=
      (real_inner_self_eq_norm_sq v).symm
    rw [hs, hi]
    ring
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

set_option backward.isDefEq.respectTransparency false in
/-- A local polar representation gives the actual curve speed; the metric base point is transported as well. (G03.b) -/
theorem hyperboloidPolar_curve_speed
    (γ : ℝ → Hyperboloid) (ρ θ : ℝ → ℝ) (t a b : ℝ)
    (hρ : HasDerivAt ρ a t) (hθ : HasDerivAt θ b t)
    (hγ : ∀ᶠ s in nhds t, γ s = hyperboloidPolar (ρ s) (θ s)) :
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ =
    Real.sqrt (a ^ 2 + (Real.sinh (ρ t)) ^ 2 * b ^ 2) := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let δ : ℝ → Hyperboloid := fun s => hyperboloidPolar (ρ s) (θ s)
  have hp := hρ.hasFDerivAt.prodMk hθ.hasFDerivAt
  have hpair : mfderiv 𝓘(ℝ, ℝ) K (fun s => (ρ s, θ s)) t 1 = (a, b) := by
    have he : (mfderiv 𝓘(ℝ, ℝ) K (fun s => (ρ s, θ s)) t : ℝ →L[ℝ] (ℝ × ℝ)) =
        (ContinuousLinearMap.toSpanSingleton ℝ a).prod
          (ContinuousLinearMap.toSpanSingleton ℝ b) :=
      mfderiv_eq_fderiv.trans hp.fderiv
    exact (congrArg (fun L : ℝ →L[ℝ] (ℝ × ℝ) => L 1) he).trans (by simp)
  have hd := mfderiv_comp_apply t
    (contMDiff_hyperboloidPolar.mdifferentiable (by simp) (ρ t, θ t))
    hp.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hpair] at hd
  change mfderiv 𝓘(ℝ, ℝ) I δ t 1 =
    mfderiv K I (fun x : ℝ × ℝ => hyperboloidPolar x.1 x.2) (ρ t, θ t) (a, b) at hd
  have hlocal : γ =ᶠ[nhds t] δ := hγ
  have hb : γ t = δ t := hlocal.eq_of_nhds
  have he : mfderiv 𝓘(ℝ, ℝ) I γ t = mfderiv 𝓘(ℝ, ℝ) I δ t := hlocal.mfderiv_eq
  have hv := congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) he
  have hn : ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ = ‖mfderiv 𝓘(ℝ, ℝ) I δ t 1‖ :=
    congrArg₂ (fun (q : Hyperboloid) (v : ℂ) => @norm (TangentSpace I q) inferInstance v) hb hv
  rw [hn]
  exact (congrArg (fun v : TangentSpace I (δ t) => ‖v‖) hd).trans
    (hyperboloidPolar_norm (ρ t) (θ t) (a, b))

/-- On a compact C1 piece the spatial map, norm and arsinh compose to a Lipschitz radius. (G03.c) -/
theorem hyperboloidRadius_lipschitzOn_piece
    {γ : ℝ → Hyperboloid} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
  ∃ κ : ℝ≥0, LipschitzOnWith κ
    (fun t => hyperboloidRadius (γ t)) (Icc a b) := by
  have hz : ContDiffOn ℝ 1 (fun t => hyperboloidSpatial (γ t)) (Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiff_hyperboloidSpatial.of_le (by simp)).comp_contMDiffOn hγ)
  obtain ⟨κz, hκz⟩ := hz.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hz.continuousOn
  have hm : MapsTo (fun t => ‖hyperboloidSpatial (γ t)‖) (Icc a b) (Icc 0 R) :=
    fun t ht => ⟨norm_nonneg _, hR t ht⟩
  obtain ⟨κa, hκa⟩ := (Real.contDiff_arsinh (n := 1)).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 R) isCompact_Icc
  have hn : LipschitzOnWith (1 * κz) (fun t => ‖hyperboloidSpatial (γ t)‖) (Icc a b) :=
    lipschitzWith_one_norm.lipschitzOnWith.comp hκz (mapsTo_univ _ _)
  exact ⟨κa * (1 * κz), hκa.comp hn hm⟩

/-- The radius is absolutely continuous on the whole weak finite subdivision, with unrestricted center visits. (G03.c) -/
theorem hyperboloidRadius_absolutelyContinuous
    {γ : ℝ → Hyperboloid} {a b : ℝ} {n : ℕ}
    {cut : Fin (n + 1) → ℝ}
    (hγ : Manifold.IsPiecewiseC1On I γ a b n cut) :
  AbsolutelyContinuousOnInterval (fun t => hyperboloidRadius (γ t)) a b := by
  apply AbsolutelyContinuousOnInterval.of_monotone_subdivision
    cut hγ.1 hγ.2.1 hγ.2.2.1
  intro i hi
  obtain ⟨κ, hκ⟩ :=
    hyperboloidRadius_lipschitzOn_piece hi (hγ.2.2.2.2 i hi)
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le (le_of_lt hi)] using hκ

/-- On a strict-piece interior radial derivative is bounded by speed; at the center a local minimum gives zero. (G03.c) -/
theorem hyperboloidRadius_deriv_le_pieceSpeed
    {γ : ℝ → Hyperboloid} {a b t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (ht : t ∈ Ioo a b)
    (hρ : DifferentiableAt ℝ (fun s => hyperboloidRadius (γ s)) t) :
  letI : Bundle.RiemannianBundle
      (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  |deriv (fun s => hyperboloidRadius (γ s)) t| ≤
    ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖ := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  by_cases hz : hyperboloidRadius (γ t) = 0
  · have hd : deriv (fun s => hyperboloidRadius (γ s)) t = 0 := by
      apply IsLocalMin.deriv_eq_zero
      apply Filter.Eventually.of_forall
      intro s
      change hyperboloidRadius (γ t) ≤ hyperboloidRadius (γ s)
      rw [hz]
      exact (hyperboloidRadius_properties (γ s)).1
    rw [hd, abs_zero]
    exact norm_nonneg _
  · have hr : 0 < hyperboloidRadius (γ t) :=
      lt_of_le_of_ne (hyperboloidRadius_properties (γ t)).1 (Ne.symm hz)
    obtain ⟨U, θ, hU, hmem, hrad, hθ, hpos, hrec⟩ := hyperboloidPolar_local_coordinates hr
    have hg := hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
    have ha := ((hθ.contMDiffAt (hU.mem_nhds hmem)).of_le (by simp)).comp t hg
    have hda := ha.contDiffAt.differentiableAt one_ne_zero
    have he : γ =ᶠ[nhds t] (fun s => hyperboloidPolar (hyperboloidRadius (γ s)) (θ (γ s))) := by
      filter_upwards [hg.continuousAt (hU.mem_nhds hmem)] with s hs
      exact (hrec (γ s) hs).symm
    have hspeed := hyperboloidPolar_curve_speed γ
      (fun s => hyperboloidRadius (γ s)) (fun s => θ (γ s)) t
      (deriv (fun s => hyperboloidRadius (γ s)) t) (deriv (fun s => θ (γ s)) t)
      hρ.hasDerivAt hda.hasDerivAt he
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hspeed]
    exact Real.abs_le_sqrt
      (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Radial derivative is bounded by the same piece speed almost everywhere, removing only endpoint singletons. (G03.c) -/
theorem hyperboloidRadius_ae_deriv_le_pieceSpeed
    {γ : ℝ → Hyperboloid} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
  letI : Bundle.RiemannianBundle
      (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  ∀ᵐ t ∂volume.restrict (Ioc a b),
    |deriv (fun s => hyperboloidRadius (γ s)) t| ≤
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖ := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  obtain ⟨κ, hκ⟩ := hyperboloidRadius_lipschitzOn_piece hab hγ
  have hac : AbsolutelyContinuousOnInterval (fun t => hyperboloidRadius (γ t)) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab.le] using hκ
  rw [← restrict_Ioo_eq_restrict_Ioc]
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hac.ae_differentiableAt] with t ht hmem
  have hmem' : t ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨hmem.1.le, hmem.2.le⟩
  exact hyperboloidRadius_deriv_le_pieceSpeed hγ hmem (ht hmem')

/-- Scalar absolute continuity bounds each piece's extended variation, hence its finite real variation, by its length. (G03.c) -/
theorem hyperboloidRadius_piece_variation
    {γ : ℝ → Hyperboloid} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
  letI : Bundle.RiemannianBundle
      (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := ∫ t in a..b,
    ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖
  eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b) ≤
      ENNReal.ofReal L ∧
    eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b) ≠ ⊤ ∧
    (eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b)).toReal ≤ L := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L := ∫ t in a..b, ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖
  obtain ⟨κ, hκ⟩ := hyperboloidRadius_lipschitzOn_piece hab hγ
  have hac : AbsolutelyContinuousOnInterval (fun t => hyperboloidRadius (γ t)) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab.le] using hκ
  have hspeed : IntervalIntegrable
      (fun t => ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      (Manifold.continuousOn_pieceSpeed hyperboloidMetric γ hab hγ).integrableOn_Icc
  have hae : ∀ᵐ t ∂volume.restrict (Icc a b),
      |deriv (fun s => hyperboloidRadius (γ s)) t| ≤
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖ := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact hyperboloidRadius_ae_deriv_le_pieceSpeed hab hγ
  have hInt : (∫ t in a..b, |deriv (fun s => hyperboloidRadius (γ s)) t|) ≤ L :=
    intervalIntegral.integral_mono_ae_restrict
      hab.le hac.intervalIntegrable_deriv.abs hspeed hae
  have hbound : eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b) ≤ ENNReal.ofReal L :=
    (hac.eVariationOn_le_ofReal_integral_abs_deriv hab.le).trans (ENNReal.ofReal_le_ofReal hInt)
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg hab.le (fun t ht => norm_nonneg _)
  refine ⟨hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hL)

/-- Finite variation additivity on the weak subdivision bounds whole radial variation and endpoint change by actual piecewise length. (G03.c) -/
theorem hyperboloidRadius_variation_le_length
    {γ : ℝ → Hyperboloid} {a b : ℝ} {n : ℕ}
    {cut : Fin (n + 1) → ℝ}
    (hγ : Manifold.IsPiecewiseC1On I γ a b n cut) :
  AbsolutelyContinuousOnInterval (fun t => hyperboloidRadius (γ t)) a b ∧
  eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b) ≤
    ENNReal.ofReal (Manifold.piecewiseC1Length hyperboloidMetric γ cut) ∧
  eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b) ≠ ⊤ ∧
  |hyperboloidRadius (γ b) - hyperboloidRadius (γ a)| ≤
    (eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b)).toReal ∧
  (eVariationOn (fun t => hyperboloidRadius (γ t)) (Icc a b)).toReal ≤
    Manifold.piecewiseC1Length hyperboloidMetric γ cut := by
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace I q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let f : ℝ → ℝ := fun t => hyperboloidRadius (γ t)
  have hc : Monotone cut := hγ.1
  have hsumcut : (∑ i : Fin n, eVariationOn f (Icc (cut i.castSucc) (cut i.succ))) =
      eVariationOn f (Icc (cut 0) (cut (Fin.last n))) := by
    let u : ℕ → ℝ :=
      fun k => cut ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right k n)⟩
    have hu : Monotone u := by
      intro i j hij
      apply hc
      change min i n ≤ min j n
      exact min_le_min_right n hij
    have h0 : u 0 = cut 0 := by simp [u]
    have hn : u n = cut (Fin.last n) := by simp [u, Fin.last]
    have hleft (i : Fin n) : u i.val = cut i.castSucc := by
      dsimp [u]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left i.isLt.le
    have hright (i : Fin n) : u (i.val+1) = cut i.succ := by
      dsimp [u]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left (by omega)
    have hFinRange :
        (∑ i : Fin n, eVariationOn f (Icc (u i.val) (u (i.val+1)))) =
          ∑ k ∈ Finset.range n, eVariationOn f (Icc (u k) (u (k+1))) :=
      Fin.sum_univ_eq_sum_range
        (fun k => eVariationOn f (Icc (u k) (u (k+1)))) n
    calc
      (∑ i : Fin n, eVariationOn f (Icc (cut i.castSucc) (cut i.succ))) =
          ∑ i : Fin n, eVariationOn f (Icc (u i.val) (u (i.val+1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hleft i, hright i]
      _ = ∑ k ∈ Finset.range n, eVariationOn f (Icc (u k) (u (k+1))) := hFinRange
      _ = eVariationOn f (Icc (u 0) (u n)) := eVariationOn.sum' f hu
      _ = eVariationOn f (Icc (cut 0) (cut (Fin.last n))) := by rw [h0, hn]
  let L : Fin n → ℝ := fun i =>
    ∫ t in cut i.castSucc..cut i.succ,
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
  have hle (i : Fin n) : cut i.castSucc ≤ cut i.succ :=
    hγ.1 (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
  have hnonneg (i : Fin n) : 0 ≤ L i :=
    intervalIntegral.integral_nonneg (hle i) (fun t ht => norm_nonneg _)
  have hpiece (i : Fin n) :
      eVariationOn f (Icc (cut i.castSucc) (cut i.succ)) ≤ ENNReal.ofReal (L i) := by
    rcases lt_or_eq_of_le (hle i) with hi | hi
    · exact (hyperboloidRadius_piece_variation hi (hγ.2.2.2.2 i hi)).1
    · simp [L, hi]
  have hsum : (∑ i : Fin n, eVariationOn f (Icc (cut i.castSucc) (cut i.succ))) =
      eVariationOn f (Icc a b) := by
    rw [hsumcut, hγ.2.1, hγ.2.2.1]
  have hlength : Manifold.piecewiseC1Length hyperboloidMetric γ cut = ∑ i : Fin n, L i := rfl
  have hbound : eVariationOn f (Icc a b) ≤
      ENNReal.ofReal (Manifold.piecewiseC1Length hyperboloidMetric γ cut) := by
    rw [← hsum, hlength, ENNReal.ofReal_sum_of_nonneg (fun i hi => hnonneg i)]
    exact Finset.sum_le_sum (fun i hi => hpiece i)
  have hL : 0 ≤ Manifold.piecewiseC1Length hyperboloidMetric γ cut := by
    rw [hlength]
    exact Finset.sum_nonneg (fun i hi => hnonneg i)
  have hfinite : eVariationOn f (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hab : a ≤ b := by
    rw [← hγ.2.1, ← hγ.2.2.1]
    exact hγ.1 (Fin.zero_le _)
  refine ⟨hyperboloidRadius_absolutelyContinuous hγ, hbound, hfinite, ?_, ?_⟩
  · have hv : BoundedVariationOn f (Icc a b) := hfinite
    simpa only [Real.dist_eq] using
      hv.dist_le (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
        (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hL)


/-! Centered radial realization and equality in the length bound (G03.d–e). -/

/-- The fixed-target radial curve is constant at the center when its radius is zero. (G03.d) -/
def hyperboloidRadialCurve (q : Hyperboloid) (s : ℝ) : Hyperboloid :=
  if hyperboloidRadius q = 0 then hyperboloidPolar 0 0
  else hyperboloidPolar s (Complex.arg (hyperboloidSpatial q))

/-- The radial competitor is smooth with the prescribed endpoints; at positive radius its SAME-metric speed is one. (G03.d) -/
theorem hyperboloidRadialCurve_properties (q : Hyperboloid) :
  ContMDiff 𝓘(ℝ, ℝ) I ∞ (hyperboloidRadialCurve q) ∧
  hyperboloidRadialCurve q 0 = hyperboloidPolar 0 0 ∧
  hyperboloidRadialCurve q (hyperboloidRadius q) = q ∧
  (hyperboloidRadius q = 0 →
    ∀ s, hyperboloidRadialCurve q s = hyperboloidPolar 0 0) ∧
  (0 < hyperboloidRadius q →
    letI : Bundle.RiemannianBundle
        (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ∀ s : ℝ, ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidRadialCurve q) s (1 : ℝ)‖ = 1) := by
  have radialSmooth (q : Hyperboloid) :
      ContMDiff 𝓘(ℝ, ℝ) I ∞ (hyperboloidRadialCurve q) := by
    by_cases hz : hyperboloidRadius q = 0
    · change ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s => hyperboloidRadialCurve q s)
      simpa only [hyperboloidRadialCurve, if_pos hz] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) I ∞
          (fun _ : ℝ => hyperboloidPolar 0 0))
    · have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
          (fun s : ℝ => (s, Complex.arg (hyperboloidSpatial q))) :=
        contMDiff_id.prodMk_space contMDiff_const
      change ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s => hyperboloidRadialCurve q s)
      simpa only [hyperboloidRadialCurve, if_neg hz, Function.comp_def] using
        contMDiff_hyperboloidPolar.comp hp
  have radialEndpoints (q : Hyperboloid) :
      hyperboloidRadialCurve q 0 = hyperboloidPolar 0 0 ∧
      hyperboloidRadialCurve q (hyperboloidRadius q) = q ∧
      (hyperboloidRadius q = 0 →
        ∀ s, hyperboloidRadialCurve q s = hyperboloidPolar 0 0) := by
    have hc (θ : ℝ) : hyperboloidPolar 0 θ = hyperboloidPolar 0 0 := by
      apply Subtype.ext
      exact (hyperboloidPolar_center_direction θ q).1.trans
        (hyperboloidPolar_center_direction 0 q).1.symm
    by_cases hz : hyperboloidRadius q = 0
    · have hq : q = hyperboloidPolar 0 0 := by
        apply Subtype.ext
        exact ((hyperboloidRadius_properties q).2.2.2.1.mp hz).trans
          (hyperboloidPolar_center_direction 0 q).1.symm
      simp only [hyperboloidRadialCurve, if_pos hz]
      exact ⟨True.intro, hq.symm, fun _ _ => True.intro⟩
    · refine ⟨?_, ?_, fun h => (hz h).elim⟩
      · simpa only [hyperboloidRadialCurve, if_neg hz] using
          hc (Complex.arg (hyperboloidSpatial q))
      · simpa only [hyperboloidRadialCurve, if_neg hz] using hyperboloidPolar_arg q
  have radialSpeed (q : Hyperboloid) (hq : 0 < hyperboloidRadius q) :
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      ∀ s : ℝ, ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidRadialCurve q) s (1 : ℝ)‖ = 1 := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    intro s
    have hlocal : ∀ᶠ t in nhds s, hyperboloidRadialCurve q t =
        hyperboloidPolar t (Complex.arg (hyperboloidSpatial q)) :=
      Filter.Eventually.of_forall (fun t => by
        simp only [hyperboloidRadialCurve, if_neg (ne_of_gt hq)])
    have hspeed := hyperboloidPolar_curve_speed (hyperboloidRadialCurve q)
      (fun t : ℝ => t) (fun _ : ℝ => Complex.arg (hyperboloidSpatial q)) s 1 0
      (hasDerivAt_id s) (hasDerivAt_const s _) hlocal
    simpa using hspeed
  exact ⟨radialSmooth q, (radialEndpoints q).1, (radialEndpoints q).2.1,
    (radialEndpoints q).2.2, radialSpeed q⟩

/-- The one-piece radial competitor realizes its radius as both real and extended finite length, including radius zero. (G03.d) -/
theorem hyperboloidRadialCurve_length (q : Hyperboloid) :
  let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
  letI : Bundle.RiemannianBundle
      (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  IsPiecewiseC1On I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) 1 cut ∧
  piecewiseC1Length hyperboloidMetric (hyperboloidRadialCurve q) cut =
    hyperboloidRadius q ∧
  pathELength I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) =
    ENNReal.ofReal (hyperboloidRadius q) ∧
  pathELength I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) < ⊤ := by
  have radialWitness (q : Hyperboloid) :
      let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
      IsPiecewiseC1On I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) 1 cut := by
    let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
    have hs := (hyperboloidRadialCurve_properties q).1
    refine ⟨?_, by simp [cut], by simp [cut], hs.continuous.continuousOn, ?_⟩
    · intro i j hij
      have hR := (hyperboloidRadius_properties q).1
      fin_cases i <;> fin_cases j <;> simp_all [cut]
    · intro i hi
      exact (hs.of_le (by simp)).contMDiffOn
  have radialIntegral (q : Hyperboloid) :
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      (∫ s in (0 : ℝ)..hyperboloidRadius q,
        ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidRadialCurve q) s (1 : ℝ)‖) =
        hyperboloidRadius q := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    by_cases hz : hyperboloidRadius q = 0
    · simp [hz]
    · have hp : 0 < hyperboloidRadius q :=
        lt_of_le_of_ne (hyperboloidRadius_properties q).1 (Ne.symm hz)
      have hs := (hyperboloidRadialCurve_properties q).2.2.2.2 hp
      simp only [hs, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have radialLengthPack (q : Hyperboloid)
      (hw : let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
        IsPiecewiseC1On I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) 1 cut)
      (hi : letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
          ⟨hyperboloidMetric.toRiemannianMetric⟩
        (∫ s in (0 : ℝ)..hyperboloidRadius q,
          ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidRadialCurve q) s (1 : ℝ)‖) =
          hyperboloidRadius q) :
      let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      piecewiseC1Length hyperboloidMetric (hyperboloidRadialCurve q) cut = hyperboloidRadius q ∧
      pathELength I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) =
        ENNReal.ofReal (hyperboloidRadius q) ∧
      pathELength I (hyperboloidRadialCurve q) 0 (hyperboloidRadius q) < ⊤ := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    rcases hw.speed_length hyperboloidMetric with
      ⟨hpInt, hpInterval, hmeas, hInt, hreal, hset, hnonneg,
        hofpiece, hfinpiece, hsum, hlin, hpath, hfinite⟩
    have hL := hreal.symm.trans hi
    exact ⟨hL, hpath.trans (congrArg ENNReal.ofReal hL), hfinite⟩
  exact ⟨radialWitness q, radialLengthPack q (radialWitness q) (radialIntegral q)⟩

/-- The actual all-family length infimum from the center equals the radius, by both competitor inequalities. (G03.d) -/
theorem hyperboloid_centered_piecewiseC1EDist (q : Hyperboloid) :
  ENNReal.ofReal (hyperboloidRadius q) ≤
    piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ∧
  piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ≤
    ENNReal.ofReal (hyperboloidRadius q) ∧
  piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q =
    ENNReal.ofReal (hyperboloidRadius q) ∧
  piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q < ⊤ ∧
  (piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q).toReal =
    hyperboloidRadius q := by
  have radialUpper (q : Hyperboloid) :
      piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ≤
        ENNReal.ofReal (hyperboloidRadius q) := by
    let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else hyperboloidRadius q
    have hp := hyperboloidRadialCurve_properties q
    have hL := hyperboloidRadialCurve_length q
    let γ : PiecewiseC1CurveOn I 0 (hyperboloidRadius q) 1 cut
        (hyperboloidPolar 0 0) q :=
      ⟨hyperboloidRadialCurve q, hL.1, hp.2.1, hp.2.2.1⟩
    have h := (piecewiseC1EDist_finite_of_curve hyperboloidMetric γ).1
    change piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ≤
      ENNReal.ofReal (piecewiseC1Length hyperboloidMetric (hyperboloidRadialCurve q) cut) at h
    exact h.trans_eq (congrArg ENNReal.ofReal hL.2.1)
  have radialLower (q : Hyperboloid) :
      ENNReal.ofReal (hyperboloidRadius q) ≤
        piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q := by
    unfold piecewiseC1EDist
    refine le_iInf (fun a => le_iInf (fun b => le_iInf (fun n =>
      le_iInf (fun cut => le_iInf (fun γ => ?_)))))
    have h := hyperboloidRadius_variation_le_length γ.property.1
    have hb := h.2.2.2.1.trans h.2.2.2.2
    have hR : hyperboloidRadius q ≤ piecewiseC1Length hyperboloidMetric γ.val cut := by
      simpa only [γ.property.2.1, γ.property.2.2,
        hyperboloidPolar_radius (le_refl 0) 0, sub_zero,
        abs_of_nonneg (hyperboloidRadius_properties q).1] using hb
    exact ENNReal.ofReal_le_ofReal hR
  have radialDistancePack (q : Hyperboloid)
      (hl : ENNReal.ofReal (hyperboloidRadius q) ≤
        piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q)
      (hu : piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ≤
        ENNReal.ofReal (hyperboloidRadius q)) :
      ENNReal.ofReal (hyperboloidRadius q) ≤
        piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ∧
      piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q ≤
        ENNReal.ofReal (hyperboloidRadius q) ∧
      piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q =
        ENNReal.ofReal (hyperboloidRadius q) ∧
      piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q < ⊤ ∧
      (piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) q).toReal =
        hyperboloidRadius q := by
    have he := le_antisymm hu hl
    refine ⟨hl, hu, he, hu.trans_lt ENNReal.ofReal_lt_top, ?_⟩
    rw [he, ENNReal.toReal_ofReal (hyperboloidRadius_properties q).1]
  exact radialDistancePack q (radialLower q) (radialUpper q)

/-- Proof-local sharing of the actual two loss sums, finite variation squeeze and radial monotonicity. -/
private theorem hyperboloid_centered_loss_data {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
    let v : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
    (eVariationOn ρ (Icc a b)).toReal = hyperboloidRadius q ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, v i t - |deriv ρ t|) = 0) ∧
    (∀ i : Fin n, (∫ t in cut i.castSucc..cut i.succ, |deriv ρ t| - deriv ρ t) = 0) ∧
    (∀ i : Fin n, ∀ᵐ t ∂volume.restrict (Ioc (cut i.castSucc) (cut i.succ)),
      v i t = |deriv ρ t| ∧ |deriv ρ t| = deriv ρ t) ∧
    MonotoneOn ρ (Icc a b) := by
  have lossL01 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) : a ≤ b ∧
      AbsolutelyContinuousOnInterval (fun t => hyperboloidRadius (γ.val t)) a b ∧
      (∫ t in a..b, deriv (fun s => hyperboloidRadius (γ.val s)) t) =
        hyperboloidRadius q := by
    have hab : a ≤ b := by
      rw [← γ.property.1.2.1, ← γ.property.1.2.2.1]
      exact γ.property.1.1 (Fin.zero_le _)
    have hac := hyperboloidRadius_absolutelyContinuous γ.property.1
    refine ⟨hab, hac, ?_⟩
    simpa only [γ.property.2.1, γ.property.2.2,
      hyperboloidPolar_radius (le_refl 0) 0, sub_zero] using hac.integral_deriv_eq_sub
  have lossL02 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) :
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
      let v : Fin n → ℝ → ℝ := fun i t =>
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
      ∀ i : Fin n,
        IntervalIntegrable (v i) volume (cut i.castSucc) (cut i.succ) ∧
        IntervalIntegrable (deriv ρ) volume (cut i.castSucc) (cut i.succ) ∧
        (∀ᵐ t ∂volume.restrict (Ioc (cut i.castSucc) (cut i.succ)),
          |deriv ρ t| ≤ v i t) := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    have hc := γ.property.1.1
    have hab : a ≤ b := by
      rw [← γ.property.1.2.1, ← γ.property.1.2.2.1]
      exact hc (Fin.zero_le _)
    have hac := hyperboloidRadius_absolutelyContinuous γ.property.1
    dsimp only
    intro i
    have hi : cut i.castSucc ≤ cut i.succ := hc (by change i.val ≤ i.val+1; omega)
    have hsub : uIcc (cut i.castSucc) (cut i.succ) ⊆ uIcc a b := by
      rw [uIcc_of_le hi, uIcc_of_le hab]
      intro t ht
      have hl : a ≤ cut i.castSucc := by
        rw [← γ.property.1.2.1]
        exact hc (Fin.zero_le _)
      have hr : cut i.succ ≤ b := by
        rw [← γ.property.1.2.2.1]
        exact hc (Fin.le_last _)
      exact ⟨hl.trans ht.1, ht.2.trans hr⟩
    refine ⟨(γ.property.1.speed_length hyperboloidMetric).2.1 i,
      (hac.mono hsub).intervalIntegrable_deriv, ?_⟩
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact hyperboloidRadius_ae_deriv_le_pieceSpeed hlt (γ.property.1.2.2.2.2 i hlt)
    · simp [heq]
  have lossL03 {l r : ℝ} {s d : ℝ → ℝ}
      (hs : IntervalIntegrable s volume l r)
      (hd : IntervalIntegrable d volume l r)
      (hbound : ∀ᵐ t ∂volume.restrict (Ioc l r), |d t| ≤ s t) :
      IntervalIntegrable (fun t => s t - |d t|) volume l r ∧
      IntervalIntegrable (fun t => |d t| - d t) volume l r ∧
      (0 ≤ᵐ[volume.restrict (Ioc l r)] (fun t => s t - |d t|)) ∧
      (0 ≤ᵐ[volume.restrict (Ioc l r)] (fun t => |d t| - d t)) := by
    refine ⟨hs.sub hd.abs, hd.abs.sub hd, ?_, ?_⟩
    · filter_upwards [hbound] with t ht
      exact sub_nonneg.mpr ht
    · exact Filter.Eventually.of_forall (fun t => sub_nonneg.mpr (le_abs_self (d t)))
  have lossL04 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b) :
      (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, g t) = ∫ t in a..b, g t := by
    have hc := γ.property.1.1
    let u : ℕ → ℝ := fun k => cut ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right k n)⟩
    have hu : Monotone u := by
      intro i j hij
      apply hc
      change min i n ≤ min j n
      exact min_le_min_right n hij
    have h0 : u 0 = a := by simpa [u] using γ.property.1.2.1
    have hn : u n = b := by simpa [u, Fin.last] using γ.property.1.2.2.1
    have hleft (i : Fin n) : u i.val = cut i.castSucc := by
      dsimp [u]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left i.isLt.le
    have hright (i : Fin n) : u (i.val+1) = cut i.succ := by
      dsimp [u]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left (by omega)
    have hab : a ≤ b := by simpa only [h0, hn] using hu (Nat.zero_le n)
    have hsub (k : ℕ) (hk : k < n) : uIcc (u k) (u (k+1)) ⊆ uIcc a b := by
      rw [uIcc_of_le (hu (Nat.le_succ k)), uIcc_of_le hab]
      intro t ht
      constructor
      · exact (show a ≤ u k from h0 ▸ hu (Nat.zero_le k)).trans ht.1
      · exact ht.2.trans (show u (k+1) ≤ b from hn ▸ hu (by omega))
    calc
      (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, g t) =
          ∑ i : Fin n, ∫ t in u i.val..u (i.val+1), g t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hleft i, hright i]
      _ = ∑ k ∈ Finset.range n, ∫ t in u k..u (k+1), g t :=
        Fin.sum_univ_eq_sum_range (fun k => ∫ t in u k..u (k+1), g t) n
      _ = ∫ t in u 0..u n, g t :=
        intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hg.mono_set (hsub k hk))
      _ = ∫ t in a..b, g t := by rw [h0, hn]
  have lossL05 (lossA lossB : Fin n → ℝ) (lossJ R : ℝ)
      (hA : ∀ i, 0 ≤ lossA i) (hB : ∀ i, 0 ≤ lossB i)
      (hsA : (∑ i, lossA i) = R - lossJ) (hsB : (∑ i, lossB i) = lossJ - R) :
      lossJ = R ∧ (∀ i, lossA i = 0) ∧ (∀ i, lossB i = 0) := by
    have ha : 0 ≤ ∑ i, lossA i := Finset.sum_nonneg (fun i hi => hA i)
    have hb : 0 ≤ ∑ i, lossB i := Finset.sum_nonneg (fun i hi => hB i)
    have hJ : lossJ = R := by rw [hsA] at ha; rw [hsB] at hb; linarith
    have ha0 : (∑ i, lossA i) = 0 := by rw [hsA, hJ, sub_self]
    have hb0 : (∑ i, lossB i) = 0 := by rw [hsB, hJ, sub_self]
    refine ⟨hJ, ?_, ?_⟩
    · exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hA j)).mp ha0 i (Finset.mem_univ i)
    · exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hB j)).mp hb0 i (Finset.mem_univ i)
  have lossL06 {l r : ℝ} {loss : ℝ → ℝ} (hlr : l ≤ r)
      (hn : 0 ≤ᵐ[volume.restrict (Ioc l r)] loss) :
      0 ≤ ∫ t in l..r, loss t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hlr
    simpa only [restrict_Ioc_eq_restrict_Icc] using hn
  have lossL07 {l r : ℝ} {s d : ℝ → ℝ} (hlr : l ≤ r)
      (hI : IntervalIntegrable (fun t => s t - |d t|) volume l r)
      (hJ : IntervalIntegrable (fun t => |d t| - d t) volume l r)
      (hN : 0 ≤ᵐ[volume.restrict (Ioc l r)] (fun t => s t - |d t|))
      (hM : 0 ≤ᵐ[volume.restrict (Ioc l r)] (fun t => |d t| - d t))
      (hZ : (∫ t in l..r, s t - |d t|) = 0)
      (hW : (∫ t in l..r, |d t| - d t) = 0) :
      ∀ᵐ t ∂volume.restrict (Ioc l r), s t = |d t| ∧ |d t| = d t := by
    have h1 := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hlr hN hI).mp hZ
    have h2 := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hlr hM hJ).mp hW
    filter_upwards [h1, h2] with t ht hu
    exact ⟨sub_eq_zero.mp ht, sub_eq_zero.mp hu⟩
  have lossL08 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
      eVariationOn (fun t => hyperboloidRadius (γ.val t)) (Icc a b) ≠ ⊤ ∧
      (eVariationOn (fun t => hyperboloidRadius (γ.val t)) (Icc a b)).toReal =
        hyperboloidRadius q := by
    have h := hyperboloidRadius_variation_le_length γ.property.1
    refine ⟨h.2.2.1, le_antisymm ?_ ?_⟩
    · exact h.2.2.2.2.trans_eq hmin
    · simpa only [γ.property.2.1, γ.property.2.2,
        hyperboloidPolar_radius (le_refl 0) 0, sub_zero,
        abs_of_nonneg (hyperboloidRadius_properties q).1] using h.2.2.2.1
  have lossL09 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) (hJ : (∫ t in a..b, |deriv (fun s => hyperboloidRadius (γ.val s)) t|) =
        hyperboloidRadius q) :
      MonotoneOn (fun t => hyperboloidRadius (γ.val t)) (Icc a b) := by
    have hac := hyperboloidRadius_absolutelyContinuous γ.property.1
    have hab : a ≤ b := by
      rw [← γ.property.1.2.1, ← γ.property.1.2.2.1]
      exact γ.property.1.1 (Fin.zero_le _)
    apply AbsolutelyContinuousOnInterval.monotoneOn_of_integral_abs_deriv_eq_sub hac hab
    simpa only [γ.property.2.1, γ.property.2.2,
      hyperboloidPolar_radius (le_refl 0) 0, sub_zero] using hJ
  have lossL10 (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q) (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      (hI : letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
          ⟨hyperboloidMetric.toRiemannianMetric⟩
        ∀ i : Fin n,
          IntervalIntegrable (fun t => ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val
            (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖)
            volume (cut i.castSucc) (cut i.succ) ∧
          IntervalIntegrable (deriv (fun s => hyperboloidRadius (γ.val s)))
            volume (cut i.castSucc) (cut i.succ))
      (hsumD : (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ,
          deriv (fun s => hyperboloidRadius (γ.val s)) t) =
        ∫ t in a..b, deriv (fun s => hyperboloidRadius (γ.val s)) t)
      (hsumA : (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ,
          |deriv (fun s => hyperboloidRadius (γ.val s)) t|) =
        ∫ t in a..b, |deriv (fun s => hyperboloidRadius (γ.val s)) t|) :
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
      let v : Fin n → ℝ → ℝ := fun i t =>
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
      ((∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, v i t - |deriv ρ t|) =
        hyperboloidRadius q - ∫ t in a..b, |deriv ρ t|) ∧
      ((∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, |deriv ρ t| - deriv ρ t) =
        (∫ t in a..b, |deriv ρ t|) - hyperboloidRadius q) := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
    let v : Fin n → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
    have hFTC : (∫ t in a..b, deriv ρ t) = hyperboloidRadius q := by
      simpa only [γ.property.2.1, γ.property.2.2,
        hyperboloidPolar_radius (le_refl 0) 0, sub_zero] using
        (hyperboloidRadius_absolutelyContinuous γ.property.1).integral_deriv_eq_sub
    have hspeed : (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, v i t) =
        hyperboloidRadius q := hmin
    constructor
    · calc
        (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, v i t - |deriv ρ t|) =
            ∑ i : Fin n, ((∫ t in cut i.castSucc..cut i.succ, v i t) -
              ∫ t in cut i.castSucc..cut i.succ, |deriv ρ t|) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact intervalIntegral.integral_sub (hI i).1 (hI i).2.abs
        _ = hyperboloidRadius q - ∫ t in a..b, |deriv ρ t| := by
          rw [Finset.sum_sub_distrib, hspeed, hsumA]
    · calc
        (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, |deriv ρ t| - deriv ρ t) =
            ∑ i : Fin n, ((∫ t in cut i.castSucc..cut i.succ, |deriv ρ t|) -
              ∫ t in cut i.castSucc..cut i.succ, deriv ρ t) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact intervalIntegral.integral_sub (hI i).2.abs (hI i).2
        _ = (∫ t in a..b, |deriv ρ t|) - hyperboloidRadius q := by
          rw [Finset.sum_sub_distrib, hsumA, hsumD, hFTC]
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
  let v : Fin n → ℝ → ℝ := fun i t =>
    ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖
  let lossA : Fin n → ℝ := fun i => ∫ t in cut i.castSucc..cut i.succ, v i t - |deriv ρ t|
  let lossB : Fin n → ℝ := fun i => ∫ t in cut i.castSucc..cut i.succ, |deriv ρ t| - deriv ρ t
  let lossJ : ℝ := ∫ t in a..b, |deriv ρ t|
  have hac := (lossL01 γ).2.1
  have hp := lossL02 γ
  have hi (i : Fin n) : cut i.castSucc ≤ cut i.succ :=
    γ.property.1.1 (by change i.val ≤ i.val+1; omega)
  have hl (i : Fin n) := lossL03 (hp i).1 (hp i).2.1 (hp i).2.2
  have hA (i : Fin n) : 0 ≤ lossA i := lossL06 (hi i) (hl i).2.2.1
  have hB (i : Fin n) : 0 ≤ lossB i := lossL06 (hi i) (hl i).2.2.2
  have hsumD := lossL04 γ (deriv ρ) hac.intervalIntegrable_deriv
  have hsumA := lossL04 γ (fun t => |deriv ρ t|) hac.intervalIntegrable_deriv.abs
  have hs := lossL10 γ hmin (fun i => ⟨(hp i).1, (hp i).2.1⟩) hsumD hsumA
  have hz := lossL05 lossA lossB lossJ (hyperboloidRadius q) hA hB hs.1 hs.2
  refine ⟨(lossL08 γ hmin).2, hz.2.1, hz.2.2, ?_, lossL09 γ hz.1⟩
  intro i
  exact lossL07 (hi i) (hl i).1 (hl i).2.1 (hl i).2.2.1 (hl i).2.2.2
    (hz.2.1 i) (hz.2.2 i)

/-- A centered minimizing curve has zero speed-versus-radial and radial-backtracking losses on every weak piece. (G03.e) -/
theorem hyperboloid_centered_minimizer_losses
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
  letI : Bundle.RiemannianBundle
      (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
  (eVariationOn ρ (Icc a b)).toReal = hyperboloidRadius q ∧
  (∀ i : Fin n,
    (∫ t in cut i.castSucc..cut i.succ,
      (‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val
          (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ -
        |deriv ρ t|)) = 0) ∧
  (∀ i : Fin n,
    (∫ t in cut i.castSucc..cut i.succ,
      (|deriv ρ t| - deriv ρ t)) = 0) ∧
  (∀ i : Fin n, ∀ᵐ t ∂volume.restrict (Ioc (cut i.castSucc) (cut i.succ)),
    ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val
        (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = |deriv ρ t| ∧
      |deriv ρ t| = deriv ρ t) := by
  rcases hyperboloid_centered_loss_data γ hmin with ⟨hV, hA, hB, hae, hm⟩
  exact ⟨hV, hA, hB, hae⟩

/-- The radius of a centered minimizing curve is nondecreasing on its whole closed parameter interval. (G03.e) -/
theorem hyperboloid_centered_minimizer_radius_monotone
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
  MonotoneOn (fun t => hyperboloidRadius (γ.val t)) (Icc a b) := by
  exact (hyperboloid_centered_loss_data γ hmin).2.2.2.2

/-- On positive-radius piece interiors the actual normalized spatial direction has derivative zero almost everywhere. (G03.e) -/
theorem hyperboloid_centered_minimizer_direction_deriv
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
  ∀ i : Fin n,
    ∀ᵐ t ∂volume.restrict
      (Ioo (cut i.castSucc) (cut i.succ) ∩
        {t | 0 < hyperboloidRadius (γ.val t)}),
      HasDerivAt
        (fun s => hyperboloidSpatial (γ.val s) /
          (‖hyperboloidSpatial (γ.val s)‖ : ℂ)) (0 : ℂ) t := by
  have directionA01 {γ : ℝ → Hyperboloid} {l r t : ℝ}
      (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc l r)) (ht : t ∈ Ioo l r)
      (hp : 0 < hyperboloidRadius (γ t)) :
      ∃ θ : Hyperboloid → ℝ,
        HasDerivAt (fun s => hyperboloidRadius (γ s))
          (deriv (fun s => hyperboloidRadius (γ s)) t) t ∧
        HasDerivAt (fun s => θ (γ s)) (deriv (fun s => θ (γ s)) t) t ∧
        (∀ᶠ s in nhds t, 0 < hyperboloidRadius (γ s) ∧
          γ s = hyperboloidPolar (hyperboloidRadius (γ s)) (θ (γ s))) := by
    obtain ⟨U, θ, hU, hmem, hrad, hθ, hpos, hrec⟩ := hyperboloidPolar_local_coordinates hp
    have hg := hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hr := ((hrad.contMDiffAt (hU.mem_nhds hmem)).of_le (by simp)).comp t hg
    have ha := ((hθ.contMDiffAt (hU.mem_nhds hmem)).of_le (by simp)).comp t hg
    refine ⟨θ, (hr.contDiffAt.differentiableAt one_ne_zero).hasDerivAt,
      (ha.contDiffAt.differentiableAt one_ne_zero).hasDerivAt, ?_⟩
    filter_upwards [hg.continuousAt (hU.mem_nhds hmem)] with s hs
    exact ⟨hpos (γ s) hs, (hrec (γ s) hs).symm⟩
  have directionA02 {γ : ℝ → Hyperboloid} {θ : Hyperboloid → ℝ} {l r t : ℝ}
      (ht : t ∈ Ioo l r) (hp : 0 < hyperboloidRadius (γ t))
      (hr : HasDerivAt (fun s => hyperboloidRadius (γ s))
        (deriv (fun s => hyperboloidRadius (γ s)) t) t)
      (ha : HasDerivAt (fun s => θ (γ s)) (deriv (fun s => θ (γ s)) t) t)
      (hrec : ∀ᶠ s in nhds t,
        γ s = hyperboloidPolar (hyperboloidRadius (γ s)) (θ (γ s)))
      (he : letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
          ⟨hyperboloidMetric.toRiemannianMetric⟩
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc l r) t (1 : ℝ)‖ =
          |deriv (fun s => hyperboloidRadius (γ s)) t|) :
      HasDerivAt (fun s => θ (γ s)) 0 t := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    have hv := hyperboloidPolar_curve_speed γ
      (fun s => hyperboloidRadius (γ s)) (fun s => θ (γ s)) t _ _ hr ha hrec
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hv] at he
    have hs : 0 < Real.sinh (hyperboloidRadius (γ t)) :=
      Real.arsinh_pos_iff.mp (by simpa only [Real.arsinh_sinh] using hp)
    have hnn : 0 ≤ (deriv (fun s => hyperboloidRadius (γ s)) t)^2 +
        (Real.sinh (hyperboloidRadius (γ t)))^2 * (deriv (fun s => θ (γ s)) t)^2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsq := Real.sq_sqrt hnn
    rw [he, sq_abs] at hsq
    have haz : deriv (fun s => θ (γ s)) t = 0 := by
      have hz : (Real.sinh (hyperboloidRadius (γ t)))^2 *
          (deriv (fun s => θ (γ s)) t)^2 = 0 := by nlinarith [hsq]
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (sq_pos_of_pos hs)))
    exact ha.congr_deriv haz
  have directionA03 (x : Hyperboloid) (r θ : ℝ) (hr : 0 < r)
      (hx : hyperboloidPolar r θ = x) :
      hyperboloidSpatial x / (‖hyperboloidSpatial x‖ : ℂ) =
        (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    have hs : 0 < Real.sinh r :=
      Real.arsinh_pos_iff.mp (by simpa only [Real.arsinh_sinh] using hr)
    have hn : ‖hyperboloidSpatial x‖ = Real.sinh r := by
      rw [← (hyperboloidRadius_properties x).2.1, ← hx, hyperboloidPolar_radius hr.le]
    have hsp : hyperboloidSpatial x = (Real.sinh r : ℂ) *
        ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
      rw [← hx]
      apply Complex.ext <;>
        simp [hyperboloidSpatial, hyperboloidPolar, hyperboloidPolarCoords,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh] <;> ring
    have hne : (‖hyperboloidSpatial x‖ : ℂ) ≠ 0 := by
      rw [hn]
      exact_mod_cast (ne_of_gt hs)
    rw [div_eq_iff hne, hn, hsp]
    ring
  have directionA04 {α : ℝ → ℝ} {t : ℝ} (ha : HasDerivAt α 0 t) :
      HasDerivAt (fun s => (Real.cos (α s) : ℂ) +
        (Real.sin (α s) : ℂ) * Complex.I) (0 : ℂ) t := by
    have hc := ha.cos.ofReal_comp
    have hs := ha.sin.ofReal_comp
    convert hc.add (hs.mul_const Complex.I) using 1 <;>
      first | rfl | simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero, Pi.add_def]
  have directionA05 {γ : ℝ → Hyperboloid} {α : ℝ → ℝ} {t : ℝ}
      (ha : HasDerivAt α 0 t)
      (he : (fun s => hyperboloidSpatial (γ s) / (‖hyperboloidSpatial (γ s)‖ : ℂ)) =ᶠ[nhds t]
        (fun s => (Real.cos (α s) : ℂ) + (Real.sin (α s) : ℂ) * Complex.I)) :
      HasDerivAt (fun s => hyperboloidSpatial (γ s) /
        (‖hyperboloidSpatial (γ s)‖ : ℂ)) (0 : ℂ) t := by
    have hd : HasDerivAt (fun s => (Real.cos (α s) : ℂ) +
        (Real.sin (α s) : ℂ) * Complex.I) (0 : ℂ) t := by
      exact directionA04 ha
    exact hd.congr_of_eventuallyEq he
  have directionA06 {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
      (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      (i : Fin n) :
      letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      ∀ᵐ t ∂volume.restrict (Ioo (cut i.castSucc) (cut i.succ) ∩
        {t | 0 < hyperboloidRadius (γ.val t)}),
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ =
          |deriv (fun s => hyperboloidRadius (γ.val s)) t| := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    have he := (hyperboloid_centered_minimizer_losses γ hmin).2.2.2 i
    have hs : Ioo (cut i.castSucc) (cut i.succ) ∩
        {t | 0 < hyperboloidRadius (γ.val t)} ⊆ Ioc (cut i.castSucc) (cut i.succ) :=
      fun t ht => ⟨ht.1.1, ht.1.2.le⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he] with t ht
    exact ht.1
  intro i
  let S := Ioo (cut i.castSucc) (cut i.succ) ∩
    {t | 0 < hyperboloidRadius (γ.val t)}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlt : cut i.castSucc < cut i.succ := ht.1.1.trans ht.1.2
    obtain ⟨θ, hr, ha, hrec⟩ := directionA01 (γ.property.1.2.2.2.2 i hlt) ht.1 ht.2
    have hp := hr.continuousAt (Ioi_mem_nhds ht.2)
    filter_upwards [Ioo_mem_nhds ht.1.1 ht.1.2, hp] with s hs hpos
    exact ⟨hs, hpos⟩
  have he := directionA06 γ hmin i
  filter_upwards [he, ae_restrict_mem hS.measurableSet] with t he ht
  have hlt : cut i.castSucc < cut i.succ := ht.1.1.trans ht.1.2
  obtain ⟨θ, hr, ha, hrec⟩ := directionA01 (γ.property.1.2.2.2.2 i hlt) ht.1 ht.2
  have haz := directionA02 ht.1 ht.2 hr ha (hrec.mono (fun s hs => hs.2)) he
  apply directionA05 haz
  filter_upwards [hrec] with s hs
  exact directionA03 (γ.val s) (hyperboloidRadius (γ.val s)) (θ (γ.val s)) hs.1 hs.2.symm

/-- Every two positive-radius points of a centered minimizing curve have the same spatial direction. (G03.e) -/
theorem hyperboloid_centered_minimizer_direction
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
  ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    0 < hyperboloidRadius (γ.val s) →
    0 < hyperboloidRadius (γ.val t) →
    hyperboloidSpatial (γ.val s) / (‖hyperboloidSpatial (γ.val s)‖ : ℂ) =
      hyperboloidSpatial (γ.val t) / (‖hyperboloidSpatial (γ.val t)‖ : ℂ) := by
  have positiveK3 {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
      (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
      (hp : 0 < hyperboloidRadius (γ.val s)) :
      ∀ u ∈ Icc s t,
        hyperboloidSpatial (γ.val u) / (‖hyperboloidSpatial (γ.val u)‖ : ℂ) =
          hyperboloidSpatial (γ.val s) / (‖hyperboloidSpatial (γ.val s)‖ : ℂ) := by
    let z : ℝ → ℂ := fun u => hyperboloidSpatial (γ.val u)
    let f : ℝ → ℂ := fun u => z u / (‖z u‖ : ℂ)
    let d : Fin (n+1) → ℝ := fun i => max s (min t (cut i))
    obtain ⟨hc, h0, hn, hcontinuous, hpieces⟩ := γ.property.1
    have hsub : Icc s t ⊆ Icc a b :=
      fun u hu => ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
    have hpos : ∀ u ∈ Icc s t, 0 < hyperboloidRadius (γ.val u) := by
      intro u hu
      exact hp.trans_le (hyperboloid_centered_minimizer_radius_monotone γ hmin
        hs (hsub hu) hu.1)
    have hz_ne : ∀ u ∈ Icc s t, z u ≠ 0 := by
      intro u hu hz
      have hr := (hyperboloidRadius_properties (γ.val u)).2.2.2.2.mp hz
      exact (ne_of_gt (hpos u hu)) hr
    have hn_ne : ∀ u ∈ Icc s t, (‖z u‖ : ℂ) ≠ 0 := by
      intro u hu
      exact_mod_cast (norm_ne_zero_iff.mpr (hz_ne u hu))
    have hd : Monotone d := by
      intro i j hij
      exact max_le_max_left s (min_le_min_left t (hc hij))
    have hd0 : d 0 = s := by
      change max s (min t (cut 0)) = s
      rw [h0]
      exact max_eq_left ((min_le_right _ _).trans hs.1)
    have hdn : d (Fin.last n) = t := by
      change max s (min t (cut (Fin.last n))) = t
      rw [hn, min_eq_left ht.2, max_eq_right hst]
    have hdmem : ∀ i, d i ∈ Icc s t := by
      intro i
      exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
    have hcontain (i : Fin n) (hi : d i.castSucc < d i.succ) :
        cut i.castSucc < cut i.succ ∧
        cut i.castSucc ≤ d i.castSucc ∧ d i.succ ≤ cut i.succ := by
      have hold := hc (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
      dsimp only [d] at hi ⊢
      constructor
      · by_contra h
        have he := le_antisymm hold (le_of_not_gt h)
        simpa only [he, lt_self_iff_false] using hi
      · constructor <;> grind
    have hnewsub (i : Fin n) : Icc (d i.castSucc) (d i.succ) ⊆ Icc s t :=
      fun u hu => ⟨(hdmem i.castSucc).1.trans hu.1, hu.2.trans (hdmem i.succ).2⟩
    let L : (Fin 3 → ℝ) →L[ℝ] ℂ :=
      Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).prod
          (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ))
    have hL (x : Hyperboloid) : L x.val = hyperboloidSpatial x := by
      apply Complex.ext <;> simp [L, hyperboloidSpatial]
    have hspatial : ContMDiff I I ∞ hyperboloidSpatial := by
      simpa only [Function.comp_def, hL] using
        L.contDiff.comp_contMDiff contMDiff_hyperboloid_val
    have hz_cont : ContinuousOn z (Icc s t) :=
      hspatial.continuous.comp_continuousOn (hcontinuous.mono hsub)
    have hf_cont : ContinuousOn f (Icc s t) := by
      exact hz_cont.div (Complex.continuous_ofReal.comp_continuousOn hz_cont.norm) hn_ne
    have hf_C1 : ∀ i : Fin n, d i.castSucc < d i.succ →
        ContDiffOn ℝ 1 f (Icc (d i.castSucc) (d i.succ)) := by
      intro i hi
      obtain ⟨hold, hleft, hright⟩ := hcontain i hi
      have hγ := (hpieces i hold).mono
        (show Icc (d i.castSucc) (d i.succ) ⊆ Icc (cut i.castSucc) (cut i.succ)
          from fun u hu => ⟨hleft.trans hu.1, hu.2.trans hright⟩)
      have hz : ContDiffOn ℝ 1 z (Icc (d i.castSucc) (d i.succ)) :=
        contMDiffOn_iff_contDiffOn.mp
          ((hspatial.of_le (by simp)).comp_contMDiffOn hγ)
      have hnrm := hz.norm ℝ (fun u hu => hz_ne u (hnewsub i hu))
      have hinv := hnrm.inv (fun u hu => norm_ne_zero_iff.mpr (hz_ne u (hnewsub i hu)))
      have hcast := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
      convert hz.mul hcast using 1
      all_goals
        first
        | rfl
        | funext u
          simp only [f, div_eq_mul_inv, Function.comp_apply, Complex.ofRealCLM_apply,
            Pi.inv_apply, Complex.ofReal_inv]
    have hf_zero : ∀ i : Fin n,
        ∀ᵐ u ∂volume.restrict (Ioo (d i.castSucc) (d i.succ)), HasDerivAt f (0 : ℂ) u := by
      intro i
      by_cases hi : d i.castSucc < d i.succ
      · obtain ⟨hold, hleft, hright⟩ := hcontain i hi
        have hset : Ioo (d i.castSucc) (d i.succ) ⊆
            Ioo (cut i.castSucc) (cut i.succ) ∩
              {u | 0 < hyperboloidRadius (γ.val u)} := by
          intro u hu
          exact ⟨⟨hleft.trans_lt hu.1, hu.2.trans_le hright⟩,
            hpos u (hnewsub i ⟨hu.1.le, hu.2.le⟩)⟩
        exact ae_restrict_of_ae_restrict_of_subset hset
          (hyperboloid_centered_minimizer_direction_deriv γ hmin i)
      · simp only [Ioo_eq_empty_of_le (le_of_not_gt hi), Measure.restrict_empty]
        simp
    exact AbsolutelyContinuousOnInterval.const_of_monotone_subdivision_of_ae_hasDerivAt_zero
      d hd hd0 hdn hf_cont hf_C1 hf_zero
  intro s hs t ht hsp htp
  rcases le_total s t with hst | hts
  · exact (positiveK3 γ hmin hs ht hst hsp t ⟨hst, le_rfl⟩).symm
  · exact positiveK3 γ hmin ht hs hts htp s ⟨hts, le_rfl⟩

/-- A centered minimizer has exactly the radial image, allowing pauses and monotone reparametrizations. (G03.e) -/
theorem hyperboloid_centered_minimizer_image
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
  (∀ t ∈ Icc a b,
    γ.val t = hyperboloidRadialCurve q (hyperboloidRadius (γ.val t))) ∧
  γ.val '' Icc a b =
    hyperboloidRadialCurve q '' Icc 0 (hyperboloidRadius q) := by
  have finalV01 {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
      (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
      let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
      a ≤ b ∧ ρ a = 0 ∧ ρ b = hyperboloidRadius q ∧
        AbsolutelyContinuousOnInterval ρ a b ∧
        (∀ t ∈ Icc a b, ρ t ∈ Icc 0 (hyperboloidRadius q)) ∧
        Icc 0 (hyperboloidRadius q) ⊆ ρ '' Icc a b := by
    let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
    have hab : a ≤ b := by
      simpa only [γ.property.1.2.1, γ.property.1.2.2.1] using
        γ.property.1.1 (show (0 : Fin (n+1)) ≤ Fin.last n by change 0 ≤ n; omega)
    have h0 : ρ a = 0 := by
      simp only [ρ, γ.property.2.1, hyperboloidPolar_radius (le_refl 0) 0]
    have hR : ρ b = hyperboloidRadius q := by simp only [ρ, γ.property.2.2]
    have hac := hyperboloidRadius_absolutelyContinuous γ.property.1
    have hm := hyperboloid_centered_minimizer_radius_monotone γ hmin
    refine ⟨hab, h0, hR, hac, ?_, ?_⟩
    · intro t ht
      constructor
      · exact (hyperboloidRadius_properties (γ.val t)).1
      · simpa only [ρ, γ.property.2.2] using hm ht (show b ∈ Icc a b from ⟨hab, le_rfl⟩) ht.2
    · have hc : ContinuousOn ρ (Icc a b) := by
        simpa only [uIcc_of_le hab] using hac.continuousOn
      simpa only [h0, hR] using intermediate_value_Icc hab hc
  have finalV02 (x q : Hyperboloid) (hx : 0 < hyperboloidRadius x)
      (hq : 0 < hyperboloidRadius q)
      (hd : hyperboloidSpatial x / (‖hyperboloidSpatial x‖ : ℂ) =
        hyperboloidSpatial q / (‖hyperboloidSpatial q‖ : ℂ)) :
      x = hyperboloidRadialCurve q (hyperboloidRadius x) := by
    have hdx := (hyperboloidPolar_center_direction 0 x).2 hx
    have hdq := (hyperboloidPolar_center_direction 0 q).2 hq
    rw [hdx, hdq] at hd
    have hc : Real.cos (Complex.arg (hyperboloidSpatial x)) =
        Real.cos (Complex.arg (hyperboloidSpatial q)) := by
      simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.re hd
    have hs : Real.sin (Complex.arg (hyperboloidSpatial x)) =
        Real.sin (Complex.arg (hyperboloidSpatial q)) := by
      simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.im hd
    rw [hyperboloidRadialCurve, if_neg (ne_of_gt hq)]
    conv_lhs => rw [← hyperboloidPolar_arg x]
    apply Subtype.ext
    simp only [hyperboloidPolar, hyperboloidPolarCoords, hc, hs]
  have finalV03 (x q : Hyperboloid) (hx : hyperboloidRadius x = 0) :
      x = hyperboloidRadialCurve q (hyperboloidRadius x) := by
    have hxval := (hyperboloidRadius_properties x).2.2.2.1.mp hx
    rw [hx, hyperboloidRadialCurve]
    split_ifs <;> apply Subtype.ext
    · exact hxval.trans (hyperboloidPolar_center_direction 0 q).1.symm
    · exact hxval.trans (hyperboloidPolar_center_direction
        (Complex.arg (hyperboloidSpatial q)) q).1.symm
  have finalV04 {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
      (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      {t : ℝ} (ht : t ∈ Icc a b) (hp : 0 < hyperboloidRadius (γ.val t)) :
      0 < hyperboloidRadius q ∧
        hyperboloidSpatial (γ.val t) / (‖hyperboloidSpatial (γ.val t)‖ : ℂ) =
          hyperboloidSpatial q / (‖hyperboloidSpatial q‖ : ℂ) := by
    have hb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
    have hq : 0 < hyperboloidRadius q := by
      have hle := hyperboloid_centered_minimizer_radius_monotone γ hmin ht hb ht.2
      change hyperboloidRadius (γ.val t) ≤ hyperboloidRadius (γ.val b) at hle
      rw [γ.property.2.2] at hle
      exact hp.trans_le hle
    refine ⟨hq, ?_⟩
    have hqb : 0 < hyperboloidRadius (γ.val b) := by simpa only [γ.property.2.2] using hq
    simpa only [γ.property.2.2] using
      hyperboloid_centered_minimizer_direction γ hmin t ht b hb hp hqb
  have finalV05 {a b : ℝ} {q : Hyperboloid} {γ : ℝ → Hyperboloid}
      (hbound : ∀ t ∈ Icc a b, hyperboloidRadius (γ t) ∈ Icc 0 (hyperboloidRadius q))
      (hsurj : Icc 0 (hyperboloidRadius q) ⊆
        (fun t => hyperboloidRadius (γ t)) '' Icc a b)
      (hpoint : ∀ t ∈ Icc a b, γ t = hyperboloidRadialCurve q (hyperboloidRadius (γ t))) :
      γ '' Icc a b = hyperboloidRadialCurve q '' Icc 0 (hyperboloidRadius q) := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact ⟨hyperboloidRadius (γ t), hbound t ht, (hpoint t ht).symm⟩
    · rintro x ⟨r, hr, rfl⟩
      obtain ⟨t, ht, he⟩ := hsurj hr
      exact ⟨t, ht, (hpoint t ht).trans (congrArg (hyperboloidRadialCurve q) he)⟩
  have hpoint : ∀ t ∈ Icc a b,
      γ.val t = hyperboloidRadialCurve q (hyperboloidRadius (γ.val t)) := by
    intro t ht
    rcases eq_or_lt_of_le (hyperboloidRadius_properties (γ.val t)).1 with hz | hp
    · exact finalV03 (γ.val t) q hz.symm
    · have hd := finalV04 γ hmin ht hp
      exact finalV02 (γ.val t) q hp hd.1 hd.2
  have h := finalV01 γ hmin
  exact ⟨hpoint, finalV05 h.2.2.2.2.1 h.2.2.2.2.2 hpoint⟩

/-- A positive-radius minimizer on its radial interval with unit intrinsic speed equals the radial parametrization. (G03.e) -/
theorem hyperboloid_centered_unitSpeed_unique
    (q : Hyperboloid) (hq : 0 < hyperboloidRadius q)
    {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (γ : PiecewiseC1CurveOn I 0 (hyperboloidRadius q) n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
    (hunit :
      letI : Bundle.RiemannianBundle
          (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      ∀ i : Fin n, ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ),
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val
          (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1) :
  ∀ t ∈ Icc 0 (hyperboloidRadius q), γ.val t = hyperboloidRadialCurve q t := by
  have finalV01 {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ} {q : Hyperboloid}
      (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q) :
      let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
      a ≤ b ∧ ρ a = 0 ∧ ρ b = hyperboloidRadius q ∧
        AbsolutelyContinuousOnInterval ρ a b ∧
        (∀ t ∈ Icc a b, ρ t ∈ Icc 0 (hyperboloidRadius q)) ∧
        Icc 0 (hyperboloidRadius q) ⊆ ρ '' Icc a b := by
    let ρ : ℝ → ℝ := fun t => hyperboloidRadius (γ.val t)
    have hab : a ≤ b := by
      simpa only [γ.property.1.2.1, γ.property.1.2.2.1] using
        γ.property.1.1 (show (0 : Fin (n+1)) ≤ Fin.last n by change 0 ≤ n; omega)
    have h0 : ρ a = 0 := by
      simp only [ρ, γ.property.2.1, hyperboloidPolar_radius (le_refl 0) 0]
    have hR : ρ b = hyperboloidRadius q := by simp only [ρ, γ.property.2.2]
    have hac := hyperboloidRadius_absolutelyContinuous γ.property.1
    have hm := hyperboloid_centered_minimizer_radius_monotone γ hmin
    refine ⟨hab, h0, hR, hac, ?_, ?_⟩
    · intro t ht
      constructor
      · exact (hyperboloidRadius_properties (γ.val t)).1
      · simpa only [ρ, γ.property.2.2] using hm ht (show b ∈ Icc a b from ⟨hab, le_rfl⟩) ht.2
    · have hc : ContinuousOn ρ (Icc a b) := by
        simpa only [uIcc_of_le hab] using hac.continuousOn
      simpa only [h0, hR] using intermediate_value_Icc hab hc
  have finalV06 (q : Hyperboloid) (hq : 0 < hyperboloidRadius q)
      {n : ℕ} {cut : Fin (n+1) → ℝ}
      (γ : PiecewiseC1CurveOn I 0 (hyperboloidRadius q) n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      (hunit : letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
        ∀ i : Fin n, ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ),
          ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1) :
      ∀ i : Fin n, ∀ᵐ t ∂volume.restrict (Ioo (cut i.castSucc) (cut i.succ)),
        deriv (fun s => hyperboloidRadius (γ.val s)) t = 1 := by
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    intro i
    have he := (hyperboloid_centered_minimizer_losses γ hmin).2.2.2 i
    have hs : Ioo (cut i.castSucc) (cut i.succ) ⊆ Ioc (cut i.castSucc) (cut i.succ) :=
      fun t ht => ⟨ht.1, ht.2.le⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he,
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    exact ht.2.symm.trans (ht.1.symm.trans (hunit i t hmem))
  have finalV07 {ρ : ℝ → ℝ} {R t : ℝ} (hR : 0 ≤ R)
      (hac : AbsolutelyContinuousOnInterval ρ 0 R) (h0 : ρ 0 = 0)
      (hderiv : ∀ᵐ s ∂volume.restrict (Icc 0 R), deriv ρ s = 1)
      (ht : t ∈ Icc 0 R) : ρ t = t := by
    have hsub : Icc 0 t ⊆ Icc 0 R := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hus : uIcc 0 t ⊆ uIcc 0 R := by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hR] using hsub
    have hsmall := hac.mono hus
    have hclosed := ae_restrict_of_ae_restrict_of_subset hsub hderiv
    have hopen : ∀ᵐ s ∂volume.restrict (uIoc 0 t), deriv ρ s = 1 := by
      simpa only [uIoc_of_le ht.1, restrict_Ioc_eq_restrict_Icc] using hclosed
    have hi : (∫ s in 0..t, deriv ρ s) = t := by
      calc
        _ = ∫ s in 0..t, (1 : ℝ) := intervalIntegral.integral_congr_ae_restrict hopen
        _ = t := by simp
    rw [hsmall.integral_deriv_eq_sub, h0, sub_zero] at hi
    exact hi
  have finalV06a (q : Hyperboloid) (hq : 0 < hyperboloidRadius q)
      {n : ℕ} {cut : Fin (n+1) → ℝ}
      (γ : PiecewiseC1CurveOn I 0 (hyperboloidRadius q) n cut (hyperboloidPolar 0 0) q)
      (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
      (hunit : letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
        ∀ i : Fin n, ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ),
          ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1) :
      ∀ᵐ t ∂volume.restrict (Icc 0 (hyperboloidRadius q)),
        deriv (fun s => hyperboloidRadius (γ.val s)) t = 1 := by
    have hfirst := γ.property.1.2.1
    have hlast := γ.property.1.2.2.1
    have hcover : ∀ t ∈ Icc (0 : ℝ) (hyperboloidRadius q), t ∉ range cut →
        ∃ i : Fin n, t ∈ Ioo (cut i.castSucc) (cut i.succ) := by
      let cN : ℕ → ℝ := fun k =>
        if hk : k < n + 1 then cut ⟨k, hk⟩ else cut (Fin.last n)
      have hN0 : cN 0 = cut 0 := by simp [cN]
      have hNlast : cN n = cut (Fin.last n) := by simp [cN, Fin.last]
      have hNleft : ∀ i : Fin n, cN i.val = cut i.castSucc := by
        intro i
        simp only [cN, dif_pos (show i.val < n + 1 by omega)]
        rfl
      have hNright : ∀ i : Fin n, cN (i.val + 1) = cut i.succ := by
        intro i
        simp only [cN, dif_pos (show i.val + 1 < n + 1 by omega)]
        rfl
      have hNcover : Ico (cN 0) (cN n) ⊆
          ⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1)) :=
        Ico_subset_biUnion_Ico n cN
      have hindex : (⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1))) =
          ⋃ i : Fin n, Ico (cut i.castSucc) (cut i.succ) := by
        ext t
        constructor
        · intro ht
          rcases mem_iUnion.1 ht with ⟨k, hk⟩
          rcases mem_iUnion.1 hk with ⟨hk, ht⟩
          let i : Fin n := ⟨k, Finset.mem_range.1 hk⟩
          exact mem_iUnion.2 ⟨i, by simpa only [← hNleft i, ← hNright i] using ht⟩
        · intro ht
          rcases mem_iUnion.1 ht with ⟨i, ht⟩
          exact mem_iUnion.2 ⟨i.val, mem_iUnion.2 ⟨Finset.mem_range.2 i.isLt,
            by simpa only [hNleft i, hNright i] using ht⟩⟩
      intro t ht hnot
      have htb : t < (hyperboloidRadius q) := lt_of_le_of_ne ht.2 (by
        intro h
        exact hnot ⟨Fin.last n, hlast.trans h.symm⟩)
      have hmem : t ∈ Ico (cN 0) (cN n) := by
        simpa only [hN0, hNlast, hfirst, hlast] using ⟨ht.1, htb⟩
      have hm := hNcover hmem
      rw [hindex] at hm
      rcases mem_iUnion.1 hm with ⟨i, hi⟩
      exact ⟨i, lt_of_le_of_ne hi.1 (by
        intro heq
        exact hnot ⟨i.castSucc, heq⟩), hi.2⟩

    have hpiece := finalV06 q hq γ hmin hunit
    have hall : ∀ᵐ t ∂volume, ∀ i : Fin n,
        t ∈ Ioo (cut i.castSucc) (cut i.succ) →
          deriv (fun s => hyperboloidRadius (γ.val s)) t = 1 :=
      ae_all_iff.mpr (fun i => (ae_restrict_iff' measurableSet_Ioo).mp (hpiece i))
    have hnot : ∀ᵐ t ∂volume, t ∉ range cut :=
      measure_eq_zero_iff_ae_notMem.mp ((Set.finite_range cut).measure_zero volume)
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hall, hnot] with t ht hn
    intro hmem
    obtain ⟨i, hi⟩ := hcover t hmem hn
    exact ht i hi
  have h := finalV01 γ hmin
  have hderiv := finalV06a q hq γ hmin hunit
  intro t ht
  have hr := finalV07 (hyperboloidRadius_properties q).1 h.2.2.2.1 h.2.1 hderiv ht
  exact ((hyperboloid_centered_minimizer_image γ hmin).1 t ht).trans
    (congrArg (hyperboloidRadialCurve q) hr)

/-- A zero-radius centered minimizer is constant, with no direction or plane choice. (G03.e) -/
theorem hyperboloid_centered_minimizer_zero
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {q : Hyperboloid}
    (γ : PiecewiseC1CurveOn I a b n cut (hyperboloidPolar 0 0) q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidRadius q)
    (hq : hyperboloidRadius q = 0) :
  ∀ t ∈ Icc a b, γ.val t = hyperboloidPolar 0 0 := by
  intro t ht
  have hb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  have hle := hyperboloid_centered_minimizer_radius_monotone γ hmin ht hb ht.2
  change hyperboloidRadius (γ.val t) ≤ hyperboloidRadius (γ.val b) at hle
  rw [γ.property.2.2, hq] at hle
  have hz := le_antisymm hle (hyperboloidRadius_properties (γ.val t)).1
  apply Subtype.ext
  exact ((hyperboloidRadius_properties (γ.val t)).2.2.2.1.mp hz).trans
    (hyperboloidPolar_center_direction 0 q).1.symm


/-! ## Arbitrary-center minimizing segments and length distance -/

/-- The real value of the existing infimum of finite-piece curve lengths. -/
def hyperboloidLengthDist (p q : Hyperboloid) : ℝ :=
  (piecewiseC1EDist hyperboloidMetric p q).toReal

/-- The minimizing segment obtained by inverse-centering the radial curve. -/
def hyperboloidSegment (p q : Hyperboloid) (s : ℝ) : Hyperboloid :=
  uncenterHyperboloid p (hyperboloidRadialCurve (centerHyperboloid p q) s)

/-- The inverse-centered initial spatial direction, with zero at coincident endpoints. -/
def hyperboloidSegmentInitial (p q : Hyperboloid) : Fin 3 → ℝ :=
  if p = q then 0 else
    (lorentzCenterCoordinates p).symm
      ![Real.cos (Complex.arg (hyperboloidSpatial (centerHyperboloid p q))),
        Real.sin (Complex.arg (hyperboloidSpatial (centerHyperboloid p q))), 0]

/-- Centering preserves both arbitrary-family length infima. The common value is finite,
and its real interpretation is the radius of the centered endpoint. -/
theorem hyperboloidLengthDist_center (p q : Hyperboloid) :
  piecewiseC1EDist hyperboloidMetric p q ≤
    piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) (centerHyperboloid p q) ∧
  piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0) (centerHyperboloid p q) ≤
    piecewiseC1EDist hyperboloidMetric p q ∧
  piecewiseC1EDist hyperboloidMetric p q =
    ENNReal.ofReal (hyperboloidRadius (centerHyperboloid p q)) ∧
  piecewiseC1EDist hyperboloidMetric p q < ⊤ ∧
  hyperboloidLengthDist p q = hyperboloidRadius (centerHyperboloid p q) := by
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩

  -- M04a: exact subtype center and inverse identities, before any family cast.
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  have hu : uncenterHyperboloid p (hyperboloidPolar 0 0) = p := by
    rw [← hc]
    exact (centerHyperboloid_properties p).2.2.1 p
  have huc : ∀ x, uncenterHyperboloid p (centerHyperboloid p x) = x :=
    (centerHyperboloid_properties p).2.2.1
  have hcu : ∀ x, centerHyperboloid p (uncenterHyperboloid p x) = x :=
    (centerHyperboloid_properties p).2.2.2.1

  -- M01/M02 forward: every original competitor, unchanged a,b,n,cut.
  -- Rebuild only the endpoint proof, preserving the underlying mapped function.
  have forward : ∀ (a b : ℝ) (n : ℕ) (cut : Fin (n+1) → ℝ)
      (γ : PiecewiseC1CurveOn I a b n cut p q),
      ∃ η : PiecewiseC1CurveOn I a b n cut
          (hyperboloidPolar 0 0) (centerHyperboloid p q),
        piecewiseC1Length hyperboloidMetric η.val cut =
          piecewiseC1Length hyperboloidMetric γ.val cut ∧
        pathELength I η.val a b = pathELength I γ.val a b ∧
        pathELength I γ.val a b < ⊤ ∧ pathELength I η.val a b < ⊤ ∧
        (∀ t, η.val t = centerHyperboloid p (γ.val t)) := by
    intro a b n cut γ
    let Φ := PiecewiseC1CurveOn.mapEquiv (a := a) (b := b) (cut := cut)
      (p := p) (q := q) (centerHyperboloidDiffeomorph p)
    let ζ := Φ γ
    have hz0 : ζ.val a = hyperboloidPolar 0 0 := by
      exact ζ.property.2.1.trans hc
    let η : PiecewiseC1CurveOn I a b n cut
        (hyperboloidPolar 0 0) (centerHyperboloid p q) :=
      ⟨ζ.val, ζ.property.1, hz0, ζ.property.2.2⟩
    have h := centerHyperboloid_curveFamily_length p
      (a := a) (b := b) (n := n) (cut := cut) (x := p) (y := q)
    have hγ := h.2.1 γ
    exact ⟨η, hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2.1,
      fun t => h.2.2.2.1 γ t⟩

  -- M01/M02 inverse: arbitrary centered competitor, not just a known image.
  -- η0 is the SAME function with source endpoint rewritten to e(p).
  have backward : ∀ (a b : ℝ) (n : ℕ) (cut : Fin (n+1) → ℝ)
      (η : PiecewiseC1CurveOn I a b n cut
        (hyperboloidPolar 0 0) (centerHyperboloid p q)),
      ∃ γ : PiecewiseC1CurveOn I a b n cut p q,
        piecewiseC1Length hyperboloidMetric γ.val cut =
          piecewiseC1Length hyperboloidMetric η.val cut ∧
        pathELength I γ.val a b = pathELength I η.val a b ∧
        pathELength I η.val a b < ⊤ ∧ pathELength I γ.val a b < ⊤ ∧
        (∀ t, γ.val t = uncenterHyperboloid p (η.val t)) := by
    intro a b n cut η
    let Φ := PiecewiseC1CurveOn.mapEquiv (a := a) (b := b) (cut := cut)
      (p := p) (q := q) (centerHyperboloidDiffeomorph p)
    let η0 : PiecewiseC1CurveOn I a b n cut
        (centerHyperboloid p p) (centerHyperboloid p q) :=
      ⟨η.val, η.property.1, η.property.2.1.trans hc.symm, η.property.2.2⟩
    let γ := Φ.symm η0
    have h := centerHyperboloid_curveFamily_length p
      (a := a) (b := b) (n := n) (cut := cut) (x := p) (y := q)
    have hη := h.2.2.1 η0
    exact ⟨γ, hη.1, hη.2.1, hη.2.2.1, hη.2.2.2.1,
      fun t => h.2.2.2.2.1 η0 t⟩

  -- M03a: original infimum ≤ centered infimum, via arbitrary inverse image.
  have hle : piecewiseC1EDist hyperboloidMetric p q ≤
      piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0)
        (centerHyperboloid p q) := by
    unfold piecewiseC1EDist
    refine le_iInf (fun a => le_iInf (fun b => le_iInf (fun n =>
      le_iInf (fun cut => le_iInf (fun η => ?_)))))
    obtain ⟨γ, hlen, hpath, hfinη, hfinγ, hval⟩ := backward a b n cut η
    exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le n
      (iInf_le_of_le cut (iInf_le_of_le γ (by rw [hlen])))))

  -- M03b: centered infimum ≤ original infimum, via arbitrary forward image.
  have hge : piecewiseC1EDist hyperboloidMetric (hyperboloidPolar 0 0)
        (centerHyperboloid p q) ≤ piecewiseC1EDist hyperboloidMetric p q := by
    unfold piecewiseC1EDist
    refine le_iInf (fun a => le_iInf (fun b => le_iInf (fun n =>
      le_iInf (fun cut => le_iInf (fun γ => ?_)))))
    obtain ⟨η, hlen, hpath, hfinγ, hfinη, hval⟩ := forward a b n cut γ
    exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le n
      (iInf_le_of_le cut (iInf_le_of_le η (by rw [hlen])))))

  -- M03c: invoke the actual centered distance only after both infimum comparisons.
  have hcentered := hyperboloid_centered_piecewiseC1EDist (centerHyperboloid p q)
  have hext : piecewiseC1EDist hyperboloidMetric p q =
      ENNReal.ofReal (hyperboloidRadius (centerHyperboloid p q)) :=
    (le_antisymm hle hge).trans hcentered.2.2.1
  have hfinite : piecewiseC1EDist hyperboloidMetric p q < ⊤ := by
    rw [hext]
    exact ENNReal.ofReal_lt_top
  have hreal : hyperboloidLengthDist p q =
      hyperboloidRadius (centerHyperboloid p q) := by
    rw [hyperboloidLengthDist, hext,
      ENNReal.toReal_ofReal (hyperboloidRadius_properties (centerHyperboloid p q)).1]
  exact ⟨hle, hge, hext, hfinite, hreal⟩

/-- The actual length distance is nonnegative and vanishes exactly on the diagonal. -/
theorem hyperboloidLengthDist_nonneg_eq_zero (p q : Hyperboloid) :
  0 ≤ hyperboloidLengthDist p q ∧
  (hyperboloidLengthDist p q = 0 ↔ p = q) ∧
  (0 < hyperboloidLengthDist p q ↔ p ≠ q) := by
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  have hreal := (hyperboloidLengthDist_center p q).2.2.2.2
  have hrzero : hyperboloidRadius (centerHyperboloid p q) = 0 ↔ p = q := by
    constructor
    · intro hz
      have hv := (hyperboloidRadius_properties (centerHyperboloid p q)).2.2.2.1.mp hz
      have heq : centerHyperboloid p q = hyperboloidPolar 0 0 := by
        apply Subtype.ext
        exact hv.trans (hyperboloidPolar_center_direction 0 p).1.symm
      have hqp : q = p := (centerHyperboloidEquiv p).injective (heq.trans hc.symm)
      exact hqp.symm
    · intro hpq
      subst q
      apply (hyperboloidRadius_properties (centerHyperboloid p p)).2.2.2.1.mpr
      exact (centerHyperboloid_properties p).2.2.2.2.1
  have hnonneg : 0 ≤ hyperboloidLengthDist p q := by
    rw [hreal]
    exact (hyperboloidRadius_properties (centerHyperboloid p q)).1
  have hzero : hyperboloidLengthDist p q = 0 ↔ p = q := by
    rw [hreal]
    exact hrzero
  have hpositive : 0 < hyperboloidLengthDist p q ↔ p ≠ q := by
    constructor
    · intro hd hpq
      exact (ne_of_gt hd) (hzero.mpr hpq)
    · intro hpq
      exact lt_of_le_of_ne hnonneg (Ne.symm (fun hz => hpq (hzero.mp hz)))
  exact ⟨hnonneg, hzero, hpositive⟩

/-- The inverse-centered radial curve is smooth, has the exact endpoints, and has
unit speed for distinct endpoints with respect to the same Lorentz tangent metric. -/
theorem hyperboloidSegment_properties (p q : Hyperboloid) :
  ContMDiff 𝓘(ℝ, ℝ) I ∞ (hyperboloidSegment p q) ∧
  hyperboloidSegment p q 0 = p ∧
  hyperboloidSegment p q (hyperboloidLengthDist p q) = q ∧
  (p = q → ∀ s, hyperboloidSegment p q s = p) ∧
  (p ≠ q →
    letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ∀ s, ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidSegment p q) s (1 : ℝ)‖ = 1) := by
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  have hu : uncenterHyperboloid p (hyperboloidPolar 0 0) = p := by
    rw [← hc]
    exact (centerHyperboloid_properties p).2.2.1 p
  have hd := (hyperboloidLengthDist_center p q).2.2.2.2
  have hr := hyperboloidRadialCurve_properties (centerHyperboloid p q)
  refine ⟨(contMDiff_uncenterHyperboloid p).comp hr.1, ?_, ?_, ?_, ?_⟩
  · change uncenterHyperboloid p (hyperboloidRadialCurve (centerHyperboloid p q) 0) = p
    rw [hr.2.1, hu]
  · change uncenterHyperboloid p
      (hyperboloidRadialCurve (centerHyperboloid p q) (hyperboloidLengthDist p q)) = q
    rw [hd, hr.2.2.1]
    exact (centerHyperboloid_properties p).2.2.1 q
  · intro hpq s
    have hz : hyperboloidRadius (centerHyperboloid p q) = 0 :=
      hd.symm.trans ((hyperboloidLengthDist_nonneg_eq_zero p q).2.1.mpr hpq)
    change uncenterHyperboloid p (hyperboloidRadialCurve (centerHyperboloid p q) s) = p
    rw [hr.2.2.2.1 hz s, hu]
  · intro hpq
    letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    have hpos : 0 < hyperboloidRadius (centerHyperboloid p q) := by
      rw [← hd]
      exact (hyperboloidLengthDist_nonneg_eq_zero p q).2.2.mpr hpq
    intro s
    exact ((uncenterHyperboloid_speed p (hyperboloidRadialCurve (centerHyperboloid p q)) s
      (hr.1.mdifferentiable (by simp) s)).1).trans (hr.2.2.2.2 hpos s)

/-- The segment has its actual weak two-cut witness and realizes both real and
extended length distance, including the constant coincident case. -/
theorem hyperboloidSegment_length (p q : Hyperboloid) :
  let d := hyperboloidLengthDist p q
  let cut : Fin 2 → ℝ := fun i => if i = 0 then 0 else d
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  IsPiecewiseC1On I (hyperboloidSegment p q) 0 d 1 cut ∧
  piecewiseC1Length hyperboloidMetric (hyperboloidSegment p q) cut = d ∧
  pathELength I (hyperboloidSegment p q) 0 d =
    piecewiseC1EDist hyperboloidMetric p q ∧
  pathELength I (hyperboloidSegment p q) 0 d < ⊤ := by
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  dsimp only
  rw [(hyperboloidLengthDist_center p q).2.2.2.2]
  have h := hyperboloidRadialCurve_length (centerHyperboloid p q)
  have hu := uncenterHyperboloid_length p h.1
  refine ⟨hu.1, hu.2.2.2.2.1.trans h.2.1, ?_, ?_⟩
  · exact (hu.2.2.2.2.2.2.2.1.trans h.2.2.1).trans
      (hyperboloidLengthDist_center p q).2.2.1.symm
  · exact hu.2.2.2.2.2.2.2.2.2.1

/-- Every minimizing curve has monotone centered radius and exactly the constructed
segment image. General parametrizations may pause; a coincident minimizer is constant. -/
theorem hyperboloid_minimizer_image
    {p q : Hyperboloid} {a b : ℝ} {n : ℕ} {cut : Fin (n+1) → ℝ}
    (γ : PiecewiseC1CurveOn I a b n cut p q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidLengthDist p q) :
  MonotoneOn (fun t => hyperboloidRadius (centerHyperboloid p (γ.val t))) (Icc a b) ∧
  (∀ t ∈ Icc a b, γ.val t = hyperboloidSegment p q
    (hyperboloidRadius (centerHyperboloid p (γ.val t)))) ∧
  γ.val '' Icc a b = hyperboloidSegment p q '' Icc 0 (hyperboloidLengthDist p q) ∧
  (p = q → ∀ t ∈ Icc a b, γ.val t = p) := by
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  have ht := centerHyperboloid_length p γ.property.1
  let η : PiecewiseC1CurveOn I a b n cut
      (hyperboloidPolar 0 0) (centerHyperboloid p q) :=
    ⟨(centerHyperboloid p) ∘ γ.val, ht.1,
      (congrArg (centerHyperboloid p) γ.property.2.1).trans hc,
      congrArg (centerHyperboloid p) γ.property.2.2⟩
  have hd := (hyperboloidLengthDist_center p q).2.2.2.2
  have hm : piecewiseC1Length hyperboloidMetric η.val cut =
      hyperboloidRadius (centerHyperboloid p q) := ht.2.2.2.2.1.trans (hmin.trans hd)
  have hmono := hyperboloid_centered_minimizer_radius_monotone η hm
  have hi := hyperboloid_centered_minimizer_image η hm
  have hinv : ∀ t, uncenterHyperboloid p (η.val t) = γ.val t :=
    fun t => (centerHyperboloid_properties p).2.2.1 (γ.val t)
  have hpoint : ∀ t ∈ Icc a b, γ.val t = hyperboloidSegment p q
      (hyperboloidRadius (centerHyperboloid p (γ.val t))) := by
    intro t hmem
    exact (hinv t).symm.trans (congrArg (uncenterHyperboloid p) (hi.1 t hmem))
  refine ⟨hmono, hpoint, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro z ⟨t, hmem, rfl⟩
      have hmemb : η.val t ∈ hyperboloidRadialCurve (centerHyperboloid p q) ''
          Icc 0 (hyperboloidRadius (centerHyperboloid p q)) :=
        hi.2 ▸ ⟨t, hmem, rfl⟩
      obtain ⟨s, hs, hst⟩ := hmemb
      refine ⟨s, by simpa only [hd] using hs, ?_⟩
      exact (congrArg (uncenterHyperboloid p) hst).trans (hinv t)
    · rintro z ⟨s, hs, rfl⟩
      have hmemb : hyperboloidRadialCurve (centerHyperboloid p q) s ∈ η.val '' Icc a b := by
        rw [hi.2]
        exact ⟨s, by simpa only [hd] using hs, rfl⟩
      obtain ⟨t, htmem, hts⟩ := hmemb
      exact ⟨t, htmem, (hinv t).symm.trans (congrArg (uncenterHyperboloid p) hts)⟩
  · intro hpq t hmem
    have hz : hyperboloidRadius (centerHyperboloid p q) = 0 :=
      hd.symm.trans ((hyperboloidLengthDist_nonneg_eq_zero p q).2.1.mpr hpq)
    have he := hyperboloid_centered_minimizer_zero η hm hz t hmem
    have hu : uncenterHyperboloid p (hyperboloidPolar 0 0) = p := by
      rw [← hc]
      exact (centerHyperboloid_properties p).2.2.1 p
    exact (hinv t).symm.trans ((congrArg (uncenterHyperboloid p) he).trans hu)

/-- A minimizing curve on the original distance interval with unit speed on its
strict pieces equals the constructed arclength segment for distinct endpoints. -/
theorem hyperboloid_unitSpeed_minimizer_unique
    (p q : Hyperboloid) (hpq : p ≠ q) {n : ℕ} {cut : Fin (n+1) → ℝ}
    (γ : PiecewiseC1CurveOn I 0 (hyperboloidLengthDist p q) n cut p q)
    (hmin : piecewiseC1Length hyperboloidMetric γ.val cut = hyperboloidLengthDist p q)
    (hunit : letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
      ∀ i : Fin n, ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ),
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1) :
  ∀ t ∈ Icc 0 (hyperboloidLengthDist p q), γ.val t = hyperboloidSegment p q t := by
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  have hd := (hyperboloidLengthDist_center p q).2.2.2.2
  have hpos : 0 < hyperboloidRadius (centerHyperboloid p q) := by
    rw [← hd]
    exact (hyperboloidLengthDist_nonneg_eq_zero p q).2.2.mpr hpq
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  let η : PiecewiseC1CurveOn I 0 (hyperboloidLengthDist p q) n cut
      (hyperboloidPolar 0 0) (centerHyperboloid p q) :=
    ⟨(centerHyperboloid p) ∘ γ.val, (centerHyperboloid_length p γ.property.1).1,
      (congrArg (centerHyperboloid p) γ.property.2.1).trans hc,
      congrArg (centerHyperboloid p) γ.property.2.2⟩
  have hm : piecewiseC1Length hyperboloidMetric η.val cut = hyperboloidRadius (centerHyperboloid p q) :=
    (centerHyperboloid_length p γ.property.1).2.2.2.2.1.trans (hmin.trans hd)
  have hηunit : ∀ i : Fin n, ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I η.val (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1 := by
    intro i t ht
    have hC1 := γ.property.1.2.2.2.2 i (lt_trans ht.1 ht.2)
    have hdiff := (hC1.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    change ‖mfderivWithin 𝓘(ℝ, ℝ) I ((centerHyperboloid p) ∘ γ.val)
      (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖ = 1
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    have hu := hunit i t ht
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at hu
    exact (centerHyperboloid_speed p γ.val t hdiff).1.trans hu
  have hcUnique : ∀ t ∈ Icc 0 (hyperboloidLengthDist p q),
      η.val t = hyperboloidRadialCurve (centerHyperboloid p q) t := by
    let ηR : PiecewiseC1CurveOn I 0 (hyperboloidRadius (centerHyperboloid p q)) n cut
        (hyperboloidPolar 0 0) (centerHyperboloid p q) :=
      ⟨η.val, by simpa only [hd] using η.property⟩
    have h := hyperboloid_centered_unitSpeed_unique (centerHyperboloid p q)
      hpos ηR hm hηunit
    intro t ht
    exact h t (by simpa only [hd] using ht)
  intro t ht
  exact ((centerHyperboloid_properties p).2.2.1 (γ.val t)).symm.trans
    (congrArg (uncenterHyperboloid p) (hcUnique t ht))

/-- The inverse-centered initial vector is a unit perpendicular tangent and the
actual ambient derivative at zero; it gives the cosh/sinh formula for every real parameter. -/
theorem hyperboloidSegment_initial_formula (p q : Hyperboloid) (hpq : p ≠ q) :
  lorentzBilinear (hyperboloidSegmentInitial p q) p.val = 0 ∧
  lorentzBilinear (hyperboloidSegmentInitial p q) (hyperboloidSegmentInitial p q) = 1 ∧
  HasDerivAt (fun s => (hyperboloidSegment p q s).val)
    (hyperboloidSegmentInitial p q) 0 ∧
  (∀ s : ℝ, (hyperboloidSegment p q s).val =
    Real.cosh s • p.val + Real.sinh s • hyperboloidSegmentInitial p q) := by
  let θ := Complex.arg (hyperboloidSpatial (centerHyperboloid p q))
  let w : Fin 3 → ℝ := ![Real.cos θ, Real.sin θ, 0]
  have hv : hyperboloidSegmentInitial p q = (lorentzCenterCoordinates p).symm w := by
    simp only [hyperboloidSegmentInitial, if_neg hpq, w, θ]
  have hpos : 0 < hyperboloidRadius (centerHyperboloid p q) := by
    rw [← (hyperboloidLengthDist_center p q).2.2.2.2]
    exact (hyperboloidLengthDist_nonneg_eq_zero p q).2.2.mpr hpq
  have hformula : ∀ s, (hyperboloidSegment p q s).val =
      Real.cosh s • p.val + Real.sinh s • hyperboloidSegmentInitial p q := by
    intro s
    have hpolar : hyperboloidPolarCoords s θ =
        Real.cosh s • ![0,0,1] + Real.sinh s • w := by
      funext i
      fin_cases i <;> simp [hyperboloidPolarCoords, w, mul_comm]
    change (lorentzCenterCoordinates p).symm
      (hyperboloidRadialCurve (centerHyperboloid p q) s).val = _
    rw [hyperboloidRadialCurve, if_neg (ne_of_gt hpos)]
    change (lorentzCenterCoordinates p).symm (hyperboloidPolarCoords s θ) = _
    rw [hpolar, map_add, map_smul, map_smul,
      (lorentzCenterCoordinates_properties p).2.2.2.2.1, ← hv]
  have hperp : lorentzBilinear (hyperboloidSegmentInitial p q) p.val = 0 := by
    rw [hv, ← (lorentzCenterCoordinates_properties p).2.2.2.2.1,
      lorentzCenterCoordinates_symm_preserves]
    simp [w, lorentzBilinear_apply]
  have hnorm : lorentzBilinear (hyperboloidSegmentInitial p q)
      (hyperboloidSegmentInitial p q) = 1 := by
    rw [hv, lorentzCenterCoordinates_symm_preserves]
    simpa [w, lorentzBilinear_apply, pow_two] using Real.cos_sq_add_sin_sq θ
  have hder : HasDerivAt (fun s => Real.cosh s • p.val +
      Real.sinh s • hyperboloidSegmentInitial p q) (hyperboloidSegmentInitial p q) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert! ((Real.hasDerivAt_cosh 0).mul_const (p.val i)).add
      ((Real.hasDerivAt_sinh 0).mul_const (hyperboloidSegmentInitial p q i)) using 1 <;>
      simp
  refine ⟨hperp, hnorm, ?_, hformula⟩
  rw [funext hformula]
  exact hder

/-- The Lorentz pairing gives the cosh of the actual length distance, for all pairs,
with equality and strictness detecting coincident and distinct endpoints. -/
theorem hyperboloidLengthDist_cosh (p q : Hyperboloid) :
  Real.cosh (hyperboloidLengthDist p q) = -lorentzBilinear p.val q.val ∧
  1 ≤ -lorentzBilinear p.val q.val ∧
  (-lorentzBilinear p.val q.val = 1 ↔ p = q) ∧
  (1 < -lorentzBilinear p.val q.val ↔ p ≠ q) := by
  have he : Real.cosh (hyperboloidLengthDist p q) = -lorentzBilinear p.val q.val := by
    rw [(hyperboloidLengthDist_center p q).2.2.2.2,
      (hyperboloidRadius_properties (centerHyperboloid p q)).2.2.1]
    exact lorentzCenterCoordinates_time p q.val
  have hzero := (hyperboloidLengthDist_nonneg_eq_zero p q).2.1
  have hstrict : 1 < -lorentzBilinear p.val q.val ↔ p ≠ q := by
    rw [← he, Real.one_lt_cosh]
    exact not_congr hzero
  have hle : 1 ≤ -lorentzBilinear p.val q.val := he ▸ Real.one_le_cosh _
  refine ⟨he, hle, ?_, hstrict⟩
  constructor
  · intro h
    by_contra hpq
    have hs := hstrict.mpr hpq
    rw [h] at hs
    exact (lt_irrefl 1) hs
  · intro hpq
    rw [← he, hzero.mpr hpq, Real.cosh_zero]

/-- For distinct endpoints, positive sinh permits recovery of the already constructed
initial tangent from the endpoint equation, and that vector is unique. -/
theorem hyperboloidSegmentInitial_endpoint (p q : Hyperboloid) (hpq : p ≠ q) :
  0 < Real.sinh (hyperboloidLengthDist p q) ∧
  hyperboloidSegmentInitial p q =
    (Real.sinh (hyperboloidLengthDist p q))⁻¹ •
      (q.val - Real.cosh (hyperboloidLengthDist p q) • p.val) ∧
  (∀ v : Fin 3 → ℝ,
    q.val = Real.cosh (hyperboloidLengthDist p q) • p.val +
      Real.sinh (hyperboloidLengthDist p q) • v →
    v = hyperboloidSegmentInitial p q) := by
  have hs := Real.sinh_pos_iff.mpr ((hyperboloidLengthDist_nonneg_eq_zero p q).2.2.mpr hpq)
  have he : q.val = Real.cosh (hyperboloidLengthDist p q) • p.val +
      Real.sinh (hyperboloidLengthDist p q) • hyperboloidSegmentInitial p q := by
    exact (congrArg Subtype.val (hyperboloidSegment_properties p q).2.2.1).symm.trans
      ((hyperboloidSegment_initial_formula p q hpq).2.2.2 (hyperboloidLengthDist p q))
  have cancel : ∀ v : Fin 3 → ℝ,
      q.val = Real.cosh (hyperboloidLengthDist p q) • p.val +
        Real.sinh (hyperboloidLengthDist p q) • v →
      v = (Real.sinh (hyperboloidLengthDist p q))⁻¹ •
        (q.val - Real.cosh (hyperboloidLengthDist p q) • p.val) := by
    intro v hv
    rw [hv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
  have hv := cancel (hyperboloidSegmentInitial p q) he
  exact ⟨hs, hv, fun v h => (cancel v h).trans hv.symm⟩

/-- The length-infimum distance is recovered from its Lorentz cosh identity by the nonnegative inverse arcosh. -/
theorem hyperboloidLengthDist_arcosh (p q : Hyperboloid) :
  hyperboloidLengthDist p q = Real.arcosh (-lorentzBilinear p.val q.val) := by
  rw [← (hyperboloidLengthDist_cosh p q).1]
  exact (Real.arcosh_cosh (hyperboloidLengthDist_nonneg_eq_zero p q).1).symm

/-- Symmetry of the Lorentz pairing gives symmetry of the actual length distance. -/
theorem hyperboloidLengthDist_symm (p q : Hyperboloid) :
  hyperboloidLengthDist p q = hyperboloidLengthDist q p := by
  rw [hyperboloidLengthDist_arcosh, hyperboloidLengthDist_arcosh, lorentzBilinear_symm]

/-- The length distance is jointly continuous in the inherited hyperboloid topology, including coincident endpoints. -/
theorem continuous_hyperboloidLengthDist :
  Continuous (fun z : Hyperboloid × Hyperboloid => hyperboloidLengthDist z.1 z.2) := by
  have hpoly : Continuous (fun z : Hyperboloid × Hyperboloid =>
      -lorentzBilinear z.1.val z.2.val) := by
    simp only [lorentzBilinear_apply]
    have hp : Continuous (fun z : Hyperboloid × Hyperboloid => z.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hq : Continuous (fun z : Hyperboloid × Hyperboloid => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact ((((continuous_apply 0).comp hp).mul ((continuous_apply 0).comp hq)).add
      (((continuous_apply 1).comp hp).mul ((continuous_apply 1).comp hq))).sub
      (((continuous_apply 2).comp hp).mul ((continuous_apply 2).comp hq)) |>.neg
  have h := Real.continuousOn_arcosh.comp_continuous hpoly
    (fun z => (hyperboloidLengthDist_cosh z.1 z.2).2.1)
  simpa only [Function.comp_def, ← hyperboloidLengthDist_arcosh] using h

/-- For distinct endpoints, the same arclength segment has the symmetric hyperbolic-sine endpoint formula. -/
theorem hyperboloidSegment_endpoint (p q : Hyperboloid) (hpq : p ≠ q)
    (s : ℝ) (hs : s ∈ Set.Icc 0 (hyperboloidLengthDist p q)) :
  (hyperboloidSegment p q s).val =
    (Real.sinh (hyperboloidLengthDist p q - s) /
      Real.sinh (hyperboloidLengthDist p q)) • p.val +
    (Real.sinh s / Real.sinh (hyperboloidLengthDist p q)) • q.val := by
  have h := hyperboloidSegmentInitial_endpoint p q hpq
  rw [(hyperboloidSegment_initial_formula p q hpq).2.2.2 s, h.2.1]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.sinh_sub]
  field_simp [ne_of_gt h.1]
  <;> ring

/-- Reversing the endpoints reverses arclength along the same segment; coincident endpoints give a constant segment. -/
theorem hyperboloidSegment_reverse (p q : Hyperboloid)
    (s : ℝ) (hs : s ∈ Set.Icc 0 (hyperboloidLengthDist p q)) :
  hyperboloidSegment q p (hyperboloidLengthDist p q - s) =
    hyperboloidSegment p q s := by
  by_cases hpq : p = q
  · subst q
    rw [(hyperboloidSegment_properties p p).2.2.2.1 rfl,
      (hyperboloidSegment_properties p p).2.2.2.1 rfl]
  · have hrev : hyperboloidLengthDist p q - s ∈ Icc 0 (hyperboloidLengthDist q p) := by
      rw [← hyperboloidLengthDist_symm p q]
      constructor <;> linarith [hs.1, hs.2]
    apply Subtype.ext
    rw [hyperboloidSegment_endpoint q p (Ne.symm hpq) _ hrev,
      hyperboloidSegment_endpoint p q hpq s hs, ← hyperboloidLengthDist_symm p q]
    have hsub : hyperboloidLengthDist p q - (hyperboloidLengthDist p q - s) = s := by ring
    rw [hsub, add_comm]

/-- The normalized segment traverses the existing arclength segment on the fixed unit parameter interval. -/
def hyperboloidNormalizedSegment (p q : Hyperboloid) (t : ℝ) : Hyperboloid :=
  hyperboloidSegment p q (t * hyperboloidLengthDist p q)

/-- The normalized segment has its prescribed endpoints, reverses naturally, and admits removable coefficients on the diagonal. -/
theorem hyperboloidNormalizedSegment_properties (p q : Hyperboloid) :
  hyperboloidNormalizedSegment p q 0 = p ∧
  hyperboloidNormalizedSegment p q 1 = q ∧
  (p = q → ∀ t : ℝ, hyperboloidNormalizedSegment p q t = p) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1,
    hyperboloidNormalizedSegment q p (1-t) = hyperboloidNormalizedSegment p q t) ∧
  (let S : ℝ → ℝ := dslope Real.sinh 0
   let W : ℝ → ℝ → ℝ := fun a t => t * S (t*a) / S a
   ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (hyperboloidNormalizedSegment p q t).val =
      W (hyperboloidLengthDist p q) (1-t) • p.val +
      W (hyperboloidLengthDist p q) t • q.val) := by
  let S : ℝ → ℝ := dslope Real.sinh 0
  let W : ℝ → ℝ → ℝ := fun a t => t * S (t*a) / S a
  have h0 : S 0 = 1 := by simp [S, dslope_same, Real.deriv_sinh]
  have hmul : ∀ a, a * S a = Real.sinh a := by
    intro a
    simpa only [sub_zero, smul_eq_mul, Real.sinh_zero] using sub_smul_dslope Real.sinh 0 a
  have hn : ∀ a, S a ≠ 0 := by
    intro a ha
    by_cases hz : a = 0
    · subst a
      rw [h0] at ha
      exact one_ne_zero ha
    · have h := hmul a
      rw [ha, mul_zero] at h
      exact (Real.sinh_ne_zero.mpr hz) h.symm
  have hquot : ∀ a t, a ≠ 0 → W a t = Real.sinh (t*a) / Real.sinh a := by
    intro a t ha
    rw [← hmul (t*a), ← hmul a]
    dsimp only [W]
    field_simp [ha, hn a] <;> ring
  have hw0 : ∀ t, W 0 t = t := by
    intro t
    simp [W, h0]
  have hparam : ∀ t ∈ Icc (0 : ℝ) 1,
      t * hyperboloidLengthDist p q ∈ Icc 0 (hyperboloidLengthDist p q) := by
    intro t ht
    have hd := (hyperboloidLengthDist_nonneg_eq_zero p q).1
    constructor
    · exact mul_nonneg ht.1 hd
    · nlinarith [ht.2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hyperboloidNormalizedSegment] using (hyperboloidSegment_properties p q).2.1
  · simpa [hyperboloidNormalizedSegment] using (hyperboloidSegment_properties p q).2.2.1
  · intro hpq t
    exact (hyperboloidSegment_properties p q).2.2.2.1 hpq _
  · intro t ht
    have h := hyperboloidSegment_reverse p q (t * hyperboloidLengthDist p q) (hparam t ht)
    simpa only [hyperboloidNormalizedSegment, ← hyperboloidLengthDist_symm p q,
      sub_mul, one_mul] using h
  · change ∀ t ∈ Icc (0 : ℝ) 1,
      (hyperboloidNormalizedSegment p q t).val =
        W (hyperboloidLengthDist p q) (1-t) • p.val +
        W (hyperboloidLengthDist p q) t • q.val
    intro t ht
    by_cases hpq : p = q
    · subst q
      have hd : hyperboloidLengthDist p p = 0 :=
        (hyperboloidLengthDist_nonneg_eq_zero p p).2.1.mpr rfl
      have hconst : hyperboloidNormalizedSegment p p t = p :=
        (hyperboloidSegment_properties p p).2.2.2.1 rfl _
      rw [hconst, hd, hw0, hw0, ← add_smul]
      have hcoeff : (1-t)+t = 1 := by ring
      rw [hcoeff, one_smul]
    · have hd : hyperboloidLengthDist p q ≠ 0 :=
        ne_of_gt ((hyperboloidLengthDist_nonneg_eq_zero p q).2.2.mpr hpq)
      rw [hquot _ (1-t) hd, hquot _ t hd]
      have hleft : (1-t) * hyperboloidLengthDist p q =
          hyperboloidLengthDist p q - t * hyperboloidLengthDist p q := by ring
      rw [hleft]
      exact hyperboloidSegment_endpoint p q hpq _ (hparam t ht)

/-- The normalized segment depends jointly continuously on both endpoints and the closed unit parameter, including coincidence. -/
theorem continuous_hyperboloidNormalizedSegment :
  Continuous (fun z : (Hyperboloid × Hyperboloid) × Set.Icc (0 : ℝ) 1 =>
    hyperboloidNormalizedSegment z.1.1 z.1.2 z.2.val) := by
  let S : ℝ → ℝ := dslope Real.sinh 0
  let W : ℝ → ℝ → ℝ := fun a t => t * S (t*a) / S a
  have h0 : S 0 = 1 := by simp [S, dslope_same, Real.deriv_sinh]
  have hmul : ∀ a, a * S a = Real.sinh a := by
    intro a
    simpa only [sub_zero, smul_eq_mul, Real.sinh_zero] using sub_smul_dslope Real.sinh 0 a
  have hn : ∀ a, S a ≠ 0 := by
    intro a ha
    by_cases hz : a = 0
    · subst a
      rw [h0] at ha
      exact one_ne_zero ha
    · have h := hmul a
      rw [ha, mul_zero] at h
      exact (Real.sinh_ne_zero.mpr hz) h.symm
  have hc : Continuous S := by
    rw [continuous_iff_continuousAt]
    intro a
    by_cases hz : a = 0
    · subst a
      exact continuousAt_dslope_same.mpr (Real.hasDerivAt_sinh 0).differentiableAt
    · exact (continuousAt_dslope_of_ne hz).mpr Real.continuous_sinh.continuousAt
  have hw : Continuous (fun z : ℝ × ℝ => W z.1 z.2) :=
    (continuous_snd.mul (hc.comp (continuous_snd.mul continuous_fst))).div
      (hc.comp continuous_fst) (fun z => hn z.1)

  let Z := (Hyperboloid × Hyperboloid) × Icc (0 : ℝ) 1
  have hd : Continuous (fun z : Z => hyperboloidLengthDist z.1.1 z.1.2) :=
    continuous_hyperboloidLengthDist.comp continuous_fst
  have ht : Continuous (fun z : Z => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous (fun z : Z => z.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hq : Continuous (fun z : Z => z.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hleft : Continuous (fun z : Z => W (hyperboloidLengthDist z.1.1 z.1.2) (1-z.2.val)) :=
    hw.comp (hd.prodMk (continuous_const.sub ht))
  have hright : Continuous (fun z : Z => W (hyperboloidLengthDist z.1.1 z.1.2) z.2.val) :=
    hw.comp (hd.prodMk ht)
  have hambient : Continuous (fun z : Z =>
      W (hyperboloidLengthDist z.1.1 z.1.2) (1-z.2.val) • z.1.1.val +
      W (hyperboloidLengthDist z.1.1 z.1.2) z.2.val • z.1.2.val) :=
    (hleft.smul hp).add (hright.smul hq)
  have heq : (fun z : Z => (hyperboloidNormalizedSegment z.1.1 z.1.2 z.2.val).val) =
      (fun z : Z => W (hyperboloidLengthDist z.1.1 z.1.2) (1-z.2.val) • z.1.1.val +
        W (hyperboloidLengthDist z.1.1 z.1.2) z.2.val • z.1.2.val) := by
    funext z
    exact (hyperboloidNormalizedSegment_properties z.1.1 z.1.2).2.2.2.2 z.2.val z.2.property
  have hval : Continuous (fun z : Z => (hyperboloidNormalizedSegment z.1.1 z.1.2 z.2.val).val) := by
    rw [heq]
    exact hambient
  -- This uses the ORIGINAL point's known membership, not a new vector premise.
  exact hval.subtype_mk (fun z => (hyperboloidNormalizedSegment z.1.1 z.1.2 z.2.val).property)

end PolarRadial

/-- The ambient hyperbolic parametrization determined by a point and a tangent direction. -/
def hyperboloidGeodesicCoords (p : Hyperboloid) (v : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  Real.cosh s • p.val + Real.sinh s • v

/-- The hyperbolic parametrization has Lorentz square minus one and lies on the upper sheet. -/
theorem hyperboloidGeodesicCoords_mem (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1) (s : ℝ) :
  (hyperboloidGeodesicCoords p v s 0)^2 +
    (hyperboloidGeodesicCoords p v s 1)^2 -
    (hyperboloidGeodesicCoords p v s 2)^2 = -1 ∧
  0 < hyperboloidGeodesicCoords p v s 2 := by
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hPair : ∀ a b c d : ℝ,
      lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) = -a*c+b*d := by
    intro a b c d
    have he : lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) =
        a*c*lorentzBilinear p.val p.val +
        (a*d+b*c)*lorentzBilinear v p.val + b*d*lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp, hvp, hvv]
    ring
  have hQ : lorentzBilinear (hyperboloidGeodesicCoords p v s)
      (hyperboloidGeodesicCoords p v s) = -1 := by
    unfold hyperboloidGeodesicCoords
    rw [hPair]
    nlinarith [Real.cosh_sq_sub_sinh_sq s]
  have htimePair : -lorentzBilinear p.val (hyperboloidGeodesicCoords p v s) = Real.cosh s := by
    have he := hPair 1 0 (Real.cosh s) (Real.sinh s)
    simp only [one_smul, zero_smul, add_zero, neg_mul, one_mul, zero_mul, add_zero] at he
    change -lorentzBilinear p.val (Real.cosh s • p.val+Real.sinh s • v) = Real.cosh s
    linarith
  refine ⟨?_, (lorentzUnit_time_sign p _ hQ).2.2.mpr ?_⟩
  · simpa only [lorentzBilinear_apply, pow_two] using hQ
  · rw [htimePair]
    exact Real.cosh_pos s

/-- The all-real hyperboloid curve determined by a unit Lorentz tangent. -/
def hyperboloidGeodesic (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1)
    (s : ℝ) : Hyperboloid :=
  ⟨hyperboloidGeodesicCoords p v s, hyperboloidGeodesicCoords_mem p v hvp hvv s⟩

set_option backward.isDefEq.respectTransparency false in
/-- The explicit curve is smooth, starts at its prescribed point, and has unit speed for the hyperboloid metric. -/
theorem hyperboloidGeodesic_properties (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1) :
  let γ := hyperboloidGeodesic p v hvp hvv
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ ∧ γ 0 = p ∧
  (∀ s, HasDerivAt (fun t => (γ t).val) (Real.sinh s • p.val + Real.cosh s • v) s) ∧
  (letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
   ∀ s, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s (1 : ℝ)‖ = 1) := by
  let γ := hyperboloidGeodesic p v hvp hvv
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hPair : ∀ a b c d : ℝ,
      lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) = -a*c+b*d := by
    intro a b c d
    have he : lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) =
        a*c*lorentzBilinear p.val p.val +
        (a*d+b*c)*lorentzBilinear v p.val + b*d*lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp, hvp, hvv]
    ring
  have hc : ContDiff ℝ ∞ (hyperboloidGeodesicCoords p v) := by
    unfold hyperboloidGeodesicCoords
    fun_prop
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ := by
    apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
    exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.contMDiffOn.comp_contMDiff
      hc.contMDiff (fun s => hyperboloid_denominator_pos (γ s))
  have hd : ∀ s, HasDerivAt (hyperboloidGeodesicCoords p v)
      (Real.sinh s • p.val+Real.cosh s • v) s := by
    intro s
    exact ((Real.hasDerivAt_cosh s).smul_const p.val).add
      ((Real.hasDerivAt_sinh s).smul_const v)
  have hzero : γ 0 = p := by
    apply Subtype.ext
    simp [γ, hyperboloidGeodesic, hyperboloidGeodesicCoords]
  refine ⟨hs, hzero, hd, ?_⟩
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  intro s
  let D := Real.sinh s • p.val+Real.cosh s • v
  let w := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s (1 : ℝ)
  have hD : lorentzBilinear D D = 1 := by
    dsimp [D]
    rw [hPair]
    nlinarith [Real.cosh_sq_sub_sinh_sq s]
  have hmixed : lorentzBilinear D (γ s).val = 0 := by
    change lorentzBilinear (Real.sinh s • p.val+Real.cosh s • v)
      (Real.cosh s • p.val+Real.sinh s • v) = 0
    rw [hPair]
    ring
  have hi : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) (fun q : Hyperboloid => q.val) (γ s) w = D := by
    have he : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 3 → ℝ)
        (hyperboloidGeodesicCoords p v) s = fderiv ℝ (hyperboloidGeodesicCoords p v) s :=
      mfderiv_eq_fderiv
    have hchain := mfderiv_comp_apply s
      (contMDiff_hyperboloid_val.mdifferentiable (by simp) _)
      (hs.mdifferentiable (by simp) _) (1 : ℝ)
    have heval := congrArg (fun L : ℝ →L[ℝ] (Fin 3 → ℝ) => L 1)
      (he.trans (hd s).hasFDerivAt.fderiv)
    exact hchain.symm.trans (heval.trans (by simp [D]))
  have hnorm : ‖w‖^2 = hyperboloidMetric.inner (γ s) w w :=
    (real_inner_self_eq_norm_sq w).symm
  rw [hyperboloidMetric_inner, hyperboloidTangentTensor_apply, hi, hD] at hnorm
  have hn := norm_nonneg w
  change ‖w‖ = 1
  nlinarith

/-- The point and unit tangent span a timelike plane whose entire upper-sheet section is the explicit curve. -/
theorem hyperboloidGeodesic_plane (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1) :
  let P := Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ))
  LinearIndependent ℝ ![p.val, v] ∧ Module.finrank ℝ P = 2 ∧
  (∀ a b : ℝ, lorentzBilinear (a • p.val + b • v) (a • p.val + b • v) = -a^2+b^2) ∧
  Set.range (hyperboloidGeodesic p v hvp hvv) = {q : Hyperboloid | q.val ∈ P} := by
  let P := Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ))
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hpv : lorentzBilinear p.val v = 0 := (lorentzBilinear_symm p.val v).trans hvp
  have hscale : ∀ (a : ℝ) (x y : Fin 3 → ℝ),
      lorentzBilinear (a • x) y = a * lorentzBilinear x y := by
    intro a x y
    simp only [lorentzBilinear_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hvne : v ≠ 0 := by
    intro hz
    have h := hvv
    simp [hz, lorentzBilinear_apply] at h
  have hlin : LinearIndependent ℝ ![p.val, v] := by
    apply linearIndependent_fin2.mpr
    constructor
    · exact hvne
    · intro a ha
      change a • v = p.val at ha
      have h := congrArg (fun x => lorentzBilinear x p.val) ha
      rw [hscale, hvp, mul_zero, hpp] at h
      norm_num at h
  have hr : Set.range ![p.val, v] = ({p.val, v} : Set (Fin 3 → ℝ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hdim : Module.finrank ℝ P = 2 := by
    have hd := finrank_span_eq_card hlin
    rw [hr] at hd
    exact hd
  have hGram : ∀ a b : ℝ,
      lorentzBilinear (a • p.val + b • v) (a • p.val + b • v) = -a^2+b^2 := by
    intro a b
    have he : lorentzBilinear (a • p.val + b • v) (a • p.val + b • v) =
        a^2 * lorentzBilinear p.val p.val +
        2*a*b * lorentzBilinear v p.val + b^2 * lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp, hvp, hvv]
    ring
  have hpP : p.val ∈ P := Submodule.subset_span (by simp)
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  refine ⟨hlin, hdim, hGram, ?_⟩
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    exact P.add_mem (P.smul_mem (Real.cosh s) hpP) (P.smul_mem (Real.sinh s) hvP)
  · intro hq
    rcases Submodule.mem_span_pair.mp hq with ⟨a, b, he⟩
    have hqq : lorentzBilinear q.val q.val = -1 := by
      simpa only [lorentzBilinear_apply, pow_two] using q.property.1
    have hcoeff : a^2-b^2=1 := by
      have hg := hGram a b
      rw [he, hqq] at hg
      linarith
    have hpair : -lorentzBilinear p.val q.val = a := by
      rw [← he]
      have hx : lorentzBilinear p.val (a • p.val+b • v) =
          a * lorentzBilinear p.val p.val + b * lorentzBilinear p.val v := by
        simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hx, hpp, hpv]
      ring
    have ha : 0 < a := hpair ▸ hyperboloid_neg_lorentz_pos p q
    have hcosh : Real.cosh (Real.arsinh b) = a := by
      rw [Real.cosh_arsinh]
      have hs : 1+b^2=a^2 := by linarith
      rw [hs, Real.sqrt_sq ha.le]
    refine ⟨Real.arsinh b, ?_⟩
    apply Subtype.ext
    change Real.cosh (Real.arsinh b) • p.val + Real.sinh (Real.arsinh b) • v = q.val
    rw [hcosh, Real.sinh_arsinh]
    exact he

/-- Distance along the explicit unit-speed curve is the absolute difference of parameters. -/
theorem hyperboloidGeodesic_lengthDist (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1) (s t : ℝ) :
  hyperboloidLengthDist (hyperboloidGeodesic p v hvp hvv s)
    (hyperboloidGeodesic p v hvp hvv t) = |t-s| := by
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hPair : ∀ a b c d : ℝ,
      lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) = -a*c+b*d := by
    intro a b c d
    have he : lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) =
        a*c*lorentzBilinear p.val p.val +
        (a*d+b*c)*lorentzBilinear v p.val + b*d*lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp, hvp, hvv]
    ring
  have hinner : -lorentzBilinear (hyperboloidGeodesic p v hvp hvv s).val
      (hyperboloidGeodesic p v hvp hvv t).val = Real.cosh (t-s) := by
    change -lorentzBilinear (Real.cosh s • p.val+Real.sinh s • v)
      (Real.cosh t • p.val+Real.sinh t • v) = Real.cosh (t-s)
    rw [hPair, Real.cosh_sub]
    ring
  apply Real.cosh_injOn
    (hyperboloidLengthDist_nonneg_eq_zero
      (hyperboloidGeodesic p v hvp hvv s) (hyperboloidGeodesic p v hvp hvv t)).1
    (show |t-s| ∈ Ici (0 : ℝ) from abs_nonneg (t-s))
  rw [(hyperboloidLengthDist_cosh
    (hyperboloidGeodesic p v hvp hvv s) (hyperboloidGeodesic p v hvp hvv t)).1, Real.cosh_abs]
  exact hinner

/-- Every finite subsegment has its parameter length and agrees with the canonical minimizing segment, including coincident endpoints. -/
theorem hyperboloidGeodesic_subsegment (p : Hyperboloid) (v : Fin 3 → ℝ)
    (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1)
    (a b : ℝ) (hab : a ≤ b) :
  let γ := hyperboloidGeodesic p v hvp hvv
  let cut : Fin 2 → ℝ := fun i => if i = 0 then a else b
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  IsPiecewiseC1On 𝓘(ℝ, ℂ) γ a b 1 cut ∧
  piecewiseC1Length hyperboloidMetric γ cut = b-a ∧
  pathELength 𝓘(ℝ, ℂ) γ a b = ENNReal.ofReal (b-a) ∧
  (∀ r ∈ Set.Icc 0 (b-a), γ (a+r) = hyperboloidSegment (γ a) (γ b) r) ∧
  γ '' Set.Icc a b = hyperboloidSegment (γ a) (γ b) '' Set.Icc 0 (b-a) := by
  let γ := hyperboloidGeodesic p v hvp hvv
  let cut : Fin 2 → ℝ := fun i => if i = 0 then a else b
  letI : Bundle.RiemannianBundle (fun q : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) q) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  have hs := (hyperboloidGeodesic_properties p v hvp hvv).1
  have hw : IsPiecewiseC1On 𝓘(ℝ, ℂ) γ a b 1 cut := by
    refine ⟨?_, by simp [cut], by simp [cut], hs.continuous.continuousOn, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [cut]
    · intro i hi
      exact (hs.of_le (by simp)).contMDiffOn
  rcases hw.speed_length hyperboloidMetric with
    ⟨hpiece, hinterval, hmeas, hint, hreal, hset, hnonneg, hconvert,
      hfinite, hsum, hwhole, hpath, hpathfinite⟩
  have hnorm : (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)‖) =
      (fun _ : ℝ => (1 : ℝ)) :=
    funext (hyperboloidGeodesic_properties p v hvp hvv).2.2.2
  rw [hnorm] at hreal
  have hlength : piecewiseC1Length hyperboloidMetric γ cut = b-a := by
    simpa using hreal.symm

  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hPair : ∀ a b c d : ℝ,
      lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) = -a*c+b*d := by
    intro a b c d
    have he : lorentzBilinear (a • p.val+b • v) (c • p.val+d • v) =
        a*c*lorentzBilinear p.val p.val +
        (a*d+b*c)*lorentzBilinear v p.val + b*d*lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp, hvp, hvv]
    ring
  have hpathLen : pathELength 𝓘(ℝ, ℂ) γ a b = ENNReal.ofReal (b-a) :=
    hpath.trans (congrArg ENNReal.ofReal hlength)
  have hparam : ∀ r ∈ Icc 0 (b-a), γ (a+r) = hyperboloidSegment (γ a) (γ b) r := by
    by_cases heq : a = b
    · subst b
      intro r hr
      have hr0 : r = 0 := by
        have hleft := hr.1
        have hright := hr.2
        linarith
      subst r
      simpa only [add_zero] using (hyperboloidSegment_properties (γ a) (γ a)).2.1.symm
    · have hablt : a < b := lt_of_le_of_ne hab heq
      have hdist : hyperboloidLengthDist (γ a) (γ b) = b-a := by
        rw [hyperboloidGeodesic_lengthDist]
        exact abs_of_nonneg (sub_nonneg.mpr hab)
      have hpq : γ a ≠ γ b :=
        (hyperboloidLengthDist_nonneg_eq_zero (γ a) (γ b)).2.2.mp
          (by rw [hdist]; exact sub_pos.mpr hablt)
      let va := Real.sinh a • p.val+Real.cosh a • v
      have hvaPerp : lorentzBilinear va (γ a).val = 0 := by
        change lorentzBilinear (Real.sinh a • p.val+Real.cosh a • v)
          (Real.cosh a • p.val+Real.sinh a • v) = 0
        rw [hPair]
        ring
      have hvaUnit : lorentzBilinear va va = 1 := by
        dsimp [va]
        rw [hPair]
        nlinarith [Real.cosh_sq_sub_sinh_sq a]
      have hshift : ∀ r : ℝ, (γ (a+r)).val =
          Real.cosh r • (γ a).val+Real.sinh r • va := by
        intro r
        funext i
        simp only [γ, hyperboloidGeodesic, hyperboloidGeodesicCoords, va,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.cosh_add, Real.sinh_add]
        ring
      have hend : (γ b).val =
          Real.cosh (hyperboloidLengthDist (γ a) (γ b)) • (γ a).val+
          Real.sinh (hyperboloidLengthDist (γ a) (γ b)) • va := by
        rw [hdist]
        have he : a+(b-a)=b := by ring
        simpa only [he] using hshift (b-a)
      have hva := (hyperboloidSegmentInitial_endpoint (γ a) (γ b) hpq).2.2 va hend
      intro r hr
      apply Subtype.ext
      rw [hshift, hva, (hyperboloidSegment_initial_formula (γ a) (γ b) hpq).2.2.2 r]
  refine ⟨hw, hlength, hpathLen, hparam, ?_⟩
  apply Set.Subset.antisymm
  · rintro q ⟨t, ht, rfl⟩
    refine ⟨t-a, ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩, ?_⟩
    have he : a+(t-a)=t := by ring
    exact (by simpa only [he] using (hparam (t-a) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩).symm)
  · rintro q ⟨r, hr, rfl⟩
    refine ⟨a+r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, hparam r hr⟩

/-- A Lorentz timelike plane is a two-dimensional subspace containing a negative vector. -/
def IsLorentzTimelikePlane (P : Submodule ℝ (Fin 3 → ℝ)) : Prop :=
  Module.finrank ℝ P = 2 ∧ ∃ w : Fin 3 → ℝ, w ∈ P ∧ lorentzBilinear w w < 0

/-- Every timelike plane admits an upper-sheet point and unit tangent parametrizing its entire hyperboloid section. -/
theorem IsLorentzTimelikePlane.exists_hyperboloidGeodesic
    {P : Submodule ℝ (Fin 3 → ℝ)} (hP : IsLorentzTimelikePlane P) :
  ∃ p : Hyperboloid, ∃ v : Fin 3 → ℝ,
    ∃ hvp : lorentzBilinear v p.val = 0, ∃ hvv : lorentzBilinear v v = 1,
      p.val ∈ P ∧ v ∈ P ∧
      P = Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ)) ∧
      Set.range (hyperboloidGeodesic p v hvp hvv) = {q : Hyperboloid | q.val ∈ P} := by
  rcases hP with ⟨hdim, w, hwP, hwneg⟩
  have hscale : ∀ (a b : ℝ) (x y : Fin 3 → ℝ),
      lorentzBilinear (a • x) (b • y) = a*b*lorentzBilinear x y := by
    intro a b x y
    simp only [lorentzBilinear_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwt : w 2 ≠ 0 := by
    intro hz
    have hn := hwneg
    simp only [lorentzBilinear_apply] at hn
    rw [hz] at hn
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  let wplus : Fin 3 → ℝ := if 0 < w 2 then w else -w
  have hwplusP : wplus ∈ P := by
    dsimp [wplus]
    split_ifs
    · exact hwP
    · exact P.neg_mem hwP
  have hwplusT : 0 < wplus 2 := by
    dsimp [wplus]
    split_ifs with h
    · exact h
    · change 0 < -(w 2)
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hwt)
  have hwplusQ : lorentzBilinear wplus wplus = lorentzBilinear w w := by
    dsimp [wplus]
    split_ifs
    · rfl
    · simp only [lorentzBilinear_apply, Pi.neg_apply, neg_mul_neg]
  let radius := Real.sqrt (-lorentzBilinear w w)
  have hrpos : 0 < radius := Real.sqrt_pos.mpr (neg_pos.mpr hwneg)
  have hrne : radius ≠ 0 := ne_of_gt hrpos
  have hrsq : radius^2 = -lorentzBilinear w w := Real.sq_sqrt (neg_nonneg.mpr hwneg.le)
  let pvec : Fin 3 → ℝ := radius⁻¹ • wplus
  have hpQ : lorentzBilinear pvec pvec = -1 := by
    rw [show pvec = radius⁻¹ • wplus from rfl, hscale, hwplusQ]
    have hww : lorentzBilinear w w = -(radius^2) := by linarith
    rw [hww]
    field_simp [hrne]
    <;> ring
  have hpT : 0 < pvec 2 := mul_pos (inv_pos.mpr hrpos) hwplusT
  let p : Hyperboloid := ⟨pvec, by
    simpa only [lorentzBilinear_apply, pow_two] using hpQ, hpT⟩
  have hpP : p.val ∈ P := P.smul_mem _ hwplusP
  have hpne : p.val ≠ 0 := by
    intro hz
    have h := hpT
    change 0 < p.val 2 at h
    rw [hz] at h
    simp at h
  have hpSpan : Submodule.span ℝ ({p.val} : Set (Fin 3 → ℝ)) ≤ P := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x = p.val := by simpa using hx
    subst x
    exact hpP
  have hz : ∃ z : Fin 3 → ℝ, z ∈ P ∧
      z ∉ Submodule.span ℝ ({p.val} : Set (Fin 3 → ℝ)) := by
    by_contra hnone
    push_neg at hnone
    have heq : P = Submodule.span ℝ ({p.val} : Set (Fin 3 → ℝ)) :=
      le_antisymm (fun z hz => hnone z hz) hpSpan
    have hdOne := finrank_span_singleton («K» := ℝ) hpne
    rw [← heq, hdim] at hdOne
    norm_num at hdOne
  rcases hz with ⟨z, hzP, hznot⟩
  let u := z + lorentzBilinear z p.val • p.val
  have huP : u ∈ P := P.add_mem hzP (P.smul_mem _ hpP)
  have hpp : lorentzBilinear p.val p.val = -1 := hpQ
  have hup : lorentzBilinear u p.val = 0 := by
    have he : lorentzBilinear u p.val =
        lorentzBilinear z p.val + lorentzBilinear z p.val * lorentzBilinear p.val p.val := by
      simp only [u, lorentzBilinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hpp]
    ring
  have hune : u ≠ 0 := by
    intro hu0
    apply hznot
    have he : z = -(lorentzBilinear z p.val) • p.val := by
      have he' : z + lorentzBilinear z p.val • p.val = 0 := hu0
      have he'' := eq_neg_of_add_eq_zero_left he'
      simpa only [neg_smul] using he''
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have huq : 0 < lorentzBilinear u u :=
    lorentzKer_quadratic_pos p u ((lorentzBilinear_symm p.val u).trans hup) hune
  let normU := Real.sqrt (lorentzBilinear u u)
  have hnpos : 0 < normU := Real.sqrt_pos.mpr huq
  have hnne : normU ≠ 0 := ne_of_gt hnpos
  have hnsq : normU^2 = lorentzBilinear u u := Real.sq_sqrt huq.le
  let v : Fin 3 → ℝ := normU⁻¹ • u
  have hvP : v ∈ P := P.smul_mem _ huP
  have hvp : lorentzBilinear v p.val = 0 := by
    have he := hscale normU⁻¹ 1 u p.val
    simpa only [one_smul, mul_one, hup, mul_zero] using he
  have hvv : lorentzBilinear v v = 1 := by
    change lorentzBilinear (normU⁻¹ • u) (normU⁻¹ • u) = 1
    rw [hscale, ← hnsq]
    field_simp [hnne]
    <;> ring
  have hplane := hyperboloidGeodesic_plane p v hvp hvv
  have hle : Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ)) ≤ P := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases (show x = p.val ∨ x = v from by simpa using hx) with rfl | rfl
    · exact hpP
    · exact hvP
  have heq : Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ)) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (hplane.2.1.trans hdim.symm)
  refine ⟨p, v, hvp, hvv, hpP, hvP, heq.symm, ?_⟩
  simpa only [heq] using hplane.2.2.2

/-- A curve is locally arclength minimizing when every sufficiently short subinterval has a finite piecewise-C1 length witness realizing its parameter distance. -/
def IsLocallyArclengthMinimizingHyperboloid (γ : ℝ → Hyperboloid) : Prop :=
  ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
    ∀ a ∈ Set.Ioo (t-ε) (t+ε), ∀ b ∈ Set.Ioo (t-ε) (t+ε), a ≤ b →
      ∃ n : ℕ, ∃ cut : Fin (n+1) → ℝ,
        IsPiecewiseC1On 𝓘(ℝ, ℂ) γ a b n cut ∧
        piecewiseC1Length hyperboloidMetric γ cut = b-a ∧
        hyperboloidLengthDist (γ a) (γ b) = b-a

/-- An all-real locally arclength-minimizing curve is exactly a hyperbolic point-and-unit-tangent parametrization. -/
theorem locallyArclengthMinimizingHyperboloid_iff (γ : ℝ → Hyperboloid) :
  IsLocallyArclengthMinimizingHyperboloid γ ↔
    ∃ p : Hyperboloid, ∃ v : Fin 3 → ℝ,
      ∃ hvp : lorentzBilinear v p.val = 0, ∃ hvv : lorentzBilinear v v = 1,
        ∀ s : ℝ, γ s = hyperboloidGeodesic p v hvp hvv s := by
  constructor
  · intro hlocal
    have localParameter (t : ℝ) :
        ∃ a b : ℝ, a < t ∧ t < b ∧ γ a ≠ γ b ∧
          ∀ u ∈ Icc a b, γ u = hyperboloidSegment (γ a) (γ b) (u-a) := by
      rcases hlocal t with ⟨ε, hε, hpiece⟩
      let a := t-ε/2
      let b := t+ε/2
      have hat : a < t := by dsimp [a]; linarith
      have htb : t < b := by dsimp [b]; linarith
      have ha : a ∈ Ioo (t-ε) (t+ε) := by dsimp [a]; constructor <;> linarith
      have hb : b ∈ Ioo (t-ε) (t+ε) := by dsimp [b]; constructor <;> linarith
      have hab : a < b := lt_trans hat htb
      rcases hpiece a ha b hb hab.le with ⟨n, cut, hC1, hLen, hDist⟩
      let η : PiecewiseC1CurveOn 𝓘(ℝ, ℂ) a b n cut (γ a) (γ b) :=
        ⟨γ, hC1, rfl, rfl⟩
      have hmin : piecewiseC1Length hyperboloidMetric η.val cut =
          hyperboloidLengthDist (γ a) (γ b) := hLen.trans hDist.symm
      have hrec := (hyperboloid_minimizer_image η hmin).2.1
      have hpq : γ a ≠ γ b :=
        (hyperboloidLengthDist_nonneg_eq_zero (γ a) (γ b)).2.2.mp
          (by rw [hDist]; exact sub_pos.mpr hab)
      refine ⟨a, b, hat, htb, hpq, ?_⟩
      intro u hu
      have huJ : u ∈ Ioo (t-ε) (t+ε) :=
        ⟨lt_of_lt_of_le ha.1 hu.1, lt_of_le_of_lt hu.2 hb.2⟩
      rcases hpiece a ha u huJ hu.1 with ⟨nu, cutu, hC1u, hLenu, hDistu⟩
      have hr : hyperboloidRadius (centerHyperboloid (γ a) (γ u)) = u-a :=
        (hyperboloidLengthDist_center (γ a) (γ u)).2.2.2.2.symm.trans hDistu
      have hpoint := hrec u hu
      change γ u = hyperboloidSegment (γ a) (γ b)
        (hyperboloidRadius (centerHyperboloid (γ a) (γ u))) at hpoint
      simpa only [hr] using hpoint
    have signedPair (p : Hyperboloid) (v : Fin 3 → ℝ)
        (hvp : lorentzBilinear v p.val = 0) (hvv : lorentzBilinear v v = 1)
        (a : ℝ) :
        let Avec := Real.cosh a • p.val - Real.sinh a • v
        let Bvec := (-Real.sinh a) • p.val + Real.cosh a • v
        ∃ p₀ : Hyperboloid, p₀.val = Avec ∧
          lorentzBilinear Bvec p₀.val = 0 ∧ lorentzBilinear Bvec Bvec = 1 ∧
          ∀ u : ℝ, (hyperboloidGeodesic p v hvp hvv (u-a)).val =
            Real.cosh u • p₀.val + Real.sinh u • Bvec := by
      let Avec := Real.cosh a • p.val - Real.sinh a • v
      let Bvec := (-Real.sinh a) • p.val + Real.cosh a • v
      let p₀ := hyperboloidGeodesic p v hvp hvv (-a)
      have hp₀ : p₀.val = Avec := by
        simp [p₀, hyperboloidGeodesic, hyperboloidGeodesicCoords, Avec,
          Real.cosh_neg, Real.sinh_neg, sub_eq_add_neg]
      have hGram := (hyperboloidGeodesic_plane p v hvp hvv).2.2.1
      have hAA : lorentzBilinear Avec Avec = -1 := by
        have h := hGram (Real.cosh a) (-Real.sinh a)
        have hc := Real.cosh_sq_sub_sinh_sq a
        simp only [neg_sq] at h
        change lorentzBilinear Avec Avec = -1
        have he : Real.cosh a • p.val + (-Real.sinh a) • v = Avec := by
          simp [Avec, sub_eq_add_neg]
        rw [he] at h
        nlinarith
      have hBB : lorentzBilinear Bvec Bvec = 1 := by
        have h := hGram (-Real.sinh a) (Real.cosh a)
        have hc := Real.cosh_sq_sub_sinh_sq a
        change lorentzBilinear Bvec Bvec = _ at h
        nlinarith
      have hsum : Avec + Bvec =
          (Real.cosh a - Real.sinh a) • p.val +
            (Real.cosh a - Real.sinh a) • v := by
        funext i
        simp only [Avec, Bvec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        <;> ring
      have hSS : lorentzBilinear (Avec+Bvec) (Avec+Bvec) = 0 := by
        rw [hsum, hGram]
        ring
      have hpolar : lorentzBilinear (Avec+Bvec) (Avec+Bvec) =
          lorentzBilinear Avec Avec + 2 * lorentzBilinear Bvec Avec +
            lorentzBilinear Bvec Bvec := by
        simp only [lorentzBilinear_apply, Pi.add_apply]
        ring
      have hBA : lorentzBilinear Bvec Avec = 0 := by linarith
      refine ⟨p₀, hp₀, ?_, hBB, ?_⟩
      · simpa only [hp₀] using hBA
      · intro u
        rw [hp₀]
        funext i
        simp only [hyperboloidGeodesic, hyperboloidGeodesicCoords, Avec, Bvec,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Real.cosh_sub, Real.sinh_sub]
        ring
    have globalAmbient (A₀ B₀ : Fin 3 → ℝ)
        (hcover : ∀ x : ℝ, ∃ intervalJ : Set ℝ, IsOpen intervalJ ∧ x ∈ intervalJ ∧
          ∃ Avec Bvec : Fin 3 → ℝ,
            ∀ s ∈ intervalJ, (γ s).val = Real.cosh s • Avec + Real.sinh s • Bvec)
        (hzero : ∃ intervalJ : Set ℝ, IsOpen intervalJ ∧ (0 : ℝ) ∈ intervalJ ∧
          ∀ s ∈ intervalJ, (γ s).val = Real.cosh s • A₀ + Real.sinh s • B₀) :
        ∀ s : ℝ, (γ s).val = Real.cosh s • A₀ + Real.sinh s • B₀ := by
      have rigid : ∀ u v : ℝ, u < v → ∀ A₁ B₁ A₂ B₂ : Fin 3 → ℝ,
          Real.cosh u • A₁ + Real.sinh u • B₁ = Real.cosh u • A₂ + Real.sinh u • B₂ →
          Real.cosh v • A₁ + Real.sinh v • B₁ = Real.cosh v • A₂ + Real.sinh v • B₂ →
          A₁ = A₂ ∧ B₁ = B₂ := by
        intro u v huv A₁ B₁ A₂ B₂ hu hv
        let det := Real.cosh u * Real.sinh v - Real.sinh u * Real.cosh v
        have hdet : det ≠ 0 := by
          have he : det = Real.sinh (v-u) := by dsimp [det]; rw [Real.sinh_sub]; ring
          rw [he]
          exact ne_of_gt (Real.sinh_pos_iff.mpr (sub_pos.mpr huv))
        have hcoord : ∀ i, A₁ i = A₂ i ∧ B₁ i = B₂ i := by
          intro i
          have heu := congrArg (fun f : Fin 3 → ℝ => f i) hu
          have hev := congrArg (fun f : Fin 3 → ℝ => f i) hv
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heu hev
          have hA : det * (A₁ i-A₂ i) = 0 := by
            dsimp [det]
            linear_combination Real.sinh v * heu - Real.sinh u * hev
          have hB : det * (B₁ i-B₂ i) = 0 := by
            dsimp [det]
            linear_combination Real.cosh u * hev - Real.cosh v * heu
          exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hA).resolve_left hdet),
            sub_eq_zero.mp ((mul_eq_zero.mp hB).resolve_left hdet)⟩
        exact ⟨funext (fun i => (hcoord i).1), funext (fun i => (hcoord i).2)⟩
      let U : Set ℝ := {x | ∃ intervalJ : Set ℝ, IsOpen intervalJ ∧ x ∈ intervalJ ∧
        ∀ s ∈ intervalJ, (γ s).val = Real.cosh s • A₀ + Real.sinh s • B₀}
      have hUopen : IsOpen U := by
        apply isOpen_iff_forall_mem_open.mpr
        rintro x ⟨intervalJ, hJ, hx, hform⟩
        exact ⟨intervalJ, fun y hy => ⟨intervalJ, hJ, hy, hform⟩, hJ, hx⟩
      have hUzero : (0 : ℝ) ∈ U := hzero
      have hUcompl : IsOpen Uᶜ := by
        apply isOpen_iff_forall_mem_open.mpr
        intro x hx
        rcases hcover x with ⟨intervalJ, hJ, hxJ, Avec, Bvec, hformJ⟩
        refine ⟨intervalJ, ?_, hJ, hxJ⟩
        intro y hyJ hyU
        rcases hyU with ⟨intervalK, hK, hyK, hformK⟩
        rcases (hJ.inter hK).exists_Ioo_subset ⟨y, hyJ, hyK⟩ with ⟨l, r, hlr, hsub⟩
        let u := (2*l+r)/3
        let v := (l+2*r)/3
        have hu : u ∈ intervalJ ∩ intervalK := hsub (by dsimp [u]; constructor <;> linarith)
        have hv : v ∈ intervalJ ∩ intervalK := hsub (by dsimp [v]; constructor <;> linarith)
        have huv : u < v := by dsimp [u, v]; linarith
        have heq := rigid u v huv Avec Bvec A₀ B₀
          ((hformJ u hu.1).symm.trans (hformK u hu.2))
          ((hformJ v hv.1).symm.trans (hformK v hv.2))
        apply hx
        refine ⟨intervalJ, hJ, hxJ, ?_⟩
        intro s hs
        simpa only [heq.1, heq.2] using hformJ s hs
      have hUclosed : IsClosed U := isOpen_compl_iff.mp hUcompl
      have hUall : U = Set.univ := (show IsClopen U from ⟨hUclosed, hUopen⟩).eq_univ ⟨0, hUzero⟩
      intro s
      have hs : s ∈ U := by rw [hUall]; exact Set.mem_univ s
      rcases hs with ⟨intervalJ, hJ, hsJ, hform⟩
      exact hform s hsJ
    -- G03b: actual cover is DERIVED from hlocal; no new public cover premise.
    have fullCover : ∀ x : ℝ, ∃ intervalJ : Set ℝ, IsOpen intervalJ ∧ x ∈ intervalJ ∧
        ∃ p₀ : Hyperboloid, ∃ Bvec : Fin 3 → ℝ,
          lorentzBilinear Bvec p₀.val = 0 ∧ lorentzBilinear Bvec Bvec = 1 ∧
          ∀ s ∈ intervalJ, (γ s).val = Real.cosh s • p₀.val + Real.sinh s • Bvec := by
      intro x
      rcases localParameter x with ⟨a, b, hax, hxb, hpq, hparam⟩
      let initVec := hyperboloidSegmentInitial (γ a) (γ b)
      have hinit := hyperboloidSegment_initial_formula (γ a) (γ b) hpq
      have hperp : lorentzBilinear initVec (γ a).val = 0 := hinit.1
      have hunit : lorentzBilinear initVec initVec = 1 := hinit.2.1
      let Bvec := (-Real.sinh a) • (γ a).val + Real.cosh a • initVec
      rcases signedPair (γ a) initVec hperp hunit a with
        ⟨p₀, hp₀, hBperp, hBunit, hshift⟩
      change lorentzBilinear Bvec p₀.val = 0 at hBperp
      change lorentzBilinear Bvec Bvec = 1 at hBunit
      change ∀ u : ℝ, (hyperboloidGeodesic (γ a) initVec hperp hunit (u-a)).val =
        Real.cosh u • p₀.val + Real.sinh u • Bvec at hshift
      refine ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, p₀, Bvec, hBperp, hBunit, ?_⟩
      intro s hs
      calc
        (γ s).val = (hyperboloidSegment (γ a) (γ b) (s-a)).val :=
          congrArg Subtype.val (hparam s ⟨hs.1.le, hs.2.le⟩)
        _ = Real.cosh (s-a) • (γ a).val + Real.sinh (s-a) • initVec :=
          hinit.2.2.2 (s-a)
        _ = (hyperboloidGeodesic (γ a) initVec hperp hunit (s-a)).val := rfl
        _ = Real.cosh s • p₀.val + Real.sinh s • Bvec := hshift s
    -- Retain the ACTUAL upper origin and both Gram proofs before forgetting fields.
    rcases fullCover 0 with ⟨intervalJ₀, hJ₀, hzero, p₀, B₀, hperp₀, hunit₀, hform₀⟩
    have ambientCover : ∀ x : ℝ, ∃ intervalJ : Set ℝ, IsOpen intervalJ ∧ x ∈ intervalJ ∧
        ∃ Avec Bvec : Fin 3 → ℝ,
          ∀ s ∈ intervalJ, (γ s).val = Real.cosh s • Avec + Real.sinh s • Bvec := by
      intro x
      rcases fullCover x with ⟨intervalJ, hJ, hx, p, v, hpv, hvv, hform⟩
      exact ⟨intervalJ, hJ, hx, p.val, v, hform⟩
    have globalEq := globalAmbient p₀.val B₀ ambientCover ⟨intervalJ₀, hJ₀, hzero, hform₀⟩
    refine ⟨p₀, B₀, hperp₀, hunit₀, ?_⟩
    intro s
    apply Subtype.ext
    change (γ s).val = Real.cosh s • p₀.val + Real.sinh s • B₀
    exact globalEq s
  · rintro ⟨p, v, hvp, hvv, hglobal⟩
    have explicitLocal :
        IsLocallyArclengthMinimizingHyperboloid (hyperboloidGeodesic p v hvp hvv) := by
      intro t
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha b hb hab
      let cut : Fin 2 → ℝ := fun i => if i = 0 then a else b
      have hseg := hyperboloidGeodesic_subsegment p v hvp hvv a b hab
      refine ⟨1, cut, hseg.1, hseg.2.1, ?_⟩
      rw [hyperboloidGeodesic_lengthDist]
      exact abs_of_nonneg (sub_nonneg.mpr hab)
    have hfun : γ = hyperboloidGeodesic p v hvp hvv := funext hglobal
    simpa only [hfun] using explicitLocal

/-- Distinct hyperboloid endpoints span the timelike plane of their minimizing segment. -/
theorem hyperboloid_distinct_span_plane (p q : Hyperboloid) (hpq : p ≠ q) :
  let v := hyperboloidSegmentInitial p q
  Submodule.span ℝ ({p.val, q.val} : Set (Fin 3 → ℝ)) =
    Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ)) ∧
  IsLorentzTimelikePlane (Submodule.span ℝ ({p.val, q.val} : Set (Fin 3 → ℝ))) ∧
  (∀ hvp : lorentzBilinear v p.val = 0, ∀ hvv : lorentzBilinear v v = 1,
    Set.range (hyperboloidGeodesic p v hvp hvv) =
      {r : Hyperboloid | r.val ∈ Submodule.span ℝ ({p.val, q.val} : Set (Fin 3 → ℝ))}) := by
  let v := hyperboloidSegmentInitial p q
  let S := Submodule.span ℝ ({p.val, q.val} : Set (Fin 3 → ℝ))
  let T := Submodule.span ℝ ({p.val, v} : Set (Fin 3 → ℝ))
  have hinit := hyperboloidSegment_initial_formula p q hpq
  have hend := hyperboloidSegmentInitial_endpoint p q hpq
  have hpS : p.val ∈ S := Submodule.subset_span (by simp)
  have hqS : q.val ∈ S := Submodule.subset_span (by simp)
  have hpT : p.val ∈ T := Submodule.subset_span (by simp)
  have hvT : v ∈ T := Submodule.subset_span (by simp)
  have hqeq : q.val = Real.cosh (hyperboloidLengthDist p q) • p.val +
      Real.sinh (hyperboloidLengthDist p q) • v :=
    (congrArg Subtype.val (hyperboloidSegment_properties p q).2.2.1).symm.trans
      (hinit.2.2.2 (hyperboloidLengthDist p q))
  have hqT : q.val ∈ T := by
    rw [hqeq]
    exact T.add_mem (T.smul_mem _ hpT) (T.smul_mem _ hvT)
  have hvS : v ∈ S := by
    rw [show v = (Real.sinh (hyperboloidLengthDist p q))⁻¹ •
      (q.val-Real.cosh (hyperboloidLengthDist p q) • p.val) from hend.2.1]
    exact S.smul_mem _ (S.sub_mem hqS (S.smul_mem _ hpS))
  have hST : S = T := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro x hx
      rcases (show x=p.val ∨ x=q.val from by simpa using hx) with rfl | rfl
      · exact hpT
      · exact hqT
    · apply Submodule.span_le.mpr
      intro x hx
      rcases (show x=p.val ∨ x=v from by simpa using hx) with rfl | rfl
      · exact hpS
      · exact hvS
  have hplane := hyperboloidGeodesic_plane p v hinit.1 hinit.2.1
  refine ⟨hST, ?_, ?_⟩
  · refine ⟨?_, p.val, hpS, ?_⟩
    · exact (congrArg (fun Q : Submodule ℝ (Fin 3 → ℝ) => Module.finrank ℝ Q) hST).trans hplane.2.1
    · have hpp : lorentzBilinear p.val p.val = -1 := by
        simpa only [lorentzBilinear_apply, pow_two] using p.property.1
      rw [hpp]
      norm_num
  · intro hvp hvv
    have hr := (hyperboloidGeodesic_plane p v hvp hvv).2.2.2
    change Set.range (hyperboloidGeodesic p v hvp hvv) = {r : Hyperboloid | r.val ∈ T} at hr
    change Set.range (hyperboloidGeodesic p v hvp hvv) = {r : Hyperboloid | r.val ∈ S}
    rw [hST]
    exact hr

section LengthTopology

open Bundle

/-- The finite Riemannian length metric on the hyperboloid, retaining its original topology. -/
def hyperboloidLengthMetricSpace : MetricSpace Hyperboloid :=
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle ℂ
      (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨⟨hyperboloidMetric.toContinuousRiemannianMetric.inner,
      hyperboloidMetric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace Hyperboloid := EMetricSpace.ofRiemannianMetric I Hyperboloid
  EMetricSpace.toMetricSpace (fun p q => by
    change riemannianEDist I p q ≠ ⊤
    exact ne_of_lt (hyperboloid_intrinsicEDist_finite p q).2)

/-- The finite Riemannian length metric on the upper half-plane, retaining its original topology. -/
def upperHalfPlaneLengthMetricSpace : MetricSpace UpperHalfPlane :=
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle ℂ
      (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨⟨upperHalfPlaneMetric.toContinuousRiemannianMetric.inner,
      upperHalfPlaneMetric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace UpperHalfPlane := EMetricSpace.ofRiemannianMetric I UpperHalfPlane
  EMetricSpace.toMetricSpace (fun u v => by
    change riemannianEDist I u v ≠ ⊤
    exact ne_of_lt (upperHalfPlane_intrinsicEDist_finite u v).2)

set_option backward.isDefEq.respectTransparency false in
/-- The hyperboloid length metric has the original topology and the same finite-piece distances. -/
theorem hyperboloidLengthMetricSpace_coherence :
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Hyperboloid) ∧
    (letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
     letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
     letI : PseudoEMetricSpace Hyperboloid :=
       @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
     letI : WeakPseudoEMetricSpace Hyperboloid :=
       @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
         (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
     (∀ p q : Hyperboloid,
       edist p q = piecewiseC1EDist hyperboloidMetric p q) ∧
     (∀ p q : Hyperboloid, dist p q = hyperboloidLengthDist p q)) := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  letI : Bundle.RiemannianBundle (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle ℂ (fun x : Hyperboloid => TangentSpace I x) :=
    ⟨⟨hyperboloidMetric.toContinuousRiemannianMetric.inner,
      hyperboloidMetric.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  have hfinite (x y : Hyperboloid) : riemannianEDist I x y ≠ ⊤ :=
    ne_of_lt (hyperboloid_intrinsicEDist_finite x y).2
  have hpieceFinite (x y : Hyperboloid) : piecewiseC1EDist hyperboloidMetric x y ≠ ⊤ :=
    ne_of_lt (hyperboloid_intrinsicEDist_finite x y).1
  have htop : hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = originalTopology := rfl
  refine ⟨htop, ?_⟩
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  constructor
  · intro x y
    change riemannianEDist I x y = piecewiseC1EDist hyperboloidMetric x y
    exact (piecewiseC1EDist_eq_riemannianEDist hyperboloidMetric x y).symm
  · intro x y
    change (riemannianEDist I x y).toReal =
      (piecewiseC1EDist hyperboloidMetric x y).toReal
    exact congrArg ENNReal.toReal
      (piecewiseC1EDist_eq_riemannianEDist hyperboloidMetric x y).symm

/-- The upper-half-plane length metric has the original topology and the same finite-piece distances. -/
theorem upperHalfPlaneLengthMetricSpace_coherence :
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace UpperHalfPlane) ∧
    (letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
     (∀ u v : UpperHalfPlane,
       edist u v = piecewiseC1EDist upperHalfPlaneMetric u v) ∧
     (∀ u v : UpperHalfPlane,
       dist u v = (piecewiseC1EDist upperHalfPlaneMetric u v).toReal)) := by
  let originalTopology : TopologicalSpace UpperHalfPlane := inferInstance
  letI : Bundle.RiemannianBundle (fun x : UpperHalfPlane => TangentSpace I x) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle ℂ (fun x : UpperHalfPlane => TangentSpace I x) :=
    ⟨⟨upperHalfPlaneMetric.toContinuousRiemannianMetric.inner,
      upperHalfPlaneMetric.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  have hfinite (x y : UpperHalfPlane) : riemannianEDist I x y ≠ ⊤ :=
    ne_of_lt (upperHalfPlane_intrinsicEDist_finite x y).2
  have hpieceFinite (x y : UpperHalfPlane) : piecewiseC1EDist upperHalfPlaneMetric x y ≠ ⊤ :=
    ne_of_lt (upperHalfPlane_intrinsicEDist_finite x y).1
  have htop : upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = originalTopology := rfl
  refine ⟨htop, ?_⟩
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  constructor
  · intro x y
    change riemannianEDist I x y = piecewiseC1EDist upperHalfPlaneMetric x y
    exact (piecewiseC1EDist_eq_riemannianEDist upperHalfPlaneMetric x y).symm
  · intro x y
    change (riemannianEDist I x y).toReal =
      (piecewiseC1EDist upperHalfPlaneMetric x y).toReal
    exact congrArg ENNReal.toReal
      (piecewiseC1EDist_eq_riemannianEDist upperHalfPlaneMetric x y).symm

set_option backward.isDefEq.respectTransparency false in
/-- Hyperboloid length balls form the neighborhood basis in the original topology. -/
theorem hyperboloidLengthDist_nhds (p : Hyperboloid) (s : Set Hyperboloid) :
    s ∈ 𝓝 p ↔ ∃ ε : ℝ, 0 < ε ∧
      {q : Hyperboloid | hyperboloidLengthDist p q < ε} ⊆ s := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  have htop := hyperboloidLengthMetricSpace_coherence.1
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  have hdist : ∀ p y : Hyperboloid, dist p y = hyperboloidLengthDist p y :=
    hyperboloidLengthMetricSpace_coherence.2.2
  have hball (ε : ℝ) : Metric.ball p ε =
      {y : Hyperboloid | hyperboloidLengthDist p y < ε} := by
    ext y
    change dist y p < ε ↔ hyperboloidLengthDist p y < ε
    rw [dist_comm, hdist]
  have h := (Metric.mem_nhds_iff : s ∈ 𝓝 p ↔
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ s)
  change s ∈ @nhds Hyperboloid originalTopology p ↔ _
  simpa only [hball] using h

set_option backward.isDefEq.respectTransparency false in
/-- Upper-half-plane length balls form the neighborhood basis in the original topology. -/
theorem upperHalfPlaneLengthDist_nhds (u : UpperHalfPlane)
    (s : Set UpperHalfPlane) :
    s ∈ 𝓝 u ↔ ∃ ε : ℝ, 0 < ε ∧
      {v : UpperHalfPlane |
        (piecewiseC1EDist upperHalfPlaneMetric u v).toReal < ε} ⊆ s := by
  let originalTopology : TopologicalSpace UpperHalfPlane := inferInstance
  have htop := upperHalfPlaneLengthMetricSpace_coherence.1
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  have hdist : ∀ u y : UpperHalfPlane, dist u y = (fun u y => (piecewiseC1EDist upperHalfPlaneMetric u y).toReal) u y :=
    upperHalfPlaneLengthMetricSpace_coherence.2.2
  have hball (ε : ℝ) : Metric.ball u ε =
      {y : UpperHalfPlane | (fun u y => (piecewiseC1EDist upperHalfPlaneMetric u y).toReal) u y < ε} := by
    ext y
    change dist y u < ε ↔ (fun u y => (piecewiseC1EDist upperHalfPlaneMetric u y).toReal) u y < ε
    rw [dist_comm, hdist]
  have h := (Metric.mem_nhds_iff : s ∈ 𝓝 u ↔
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball u ε ⊆ s)
  change s ∈ @nhds UpperHalfPlane originalTopology u ↔ _
  simpa only [hball] using h

/-- The coordinate maps are isometries for the two length metrics. -/
theorem modelLengthMetric_isometries :
    letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
    letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
    letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : PseudoEMetricSpace Hyperboloid :=
      @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : WeakPseudoEMetricSpace Hyperboloid :=
      @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
        (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
    Isometry toHyperboloid ∧ Isometry fromHyperboloid := by
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : Bundle.RiemannianBundle (fun z : UpperHalfPlane => TangentSpace I z) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  have hU := upperHalfPlaneLengthMetricSpace_coherence.2.1
  have hQ := hyperboloidLengthMetricSpace_coherence.2.1
  have hinvU (u : UpperHalfPlane) : fromHyperboloid (toHyperboloid u) = u :=
    fromHyperboloid_toHyperboloid u
  have hinvQ (p : Hyperboloid) : toHyperboloid (fromHyperboloid p) = p :=
    toHyperboloid_fromHyperboloid p
  constructor
  · intro u v
    rw [hQ, hU]
    exact (toHyperboloid_intrinsicEDist u v).1
  · intro p q
    rw [hU, hQ]
    exact (fromHyperboloid_intrinsicEDist p q).1

end LengthTopology

section CenteredLengthBalls

open Set

/-- For a nonnegative radius, the length-distance sublevel about the polar center is
exactly the time-coordinate sublevel. Textbook centered-ball criterion (lines
120–121). -/
theorem hyperboloidLengthDist_center_le_iff (q : Hyperboloid) (R : ℝ)
    (hR : 0 ≤ R) :
    hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R ↔
      q.val 2 ≤ Real.cosh R := by
  have hc : (hyperboloidPolar 0 0).val = ![0, 0, 1] := by
    simp [hyperboloidPolar, hyperboloidPolarCoords]
  have hpair : -lorentzBilinear (hyperboloidPolar 0 0).val q.val = q.val 2 := by
    rw [hc]
    simp [lorentzBilinear_apply]
  have hd := (hyperboloidLengthDist_nonneg_eq_zero (hyperboloidPolar 0 0) q).1
  have hcosh := (hyperboloidLengthDist_cosh (hyperboloidPolar 0 0) q).1
  rw [hpair] at hcosh
  rw [← hcosh, Real.cosh_le_cosh, abs_of_nonneg hd, abs_of_nonneg hR]

/-- A point in a centered length-distance sublevel has time coordinate between one and
cosh of the radius, and spatial squared norm at most sinh squared. Textbook
centered-ball bounds (lines 120–121). -/
theorem hyperboloidLengthDist_center_bounds (q : Hyperboloid) (R : ℝ)
    (hR : 0 ≤ R)
    (hq : hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R) :
    1 ≤ q.val 2 ∧ q.val 2 ≤ Real.cosh R ∧
      q.val 0 ^ 2 + q.val 1 ^ 2 ≤ Real.sinh R ^ 2 := by
  have heq := q.property.1
  have ht := q.property.2
  have hlo : 1 ≤ q.val 2 := by
    by_contra h
    have hlt : q.val 2 < 1 := lt_of_not_ge h
    have hprod := mul_pos (sub_pos.mpr hlt) (add_pos zero_lt_one ht)
    nlinarith [sq_nonneg (q.val 0), sq_nonneg (q.val 1)]
  have hhi := (Hyperbolic.hyperboloidLengthDist_center_le_iff q R hR).mp hq
  have hprod : 0 ≤ (Real.cosh R - q.val 2) * (Real.cosh R + q.val 2) :=
    mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg (Real.cosh_pos R).le ht.le)
  refine ⟨hlo, hhi, ?_⟩
  nlinarith [Real.cosh_sq_sub_sinh_sq R]

/-- The zero-radius centered length-distance sublevel is the singleton center. Textbook
centered-ball zero case (lines 120–121). -/
theorem hyperboloidLengthDist_center_sublevel_zero :
    {q : Hyperboloid | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ 0} =
      {hyperboloidPolar 0 0} := by
  ext q
  change hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ 0 ↔ q = hyperboloidPolar 0 0
  have h := hyperboloidLengthDist_nonneg_eq_zero (hyperboloidPolar 0 0) q
  constructor
  · intro hq
    exact (h.2.1.mp (le_antisymm hq h.1)).symm
  · intro hq
    exact (h.2.1.mpr hq.symm).le

/-- A negative-radius centered length-distance sublevel is empty. Textbook centered-ball
negative case (lines 120–121). -/
theorem hyperboloidLengthDist_center_sublevel_neg (R : ℝ) (hR : R < 0) :
    {q : Hyperboloid | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hd := (hyperboloidLengthDist_nonneg_eq_zero (hyperboloidPolar 0 0) q).1
  exact (not_le_of_gt hR) (le_trans hd hq)

end CenteredLengthBalls

section CenteredCompactBalls

open Set

/-- The ambient centered hyperbolic ball is compact: its quadratic equation and weak time bounds are closed, and its coordinate bounds are finite. Textbook Euclidean compactness argument, lines 121–122. -/
theorem isCompact_hyperboloid_center_ambient (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {v : Fin 3 → ℝ |
      v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 = -1 ∧
      1 ≤ v 2 ∧ v 2 ≤ Real.cosh R} := by
  have hclosed : IsClosed {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 = -1 ∧
      1 ≤ v 2 ∧ v 2 ≤ Real.cosh R} := by
    have hpoly : Continuous (fun v : Fin 3 → ℝ =>
        v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) :=
      (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).sub
        ((continuous_apply 2).pow 2)
    change IsClosed ({v : Fin 3 → ℝ |
        v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 = -1} ∩
      ({v : Fin 3 → ℝ | 1 ≤ v 2} ∩
        {v : Fin 3 → ℝ | v 2 ≤ Real.cosh R}))
    exact (isClosed_eq hpoly continuous_const).inter
      ((isClosed_le continuous_const (continuous_apply 2)).inter
        (isClosed_le (continuous_apply 2) continuous_const))

  have hbounded : Bornology.IsBounded {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 = -1 ∧
      1 ≤ v 2 ∧ v 2 ≤ Real.cosh R} := by
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.cosh R, ?_⟩
    intro v hv
    let q : Hyperboloid :=
      ⟨v, hv.1, lt_of_lt_of_le zero_lt_one hv.2.1⟩
    have hq : hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R :=
      (hyperboloidLengthDist_center_le_iff q R hR).mpr hv.2.2
    have hb := hyperboloidLengthDist_center_bounds q R hR hq
    have hsp : v 0 ^ 2 + v 1 ^ 2 ≤ Real.sinh R ^ 2 := hb.2.2
    have hx : v 0 ^ 2 ≤ Real.cosh R ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq R, sq_nonneg (v 1)]
    have hy : v 1 ^ 2 ≤ Real.cosh R ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq R, sq_nonneg (v 0)]
    have hxabs : |v 0| ≤ Real.cosh R := by
      apply (sq_le_sq₀ (abs_nonneg (v 0)) (Real.cosh_pos R).le).mp
      simpa only [sq_abs] using hx
    have hyabs : |v 1| ≤ Real.cosh R := by
      apply (sq_le_sq₀ (abs_nonneg (v 1)) (Real.cosh_pos R).le).mp
      simpa only [sq_abs] using hy
    have ht : 0 ≤ v 2 := le_trans zero_le_one hv.2.1
    apply (pi_norm_le_iff_of_nonneg (Real.cosh_pos R).le).mpr
    intro i
    fin_cases i
    · simpa [Real.norm_eq_abs] using hxabs
    · simpa [Real.norm_eq_abs] using hyabs
    · simpa [Real.norm_eq_abs, abs_of_nonneg ht] using hv.2.2

  have hproper : ProperSpace (Fin 3 → ℝ) := inferInstance
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩

/-- Every centered length-distance sublevel is compact in the original hyperboloid topology. Negative radii give the empty set; nonnegative radii are transferred from the ambient compact set. Textbook lines 121–122. -/
theorem isCompact_hyperboloidLengthDist_center_sublevel (R : ℝ) :
    IsCompact {q : Hyperboloid |
      hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} := by
  rcases lt_or_ge R 0 with hR | hR
  · rw [hyperboloidLengthDist_center_sublevel_neg R hR]
    exact isCompact_empty
  · have himage :
        (fun q : Hyperboloid => q.val) ''
          {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} =
        {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 = -1 ∧
      1 ≤ v 2 ∧ v 2 ≤ Real.cosh R} := by
      ext v
      constructor
      · rintro ⟨q, hq, rfl⟩
        have h := hyperboloidLengthDist_center_bounds q R hR hq
        exact ⟨q.property.1, h.1, h.2.1⟩
      · intro hv
        let q : Hyperboloid := ⟨v, hv.1, lt_of_lt_of_le zero_lt_one hv.2.1⟩
        refine ⟨q, ?_, rfl⟩
        exact (hyperboloidLengthDist_center_le_iff q R hR).mpr hv.2.2

    apply Subtype.isCompact_iff.mpr
    rw [himage]
    exact Hyperbolic.isCompact_hyperboloid_center_ambient R hR

/-- Every centered closed ball for the named hyperbolic length metric is compact. The original subspace compactness is transported through the same metric topology, for all real radii. Textbook lines 121–122. -/
theorem isCompact_hyperboloidLengthMetricSpace_center_closedBall (R : ℝ) :
    letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
    letI : PseudoMetricSpace Hyperboloid :=
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : PseudoEMetricSpace Hyperboloid :=
      @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : WeakPseudoEMetricSpace Hyperboloid :=
      @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
        (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
          hyperboloidLengthMetricSpace.toPseudoMetricSpace)
    IsCompact (Metric.closedBall (hyperboloidPolar 0 0) R) := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  have htop :
      hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology :=
    hyperboloidLengthMetricSpace_coherence.1
  have hOriginal :
      @IsCompact Hyperboloid originalTopology
        {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} :=
    Hyperbolic.isCompact_hyperboloidLengthDist_center_sublevel R
  have hSame :
      @IsCompact Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} := by
    rw [htop]
    exact hOriginal
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  have hball : Metric.closedBall (hyperboloidPolar 0 0) R =
      {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} := by
    ext q
    change dist q (hyperboloidPolar 0 0) ≤ R ↔
      hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R
    rw [dist_comm, hyperboloidLengthMetricSpace_coherence.2.2]
  rw [hball]
  exact hSame

end CenteredCompactBalls

section ProperLengthBalls

open Set

/-- Every closed ball for the hyperboloid length metric is compact. The chosen inverse center change transports the centered compact ball (G04.D, canonical line 122). -/
theorem isCompact_hyperboloidLengthMetricSpace_closedBall (p : Hyperboloid) (R : ℝ) :
    letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
    letI : PseudoMetricSpace Hyperboloid :=
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : PseudoEMetricSpace Hyperboloid :=
      @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : WeakPseudoEMetricSpace Hyperboloid :=
      @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
        (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
          hyperboloidLengthMetricSpace.toPseudoMetricSpace)
    IsCompact (Metric.closedBall p R) := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  have hc : centerHyperboloid p p = hyperboloidPolar 0 0 := by
    apply Subtype.ext
    exact (centerHyperboloid_properties p).2.2.2.2.1.trans
      (hyperboloidPolar_center_direction 0 p).1.symm
  have huc : ∀ q, uncenterHyperboloid p (centerHyperboloid p q) = q :=
    (centerHyperboloid_properties p).2.2.1
  have hcu : ∀ q, centerHyperboloid p (uncenterHyperboloid p q) = q :=
    (centerHyperboloid_properties p).2.2.2.1
  have hforward (q : Hyperboloid) :
      hyperboloidLengthDist (hyperboloidPolar 0 0) (centerHyperboloid p q) =
        hyperboloidLengthDist p q := by
    have h := hyperboloidLengthDist_center p q
    exact (congrArg ENNReal.toReal (le_antisymm h.1 h.2.1)).symm
  have hinverse (q : Hyperboloid) :
      hyperboloidLengthDist p (uncenterHyperboloid p q) =
        hyperboloidLengthDist (hyperboloidPolar 0 0) q := by
    have h := (hforward (uncenterHyperboloid p q)).symm
    simpa only [hcu] using h
  have hmap :
      centerHyperboloid p '' {q | hyperboloidLengthDist p q ≤ R} =
        {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      change hyperboloidLengthDist (hyperboloidPolar 0 0) (centerHyperboloid p x) ≤ R
      rw [hforward]
      exact hx
    · intro hq
      refine ⟨uncenterHyperboloid p q, ?_, hcu q⟩
      change hyperboloidLengthDist p (uncenterHyperboloid p q) ≤ R
      rw [hinverse]
      exact hq
  have hback :
      uncenterHyperboloid p ''
        {q | hyperboloidLengthDist (hyperboloidPolar 0 0) q ≤ R} =
        {q | hyperboloidLengthDist p q ≤ R} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      change hyperboloidLengthDist p (uncenterHyperboloid p x) ≤ R
      rw [hinverse]
      exact hx
    · intro hq
      refine ⟨centerHyperboloid p q, ?_, huc q⟩
      change hyperboloidLengthDist (hyperboloidPolar 0 0) (centerHyperboloid p q) ≤ R
      rw [hforward]
      exact hq
  have hOriginal :
      @IsCompact Hyperboloid originalTopology {q | hyperboloidLengthDist p q ≤ R} := by
    rw [← hback]
    exact (Hyperbolic.isCompact_hyperboloidLengthDist_center_sublevel R).image
      (contMDiff_uncenterHyperboloid p).continuous
  have htop :
      hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology := hyperboloidLengthMetricSpace_coherence.1
  have hSame :
      @IsCompact Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        {q | hyperboloidLengthDist p q ≤ R} := by
    rw [htop]
    exact hOriginal
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  have hball : Metric.closedBall p R = {q | hyperboloidLengthDist p q ≤ R} := by
    ext q
    change dist q p ≤ R ↔ hyperboloidLengthDist p q ≤ R
    rw [dist_comm, hyperboloidLengthMetricSpace_coherence.2.2]
  rw [hball]
  exact hSame

/-- The hyperboloid length metric is proper, packaged without a global instance (G04.D, canonical line 122). -/
theorem properSpace_hyperboloidLengthMetricSpace :
    letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
    letI : PseudoMetricSpace Hyperboloid :=
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : PseudoEMetricSpace Hyperboloid :=
      @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace
    letI : WeakPseudoEMetricSpace Hyperboloid :=
      @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
        (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
          hyperboloidLengthMetricSpace.toPseudoMetricSpace)
    ProperSpace Hyperboloid := by
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  exact ⟨fun p R => Hyperbolic.isCompact_hyperboloidLengthMetricSpace_closedBall p R⟩

/-- Every closed ball for the upper-half-plane length metric is compact by the actual inverse model map (G04.D, canonical line 122). -/
theorem isCompact_upperHalfPlaneLengthMetricSpace_closedBall
    (u : UpperHalfPlane) (R : ℝ) :
    letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
    IsCompact (Metric.closedBall u R) := by
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
      hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  have hTo := modelLengthMetric_isometries.1
  have hFrom := modelLengthMetric_isometries.2
  have hQ : IsCompact (Metric.closedBall (toHyperboloid u) R) :=
    Hyperbolic.isCompact_hyperboloidLengthMetricSpace_closedBall (toHyperboloid u) R
  have hback :
      fromHyperboloid '' Metric.closedBall (toHyperboloid u) R = Metric.closedBall u R := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      change dist (fromHyperboloid q) u ≤ R
      have hd := hFrom.dist_eq q (toHyperboloid u)
      rw [fromHyperboloid_toHyperboloid] at hd
      rw [hd]
      exact hq
    · intro hv
      refine ⟨toHyperboloid v, ?_, fromHyperboloid_toHyperboloid v⟩
      change dist (toHyperboloid v) (toHyperboloid u) ≤ R
      rw [hTo.dist_eq]
      exact hv
  rw [← hback]
  exact hQ.image hFrom.continuous

/-- The upper-half-plane length metric is proper, packaged without a global instance (G04.D, canonical line 122). -/
theorem properSpace_upperHalfPlaneLengthMetricSpace :
    letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
    ProperSpace UpperHalfPlane := by
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  exact ⟨fun u R => Hyperbolic.isCompact_upperHalfPlaneLengthMetricSpace_closedBall u R⟩

end ProperLengthBalls

section CompleteLengthMetrics

open Set Filter
open scoped Topology

/-- Every Cauchy sequence for the hyperboloid length metric converges inside the model, by a compact tail and the epsilon-half estimate (G04.E, canonical lines 123–125). -/
theorem cauchySeq_tendsto_hyperboloidLengthMetricSpace (x : ℕ → Hyperboloid) :
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  CauchySeq x → ∃ p : Hyperboloid, Tendsto x atTop (𝓝 p) := by
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  intro hx
  rcases Metric.cauchySeq_iff.1 hx 1 zero_lt_one with ⟨N, hN⟩
  let y : ℕ → Hyperboloid := fun n => x (N + n)
  have hy : ∀ n, y n ∈ Metric.closedBall (x N) 1 := by
    intro n
    change dist (x (N + n)) (x N) ≤ 1
    exact (hN (N + n) (Nat.le_add_right N n) N le_rfl).le
  -- Actual committed D compact-ball dependency.
  have hcompact : IsCompact (Metric.closedBall (x N) 1) :=
    Hyperbolic.isCompact_hyperboloidLengthMetricSpace_closedBall (x N) 1
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hy
  have hlim' : Tendsto (fun k => x (N + φ k)) atTop (𝓝 p) := by
    simpa only [Function.comp_def, y] using hlim
  have hshift : StrictMono (fun k => N + φ k) := by
    intro i j hij
    exact Nat.add_lt_add_left (hφ hij) N
  refine ⟨p, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  rcases Metric.cauchySeq_iff.1 hx (ε / 2) (half_pos hε) with ⟨cauchyIndex, hK⟩
  rcases Metric.tendsto_atTop.1 hlim' (ε / 2) (half_pos hε) with ⟨L, hL⟩
  let k := max cauchyIndex L
  have hkL : L ≤ k := le_max_right _ _
  have hkK : cauchyIndex ≤ k := le_max_left _ _
  have hKidx : cauchyIndex ≤ N + φ k :=
    hkK.trans ((hφ.id_le k).trans (Nat.le_add_left (φ k) N))
  have hsub : dist (x (N + φ k)) p < ε / 2 := hL k hkL
  refine ⟨cauchyIndex, ?_⟩
  intro n hn
  calc
    dist (x n) p ≤ dist (x n) (x (N + φ k)) + dist (x (N + φ k)) p :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hK n hn (N + φ k) hKidx) hsub
    _ = ε := add_halves ε

/-- The hyperboloid length metric is complete, packaged without a global instance (G04.E, canonical line 125). -/
theorem completeSpace_hyperboloidLengthMetricSpace :
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  CompleteSpace Hyperboloid := by
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact Metric.complete_of_cauchySeq_tendsto
    (fun x hx => Hyperbolic.cauchySeq_tendsto_hyperboloidLengthMetricSpace x hx)

/-- Every Cauchy sequence for the upper-half-plane length metric converges inside the model, by a compact tail and the epsilon-half estimate (G04.E, canonical lines 123–125). -/
theorem cauchySeq_tendsto_upperHalfPlaneLengthMetricSpace (x : ℕ → UpperHalfPlane) :
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  CauchySeq x → ∃ p : UpperHalfPlane, Tendsto x atTop (𝓝 p) := by
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  intro hx
  rcases Metric.cauchySeq_iff.1 hx 1 zero_lt_one with ⟨N, hN⟩
  let y : ℕ → UpperHalfPlane := fun n => x (N + n)
  have hy : ∀ n, y n ∈ Metric.closedBall (x N) 1 := by
    intro n
    change dist (x (N + n)) (x N) ≤ 1
    exact (hN (N + n) (Nat.le_add_right N n) N le_rfl).le
  -- Actual committed D compact-ball dependency.
  have hcompact : IsCompact (Metric.closedBall (x N) 1) :=
    Hyperbolic.isCompact_upperHalfPlaneLengthMetricSpace_closedBall (x N) 1
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hy
  have hlim' : Tendsto (fun k => x (N + φ k)) atTop (𝓝 p) := by
    simpa only [Function.comp_def, y] using hlim
  have hshift : StrictMono (fun k => N + φ k) := by
    intro i j hij
    exact Nat.add_lt_add_left (hφ hij) N
  refine ⟨p, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  rcases Metric.cauchySeq_iff.1 hx (ε / 2) (half_pos hε) with ⟨cauchyIndex, hK⟩
  rcases Metric.tendsto_atTop.1 hlim' (ε / 2) (half_pos hε) with ⟨L, hL⟩
  let k := max cauchyIndex L
  have hkL : L ≤ k := le_max_right _ _
  have hkK : cauchyIndex ≤ k := le_max_left _ _
  have hKidx : cauchyIndex ≤ N + φ k :=
    hkK.trans ((hφ.id_le k).trans (Nat.le_add_left (φ k) N))
  have hsub : dist (x (N + φ k)) p < ε / 2 := hL k hkL
  refine ⟨cauchyIndex, ?_⟩
  intro n hn
  calc
    dist (x n) p ≤ dist (x n) (x (N + φ k)) + dist (x (N + φ k)) p :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hK n hn (N + φ k) hKidx) hsub
    _ = ε := add_halves ε

/-- The upper-half-plane length metric is complete, packaged without a global instance (G04.E, canonical line 125). -/
theorem completeSpace_upperHalfPlaneLengthMetricSpace :
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  CompleteSpace UpperHalfPlane := by
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact Metric.complete_of_cauchySeq_tendsto
    (fun x hx => Hyperbolic.cauchySeq_tendsto_upperHalfPlaneLengthMetricSpace x hx)

end CompleteLengthMetrics

section IdealLengthEnds

open Set Filter
open scoped Topology OnePoint
universe u

/-- A nontrivial length-Cauchy filter in the upper half-plane cannot converge to a real ideal endpoint or infinity in OnePoint complex. The SAME complete metric supplies an interior limit; its original topology and Hausdorff uniqueness exclude the ideal limit (G04.F, textbook lines 125–126). -/
theorem upperHalfPlane_lengthCauchy_not_tendsto_ideal
    {ι : Type u} (l : Filter ι) [l.NeBot] (x : ι → UpperHalfPlane)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ S : Set ι, S ∈ l ∧
      ∀ i ∈ S, ∀ j ∈ S, (Manifold.piecewiseC1EDist upperHalfPlaneMetric (x i) (x j)).toReal < ε)
    (b : OnePoint ℂ)
    (hb : b = OnePoint.infty ∨ ∃ r : ℝ, b = ((r : ℂ) : OnePoint ℂ)) :
    ¬ Tendsto (fun i => ((x i : ℂ) : OnePoint ℂ)) l (𝓝 b) := by
  let originalTopology : TopologicalSpace UpperHalfPlane := inferInstance
  have htop :
      upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology := upperHalfPlaneLengthMetricSpace_coherence.1
  have hinc : Continuous (fun p : UpperHalfPlane => ((p : ℂ) : OnePoint ℂ)) :=
    OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  -- Actual committed E supplies completeness of this SAME uniformity.
  letI : CompleteSpace UpperHalfPlane := Hyperbolic.completeSpace_upperHalfPlaneLengthMetricSpace
  have hx : Cauchy (Filter.map x l) := Metric.cauchy_iff.2 (by
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    rcases hC ε hε with ⟨S, hS, hpair⟩
    refine ⟨x '' S, Filter.image_mem_map hS, ?_⟩
    rintro a ⟨i, hi, rfl⟩ b' ⟨j, hj, rfl⟩
    rw [upperHalfPlaneLengthMetricSpace_coherence.2.2]
    exact hpair i hi j hj)
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.1 hx
  have hpOriginal : Tendsto x l (@nhds UpperHalfPlane originalTopology p) := by
    change Tendsto x l
      (@nhds UpperHalfPlane
        upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace p) at hp
    rw [htop] at hp
    exact hp
  have hpAmbient : Tendsto (fun i => ((x i : ℂ) : OnePoint ℂ)) l
      (𝓝 ((p : ℂ) : OnePoint ℂ)) :=
    hinc.continuousAt.tendsto.comp hpOriginal
  intro hideal
  have heq : ((p : ℂ) : OnePoint ℂ) = b := tendsto_nhds_unique hpAmbient hideal
  rcases hb with hb | ⟨r, hb⟩
  · exact OnePoint.coe_ne_infty ((p) : ℂ) (heq.trans hb)
  · have hz : ((p) : ℂ) = (r : ℂ) := OnePoint.coe_injective (heq.trans hb)
    have him : (p).im = 0 := by
      simpa only [UpperHalfPlane.coe_im, Complex.ofReal_im] using congrArg Complex.im hz
    exact (ne_of_gt (p).im_pos) him

/-- A nontrivial upper-half-plane length-Cauchy filter is eventually contained in one compact closed unit length ball, in the original topology. This fixed compact tail rules out eventual escape from every compact set (G04.F, textbook lines 125–126). -/
theorem upperHalfPlane_lengthCauchy_compact_tail
    {ι : Type u} (l : Filter ι) [l.NeBot] (x : ι → UpperHalfPlane)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ S : Set ι, S ∈ l ∧
      ∀ i ∈ S, ∀ j ∈ S, (Manifold.piecewiseC1EDist upperHalfPlaneMetric (x i) (x j)).toReal < ε) :
    ∃ p : UpperHalfPlane, IsCompact {q : UpperHalfPlane | (Manifold.piecewiseC1EDist upperHalfPlaneMetric (q) (p)).toReal ≤ 1} ∧
      ∀ᶠ i in l, (Manifold.piecewiseC1EDist upperHalfPlaneMetric (x i) (p)).toReal ≤ 1 := by
  let originalTopology : TopologicalSpace UpperHalfPlane := inferInstance
  have htop :
      upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology := upperHalfPlaneLengthMetricSpace_coherence.1
  rcases hC 1 zero_lt_one with ⟨S, hS, hpair⟩
  obtain ⟨i, hi⟩ := Filter.nonempty_of_mem hS
  letI : MetricSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace
  letI : UniformSpace UpperHalfPlane := upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace UpperHalfPlane :=
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hball : Metric.closedBall (x i) 1 =
      {q : UpperHalfPlane | (Manifold.piecewiseC1EDist upperHalfPlaneMetric (q) (x i)).toReal ≤ 1} := by
    ext q
    change dist q (x i) ≤ 1 ↔ (Manifold.piecewiseC1EDist upperHalfPlaneMetric (q) (x i)).toReal ≤ 1
    rw [upperHalfPlaneLengthMetricSpace_coherence.2.2]
  -- Actual committed D supplies this SAME metric ball's compactness.
  have hc : IsCompact (Metric.closedBall (x i) 1) :=
    Hyperbolic.isCompact_upperHalfPlaneLengthMetricSpace_closedBall (x i) 1
  rw [hball] at hc
  change @IsCompact UpperHalfPlane
    upperHalfPlaneLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    {q : UpperHalfPlane | (Manifold.piecewiseC1EDist upperHalfPlaneMetric (q) (x i)).toReal ≤ 1} at hc
  rw [htop] at hc
  refine ⟨x i, hc, ?_⟩
  exact Filter.mem_of_superset hS (fun j hj => (hpair j hj i hi).le)

/-- A nontrivial hyperboloid length-Cauchy filter cannot converge to a real ideal endpoint or infinity under the actual inverse model inclusion into OnePoint complex. The SAME complete metric and original topology give the interior limit (G04.F, textbook lines 125–126). -/
theorem hyperboloid_lengthCauchy_not_tendsto_ideal
    {ι : Type u} (l : Filter ι) [l.NeBot] (x : ι → Hyperboloid)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ S : Set ι, S ∈ l ∧
      ∀ i ∈ S, ∀ j ∈ S, hyperboloidLengthDist (x i) (x j) < ε)
    (b : OnePoint ℂ)
    (hb : b = OnePoint.infty ∨ ∃ r : ℝ, b = ((r : ℂ) : OnePoint ℂ)) :
    ¬ Tendsto (fun i => ((fromHyperboloid (x i) : ℂ) : OnePoint ℂ)) l (𝓝 b) := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  have htop :
      hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology := hyperboloidLengthMetricSpace_coherence.1
  have hinc : Continuous (fun p : Hyperboloid => ((fromHyperboloid (p) : ℂ) : OnePoint ℂ)) :=
    OnePoint.continuous_coe.comp
      (UpperHalfPlane.continuous_coe.comp contMDiff_fromHyperboloid.continuous)
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  -- Actual committed E supplies completeness of this SAME uniformity.
  letI : CompleteSpace Hyperboloid := Hyperbolic.completeSpace_hyperboloidLengthMetricSpace
  have hx : Cauchy (Filter.map x l) := Metric.cauchy_iff.2 (by
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    rcases hC ε hε with ⟨S, hS, hpair⟩
    refine ⟨x '' S, Filter.image_mem_map hS, ?_⟩
    rintro a ⟨i, hi, rfl⟩ b' ⟨j, hj, rfl⟩
    rw [hyperboloidLengthMetricSpace_coherence.2.2]
    exact hpair i hi j hj)
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.1 hx
  have hpOriginal : Tendsto x l (@nhds Hyperboloid originalTopology p) := by
    change Tendsto x l
      (@nhds Hyperboloid
        hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace p) at hp
    rw [htop] at hp
    exact hp
  have hpAmbient : Tendsto (fun i => ((fromHyperboloid (x i) : ℂ) : OnePoint ℂ)) l
      (𝓝 ((fromHyperboloid (p) : ℂ) : OnePoint ℂ)) :=
    hinc.continuousAt.tendsto.comp hpOriginal
  intro hideal
  have heq : ((fromHyperboloid (p) : ℂ) : OnePoint ℂ) = b := tendsto_nhds_unique hpAmbient hideal
  rcases hb with hb | ⟨r, hb⟩
  · exact OnePoint.coe_ne_infty ((fromHyperboloid p) : ℂ) (heq.trans hb)
  · have hz : ((fromHyperboloid p) : ℂ) = (r : ℂ) := OnePoint.coe_injective (heq.trans hb)
    have him : (fromHyperboloid p).im = 0 := by
      simpa only [UpperHalfPlane.coe_im, Complex.ofReal_im] using congrArg Complex.im hz
    exact (ne_of_gt (fromHyperboloid p).im_pos) him

/-- A nontrivial hyperboloid length-Cauchy filter is eventually contained in one compact closed unit length ball, in the original topology. Compactness concerns this single fixed tail ball (G04.F, textbook lines 125–126). -/
theorem hyperboloid_lengthCauchy_compact_tail
    {ι : Type u} (l : Filter ι) [l.NeBot] (x : ι → Hyperboloid)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ S : Set ι, S ∈ l ∧
      ∀ i ∈ S, ∀ j ∈ S, hyperboloidLengthDist (x i) (x j) < ε) :
    ∃ p : Hyperboloid, IsCompact {q : Hyperboloid | hyperboloidLengthDist (q) (p) ≤ 1} ∧
      ∀ᶠ i in l, hyperboloidLengthDist (x i) (p) ≤ 1 := by
  let originalTopology : TopologicalSpace Hyperboloid := inferInstance
  have htop :
      hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        originalTopology := hyperboloidLengthMetricSpace_coherence.1
  rcases hC 1 zero_lt_one with ⟨S, hS, hpair⟩
  obtain ⟨i, hi⟩ := Filter.nonempty_of_mem hS
  letI : MetricSpace Hyperboloid := hyperboloidLengthMetricSpace
  letI : PseudoMetricSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace Hyperboloid :=
    @PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace
  letI : WeakPseudoEMetricSpace Hyperboloid :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace Hyperboloid
      (@PseudoMetricSpace.toPseudoEMetricSpace Hyperboloid hyperboloidLengthMetricSpace.toPseudoMetricSpace)
  letI : UniformSpace Hyperboloid := hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace Hyperboloid :=
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hball : Metric.closedBall (x i) 1 =
      {q : Hyperboloid | hyperboloidLengthDist (q) (x i) ≤ 1} := by
    ext q
    change dist q (x i) ≤ 1 ↔ hyperboloidLengthDist (q) (x i) ≤ 1
    rw [hyperboloidLengthMetricSpace_coherence.2.2]
  -- Actual committed D supplies this SAME metric ball's compactness.
  have hc : IsCompact (Metric.closedBall (x i) 1) :=
    Hyperbolic.isCompact_hyperboloidLengthMetricSpace_closedBall (x i) 1
  rw [hball] at hc
  change @IsCompact Hyperboloid
    hyperboloidLengthMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    {q : Hyperboloid | hyperboloidLengthDist (q) (x i) ≤ 1} at hc
  rw [htop] at hc
  refine ⟨x i, hc, ?_⟩
  exact Filter.mem_of_superset hS (fun j hj => (hpair j hj i hi).le)

end IdealLengthEnds

section FiniteLengthTails

open Manifold Set Filter MeasureTheory
open scoped Bundle Topology ENNReal OnePoint

/-- A locally piecewise continuously differentiable upper-half-plane curve of finite original
Riemannian speed length has a Cauchy tail along its finite right endpoint filter.
The proof bounds every pair on one tail by the same small nonnegative speed integral.
Textbook source: ideal-reflection G04.F, canonical lines 125–126. -/
theorem upperHalfPlane_finite_length_tail_cauchy
    (a b : ℝ) (hab : a < b) (γ : ℝ → UpperHalfPlane)
    (hlocal : ∀ s t : ℝ, a < s → s ≤ t → t < b →
      ∃ n : ℕ, ∃ cut : Fin (n + 1) → ℝ,
        IsPiecewiseC1On 𝓘(ℝ, ℂ) γ s t n cut)
    (hLength :
      letI : Bundle.RiemannianBundle
          (fun p : UpperHalfPlane => TangentSpace 𝓘(ℝ, ℂ) p) :=
        ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
      pathELength 𝓘(ℝ, ℂ) γ a b < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ S : Set ℝ, S ∈ nhdsWithin b (Ioo a b) ∧
        ∀ s ∈ S, ∀ t ∈ S, (piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t)).toReal < ε := by
  letI : Bundle.RiemannianBundle
      (fun p : UpperHalfPlane => TangentSpace 𝓘(ℝ, ℂ) p) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  let L : Filter ℝ := nhdsWithin b (Ioo a b)
  letI : L.NeBot := right_nhdsWithin_Ioo_neBot hab
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  let v : ℝ → ℝ≥0∞ :=
    fun r => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ r (1 : ℝ)‖ₑ
  let W : ℝ → ℝ≥0∞ := fun y => ∫⁻ r in Ioo y b, v r ∂μ
  have hfinite : (∫⁻ r, v r ∂μ) ≠ ⊤ := by
    change (∫⁻ r in Ioo a b,
      ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ r (1 : ℝ)‖ₑ) ≠ ⊤
    have h := ne_of_lt hLength
    rw [pathELength_eq_lintegral_mfderiv_Ioo] at h
    exact h
  have hId : Tendsto (fun y : ℝ => y) L (𝓝 b) :=
    (continuous_id.tendsto b).mono_left nhdsWithin_le_nhds
  have hDiff : Tendsto (fun y : ℝ => b - y) L (𝓝 (b - b)) :=
    tendsto_const_nhds.sub hId
  have hVol : Tendsto (fun y : ℝ => volume (Ioo y b)) L (𝓝 0) := by
    simpa only [Real.volume_Ioo, sub_self, ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal hDiff)
  have hμ : Tendsto (μ ∘ (fun y : ℝ => Ioo y b)) L (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVol
    · intro y
      exact zero_le
    · intro y
      exact Measure.restrict_apply_le (Ioo a b) (Ioo y b)
  have hW : Tendsto W L (𝓝 0) :=
    tendsto_setLIntegral_zero (μ := μ) (f := v) hfinite hμ
  intro ε hε
  have hsmall : ∀ᶠ y in L, W y < ENNReal.ofReal ε :=
    (tendsto_order.1 hW).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hOriginal : ∀ᶠ y in L, y ∈ Ioo a b := self_mem_nhdsWithin
  obtain ⟨c, hcSmall, hc⟩ := (hsmall.and hOriginal).exists
  have hS : Ioo c b ∈ L := by
    change Ioo c b ∈ nhdsWithin b (Ioo a b)
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact Ioo_mem_nhdsLT hc.2
  have hordered (s t : ℝ) (hs : s ∈ Ioo c b) (ht : t ∈ Ioo c b)
      (hst : s ≤ t) : (piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t)).toReal < ε := by
    have has : a < s := hc.1.trans hs.1
    obtain ⟨n, cut, hγ⟩ := hlocal s t has hst ht.2
    let η : PiecewiseC1CurveOn 𝓘(ℝ, ℂ) s t n cut (γ s) (γ t) :=
      ⟨γ, hγ, rfl, rfl⟩
    have he :
        piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t) ≤
          ENNReal.ofReal (piecewiseC1Length upperHalfPlaneMetric γ cut) :=
      (piecewiseC1EDist_finite_of_curve upperHalfPlaneMetric η).1
    rcases hγ.speed_length upperHalfPlaneMetric with
      ⟨hpi, hpii, hm, hint, hreal, hset, hnonneg, hepi, hfpi,
        hsum, hext, hpath, hpieceFinite⟩
    have heLength :
        piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t) ≤
          pathELength 𝓘(ℝ, ℂ) γ s t :=
      he.trans_eq hpath.symm
    have hsubOriginal : Icc s t ⊆ Ioo a b := by
      intro r hr
      exact ⟨has.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hsubTail : Icc s t ⊆ Ioo c b := by
      intro r hr
      exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hμInterval :
        μ.restrict (Icc s t) = volume.restrict (Icc s t) :=
      Measure.restrict_restrict_of_subset hsubOriginal
    have hInterval :
        pathELength 𝓘(ℝ, ℂ) γ s t = ∫⁻ r in Icc s t, v r ∂μ := by
      rw [pathELength_eq_lintegral_mfderiv_Icc]
      change (∫⁻ r, v r ∂volume.restrict (Icc s t)) =
        ∫⁻ r, v r ∂μ.restrict (Icc s t)
      rw [hμInterval]
    have hIntervalTail : pathELength 𝓘(ℝ, ℂ) γ s t ≤ W c := by
      rw [hInterval]
      exact lintegral_mono_set hsubTail
    have hExtended :
        piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t) < ENNReal.ofReal ε :=
      (heLength.trans hIntervalTail).trans_lt hcSmall
    exact ENNReal.toReal_lt_of_lt_ofReal hExtended
  refine ⟨Ioo c b, hS, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s t hs ht hst
  · have hsym :
        piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t) =
          piecewiseC1EDist upperHalfPlaneMetric (γ t) (γ s) :=
      (piecewiseC1EDist_eq_riemannianEDist upperHalfPlaneMetric (γ s) (γ t)).trans
        (riemannianEDist_comm.trans
          (piecewiseC1EDist_eq_riemannianEDist upperHalfPlaneMetric (γ t) (γ s)).symm)
    change (piecewiseC1EDist upperHalfPlaneMetric (γ s) (γ t)).toReal < ε
    rw [hsym]
    exact hordered t s ht hs hts

/-- A locally piecewise continuously differentiable hyperboloid curve of finite original
Riemannian speed length has a Cauchy tail for the same length distance.
Local finite partitions may vary with the compact interval; no endpoint extension is assumed.
Textbook source: ideal-reflection G04.F, canonical lines 125–126. -/
theorem hyperboloid_finite_length_tail_cauchy
    (a b : ℝ) (hab : a < b) (γ : ℝ → Hyperboloid)
    (hlocal : ∀ s t : ℝ, a < s → s ≤ t → t < b →
      ∃ n : ℕ, ∃ cut : Fin (n + 1) → ℝ,
        IsPiecewiseC1On 𝓘(ℝ, ℂ) γ s t n cut)
    (hLength :
      letI : Bundle.RiemannianBundle
          (fun p : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) p) :=
        ⟨hyperboloidMetric.toRiemannianMetric⟩
      pathELength 𝓘(ℝ, ℂ) γ a b < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ S : Set ℝ, S ∈ nhdsWithin b (Ioo a b) ∧
        ∀ s ∈ S, ∀ t ∈ S, hyperboloidLengthDist (γ s) (γ t) < ε := by
  letI : Bundle.RiemannianBundle
      (fun p : Hyperboloid => TangentSpace 𝓘(ℝ, ℂ) p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  let L : Filter ℝ := nhdsWithin b (Ioo a b)
  letI : L.NeBot := right_nhdsWithin_Ioo_neBot hab
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  let v : ℝ → ℝ≥0∞ :=
    fun r => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ r (1 : ℝ)‖ₑ
  let W : ℝ → ℝ≥0∞ := fun y => ∫⁻ r in Ioo y b, v r ∂μ
  have hfinite : (∫⁻ r, v r ∂μ) ≠ ⊤ := by
    change (∫⁻ r in Ioo a b,
      ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ r (1 : ℝ)‖ₑ) ≠ ⊤
    have h := ne_of_lt hLength
    rw [pathELength_eq_lintegral_mfderiv_Ioo] at h
    exact h
  have hId : Tendsto (fun y : ℝ => y) L (𝓝 b) :=
    (continuous_id.tendsto b).mono_left nhdsWithin_le_nhds
  have hDiff : Tendsto (fun y : ℝ => b - y) L (𝓝 (b - b)) :=
    tendsto_const_nhds.sub hId
  have hVol : Tendsto (fun y : ℝ => volume (Ioo y b)) L (𝓝 0) := by
    simpa only [Real.volume_Ioo, sub_self, ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal hDiff)
  have hμ : Tendsto (μ ∘ (fun y : ℝ => Ioo y b)) L (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVol
    · intro y
      exact zero_le
    · intro y
      exact Measure.restrict_apply_le (Ioo a b) (Ioo y b)
  have hW : Tendsto W L (𝓝 0) :=
    tendsto_setLIntegral_zero (μ := μ) (f := v) hfinite hμ
  intro ε hε
  have hsmall : ∀ᶠ y in L, W y < ENNReal.ofReal ε :=
    (tendsto_order.1 hW).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hOriginal : ∀ᶠ y in L, y ∈ Ioo a b := self_mem_nhdsWithin
  obtain ⟨c, hcSmall, hc⟩ := (hsmall.and hOriginal).exists
  have hS : Ioo c b ∈ L := by
    change Ioo c b ∈ nhdsWithin b (Ioo a b)
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact Ioo_mem_nhdsLT hc.2
  have hordered (s t : ℝ) (hs : s ∈ Ioo c b) (ht : t ∈ Ioo c b)
      (hst : s ≤ t) : hyperboloidLengthDist (γ s) (γ t) < ε := by
    have has : a < s := hc.1.trans hs.1
    obtain ⟨n, cut, hγ⟩ := hlocal s t has hst ht.2
    let η : PiecewiseC1CurveOn 𝓘(ℝ, ℂ) s t n cut (γ s) (γ t) :=
      ⟨γ, hγ, rfl, rfl⟩
    have he :
        piecewiseC1EDist hyperboloidMetric (γ s) (γ t) ≤
          ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ cut) :=
      (piecewiseC1EDist_finite_of_curve hyperboloidMetric η).1
    rcases hγ.speed_length hyperboloidMetric with
      ⟨hpi, hpii, hm, hint, hreal, hset, hnonneg, hepi, hfpi,
        hsum, hext, hpath, hpieceFinite⟩
    have heLength :
        piecewiseC1EDist hyperboloidMetric (γ s) (γ t) ≤
          pathELength 𝓘(ℝ, ℂ) γ s t :=
      he.trans_eq hpath.symm
    have hsubOriginal : Icc s t ⊆ Ioo a b := by
      intro r hr
      exact ⟨has.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hsubTail : Icc s t ⊆ Ioo c b := by
      intro r hr
      exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hμInterval :
        μ.restrict (Icc s t) = volume.restrict (Icc s t) :=
      Measure.restrict_restrict_of_subset hsubOriginal
    have hInterval :
        pathELength 𝓘(ℝ, ℂ) γ s t = ∫⁻ r in Icc s t, v r ∂μ := by
      rw [pathELength_eq_lintegral_mfderiv_Icc]
      change (∫⁻ r, v r ∂volume.restrict (Icc s t)) =
        ∫⁻ r, v r ∂μ.restrict (Icc s t)
      rw [hμInterval]
    have hIntervalTail : pathELength 𝓘(ℝ, ℂ) γ s t ≤ W c := by
      rw [hInterval]
      exact lintegral_mono_set hsubTail
    have hExtended :
        piecewiseC1EDist hyperboloidMetric (γ s) (γ t) < ENNReal.ofReal ε :=
      (heLength.trans hIntervalTail).trans_lt hcSmall
    change (piecewiseC1EDist hyperboloidMetric (γ s) (γ t)).toReal < ε
    exact ENNReal.toReal_lt_of_lt_ofReal hExtended
  refine ⟨Ioo c b, hS, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s t hs ht hst
  · have hsym :
        piecewiseC1EDist hyperboloidMetric (γ s) (γ t) =
          piecewiseC1EDist hyperboloidMetric (γ t) (γ s) :=
      (piecewiseC1EDist_eq_riemannianEDist hyperboloidMetric (γ s) (γ t)).trans
        (riemannianEDist_comm.trans
          (piecewiseC1EDist_eq_riemannianEDist hyperboloidMetric (γ t) (γ s)).symm)
    change (piecewiseC1EDist hyperboloidMetric (γ s) (γ t)).toReal < ε
    rw [hsym]
    exact hordered t s ht hs hts

end FiniteLengthTails


/-! ## Ambient Lorentz reflection

Textbook source: G06 R01/R02, literal specialization of the generic real
bilinear reflection. These are ambient identities only; upper-sheet, metric,
side and polar geometry remain separate results.
-/

/-- R01: forget continuity in both slots of the literal Lorentz form. -/
def lorentzBilinForm : LinearMap.BilinForm ℝ (Fin 3 → ℝ) :=
  (ContinuousLinearMap.coeLM ℝ).comp Hyperbolic.lorentzBilinear.toLinearMap

/-- R01: the algebraic form evaluates as the original continuous form. -/
theorem lorentzBilinForm_apply (v w : Fin 3 → ℝ) :
    lorentzBilinForm v w = Hyperbolic.lorentzBilinear v w := rfl

/-- R01: the literal Lorentz form is symmetric. -/
theorem lorentzBilinForm_symm (v w : Fin 3 → ℝ) :
    lorentzBilinForm v w = lorentzBilinForm w v :=
  Hyperbolic.lorentzBilinear_symm v w

/-- R01: the Lorentz reflection is the generic unit-normal reflection. -/
def lorentzReflection (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.BilinForm.unitNormalReflection lorentzBilinForm n
    (by change Hyperbolic.lorentzBilinear n n = 1; exact hn)

/-- R01: the literal second-slot reflection formula. -/
theorem lorentzReflection_apply (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) (v : Fin 3 → ℝ) :
    lorentzReflection n hn v = v - (2 * Hyperbolic.lorentzBilinear v n) • n :=
  LinearMap.BilinForm.unitNormalReflection_apply lorentzBilinForm lorentzBilinForm_symm n hn v

/-- R01: the ambient Lorentz pairing is preserved. -/
theorem lorentzReflection_preserves (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) (v w : Fin 3 → ℝ) :
    Hyperbolic.lorentzBilinear (lorentzReflection n hn v) (lorentzReflection n hn w) =
      Hyperbolic.lorentzBilinear v w :=
  LinearMap.BilinForm.unitNormalReflection_preserves lorentzBilinForm lorentzBilinForm_symm n hn v w

/-- R02: the literal normal coordinate is negated. -/
theorem lorentzReflection_normal (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) (v : Fin 3 → ℝ) :
    Hyperbolic.lorentzBilinear (lorentzReflection n hn v) n =
      -Hyperbolic.lorentzBilinear v n :=
  LinearMap.BilinForm.unitNormalReflection_normal lorentzBilinForm lorentzBilinForm_symm n hn v

/-- R02: the literal ambient reflection is involutive. -/
theorem lorentzReflection_involutive (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) :
    Function.Involutive (lorentzReflection n hn) :=
  LinearMap.BilinForm.unitNormalReflection_involutive lorentzBilinForm n hn

/-- R02: the literal inverse equals the reflection. -/
theorem lorentzReflection_symm (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) :
    (lorentzReflection n hn).symm = lorentzReflection n hn :=
  LinearMap.BilinForm.unitNormalReflection_symm lorentzBilinForm n hn

/-- R02: the ambient fixed set is exactly the Lorentz perpendicular kernel. -/
theorem lorentzReflection_fixed_iff (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) (v : Fin 3 → ℝ) :
    lorentzReflection n hn v = v ↔ Hyperbolic.lorentzBilinear v n = 0 :=
  LinearMap.BilinForm.unitNormalReflection_fixed_iff lorentzBilinForm lorentzBilinForm_symm n hn v

/-- R02: the unit normal is reversed. -/
theorem lorentzReflection_self (n : Fin 3 → ℝ)
    (hn : Hyperbolic.lorentzBilinear n n = 1) :
    lorentzReflection n hn n = -n :=
  LinearMap.BilinForm.unitNormalReflection_self lorentzBilinForm n hn

/-- Project the vertical timelike vector onto the perpendicular of the prescribed normal. -/
def lorentzAxisProjection (n : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, 0, 1] - lorentzBilinear ![0, 0, 1] n • n

/-- For a unit spacelike normal, the vertical projection is perpendicular with negative square and nonzero time coordinate. -/
theorem lorentzAxisProjection_spec (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  n ≠ 0 ∧ (lorentzFunctional n).toLinearMap ≠ 0 ∧
  lorentzBilinear (lorentzAxisProjection n) n = 0 ∧
  lorentzBilinear (lorentzAxisProjection n) (lorentzAxisProjection n) =
    -1 - (lorentzBilinear ![0, 0, 1] n)^2 ∧
  lorentzAxisProjection n 2 ≠ 0 := by
  have hne : n ≠ 0 := by
    intro h
    subst n
    simpa using hn
  have hfn : (lorentzFunctional n).toLinearMap ≠ 0 := by
    intro h
    have he := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => f n) h
    have hval : lorentzFunctional n n = 1 := by
      rw [← lorentzBilinear_eq_functional]
      exact hn
    change lorentzFunctional n n = 0 at he
    linarith
  have horth : lorentzBilinear (lorentzAxisProjection n) n = 0 := by
    simp only [lorentzAxisProjection, map_sub, map_smul,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hn]
    ring
  have hsq : lorentzBilinear (lorentzAxisProjection n) (lorentzAxisProjection n) =
      -1 - (lorentzBilinear ![0, 0, 1] n)^2 := by
    simp only [lorentzAxisProjection, map_sub, map_smul,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [lorentzBilinear_symm n ![0, 0, 1], hn]
    have hvertical : lorentzBilinear ![0, 0, 1] ![0, 0, 1] = -1 := by
      change (0 : ℝ) * 0 + 0 * 0 - 1 * 1 = -1
      norm_num
    rw [hvertical]
    ring
  refine ⟨hne, hfn, horth, hsq, ?_⟩
  intro ht
  have hh := hsq
  simp only [lorentzBilinear_apply] at hh
  rw [ht] at hh
  nlinarith [sq_nonneg (lorentzAxisProjection n 0),
    sq_nonneg (lorentzAxisProjection n 1), sq_nonneg (lorentzBilinear ![0, 0, 1] n)]

/-- Choose the positive-time sign of the projected vector and normalize its negative square. -/
def lorentzAxisPointCoords (n : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sqrt (1 + (lorentzBilinear ![0, 0, 1] n)^2))⁻¹ •
    (if 0 < lorentzAxisProjection n 2 then lorentzAxisProjection n
      else -lorentzAxisProjection n)

/-- The normalized signed projection is an upper-sheet point perpendicular to the prescribed normal. -/
theorem lorentzAxisPointCoords_spec (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  ((lorentzAxisPointCoords n 0)^2 + (lorentzAxisPointCoords n 1)^2 -
    (lorentzAxisPointCoords n 2)^2 = -1 ∧ 0 < lorentzAxisPointCoords n 2) ∧
  lorentzBilinear (lorentzAxisPointCoords n) n = 0 := by
  obtain ⟨_, _, horth, hsq, ht⟩ := lorentzAxisProjection_spec n hn
  let w := lorentzAxisProjection n
  let v : Fin 3 → ℝ := if 0 < w 2 then w else -w
  let r := Real.sqrt (1 + (lorentzBilinear ![0, 0, 1] n)^2)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hrsq : r^2 = 1 + (lorentzBilinear ![0, 0, 1] n)^2 :=
    Real.sq_sqrt (by positivity)
  have hvT : 0 < v 2 := by
    dsimp [v]
    split_ifs with h
    · exact h
    · change 0 < -(w 2)
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) ht)
  have hvQ : lorentzBilinear v v = lorentzBilinear w w := by
    dsimp [v]
    split_ifs
    · rfl
    · simp only [lorentzBilinear_apply, Pi.neg_apply, neg_mul_neg]
  have hvn : lorentzBilinear v n = 0 := by
    dsimp [v]
    split_ifs
    · exact horth
    · simpa using congrArg Neg.neg horth
  have hpQ : lorentzBilinear (r⁻¹ • v) (r⁻¹ • v) = -1 := by
    have he : lorentzBilinear (r⁻¹ • v) (r⁻¹ • v) =
        r⁻¹ * r⁻¹ * lorentzBilinear v v := by
      simp only [lorentzBilinear_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, hvQ]
    have hww : lorentzBilinear w w = -(r^2) := by
      dsimp [w]
      rw [hsq, hrsq]
      ring
    rw [hww]
    field_simp [hrne]
    <;> ring
  have hpT : 0 < (r⁻¹ • v) 2 := mul_pos (inv_pos.mpr hrpos) hvT
  refine ⟨?_, ?_⟩
  · change (((r⁻¹ • v) 0)^2 + ((r⁻¹ • v) 1)^2 -
        ((r⁻¹ • v) 2)^2 = -1 ∧ 0 < (r⁻¹ • v) 2)
    simpa only [lorentzBilinear_apply, pow_two] using And.intro hpQ hpT
  · change lorentzBilinear (r⁻¹ • v) n = 0
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hvn, mul_zero]

/-- The explicit upper-sheet point on the axis of a prescribed unit normal. -/
def lorentzAxisPoint (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) : Hyperboloid :=
  ⟨lorentzAxisPointCoords n, (lorentzAxisPointCoords_spec n hn).1⟩

/-- Remove the normal component of a vector and normalize the remainder. -/
def lorentzAxisDirectionCoords (n z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let u := z - lorentzBilinear z n • n
  (Real.sqrt (lorentzBilinear u u))⁻¹ • u

/-- An independent tangent vector has a nonzero positive-square remainder perpendicular to both the point and normal. -/
theorem lorentzAxisDirectionRemainder_spec (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (hpn : lorentzBilinear p.val n = 0) (z : Fin 3 → ℝ)
    (hz : z ∈ (lorentzFunctional p.val).ker)
    (hznot : z ∉ Submodule.span ℝ ({n} : Set (Fin 3 → ℝ))) :
  let u := z - lorentzBilinear z n • n
  u ≠ 0 ∧ lorentzBilinear u p.val = 0 ∧
    lorentzBilinear u n = 0 ∧ 0 < lorentzBilinear u u := by
  let u := z - lorentzBilinear z n • n
  have hune : u ≠ 0 := by
    intro hu
    apply hznot
    have he : z = lorentzBilinear z n • n := sub_eq_zero.mp hu
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hzp : lorentzBilinear z p.val = 0 := by
    rw [lorentzBilinear_symm, lorentzBilinear_eq_functional]
    exact hz
  have hnp : lorentzBilinear n p.val = 0 :=
    (lorentzBilinear_symm n p.val).trans hpn
  have hup : lorentzBilinear u p.val = 0 := by
    simp only [u, map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hzp, hnp, mul_zero, sub_zero]
  have hun : lorentzBilinear u n = 0 := by
    simp only [u, map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hn, mul_one, sub_self]
  exact ⟨hune, hup, hun,
    lorentzKer_quadratic_pos p u ((lorentzBilinear_symm p.val u).trans hup) hune⟩

/-- The normalized tangent remainder is unit and perpendicular to the point and prescribed normal. -/
theorem lorentzAxisDirectionCoords_spec (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (hpn : lorentzBilinear p.val n = 0) (z : Fin 3 → ℝ)
    (hz : z ∈ (lorentzFunctional p.val).ker)
    (hznot : z ∉ Submodule.span ℝ ({n} : Set (Fin 3 → ℝ))) :
  lorentzBilinear (lorentzAxisDirectionCoords n z) p.val = 0 ∧
  lorentzBilinear (lorentzAxisDirectionCoords n z) n = 0 ∧
  lorentzBilinear (lorentzAxisDirectionCoords n z)
    (lorentzAxisDirectionCoords n z) = 1 := by
  obtain ⟨_, hup, hun, huq⟩ :=
    lorentzAxisDirectionRemainder_spec n hn p hpn z hz hznot
  let u := z - lorentzBilinear z n • n
  let r := Real.sqrt (lorentzBilinear u u)
  change lorentzBilinear u p.val = 0 at hup
  change lorentzBilinear u n = 0 at hun
  have hrpos : 0 < r := Real.sqrt_pos.mpr huq
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hrsq : r^2 = lorentzBilinear u u := Real.sq_sqrt huq.le
  change lorentzBilinear (r⁻¹ • u) p.val = 0 ∧
    lorentzBilinear (r⁻¹ • u) n = 0 ∧
    lorentzBilinear (r⁻¹ • u) (r⁻¹ • u) = 1
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hup, mul_zero]
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hun, mul_zero]
  · have he : lorentzBilinear (r⁻¹ • u) (r⁻¹ • u) =
        r⁻¹ * r⁻¹ * lorentzBilinear u u := by
      simp only [lorentzBilinear_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, ← hrsq]
    field_simp [hrne]

/-- At any point perpendicular to a unit normal, choose an independent tangent vector and normalize its remainder. -/
theorem exists_lorentzAxisDirection (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (hpn : lorentzBilinear p.val n = 0) :
  ∃ z : Fin 3 → ℝ,
    z ∈ (lorentzFunctional p.val).ker ∧
    z ∉ Submodule.span ℝ ({n} : Set (Fin 3 → ℝ)) ∧
    lorentzBilinear (lorentzAxisDirectionCoords n z) p.val = 0 ∧
    lorentzBilinear (lorentzAxisDirectionCoords n z) n = 0 ∧
    lorentzBilinear (lorentzAxisDirectionCoords n z)
      (lorentzAxisDirectionCoords n z) = 1 := by
  have hne := (lorentzAxisProjection_spec n hn).1
  have hle : Submodule.span ℝ ({n} : Set (Fin 3 → ℝ)) ≤
      (lorentzFunctional p.val).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x = n := by simpa using hx
    subst x
    change lorentzFunctional p.val n = 0
    rw [← lorentzBilinear_eq_functional]
    exact hpn
  have hlt : Submodule.span ℝ ({n} : Set (Fin 3 → ℝ)) <
      (lorentzFunctional p.val).ker := by
    apply Submodule.lt_of_le_of_finrank_lt_finrank hle
    rw [finrank_span_singleton hne, finrank_lorentzKer p]
    decide
  obtain ⟨z, hz, hznot⟩ := SetLike.exists_of_lt hlt
  exact ⟨z, hz, hznot, lorentzAxisDirectionCoords_spec n hn p hpn z hz hznot⟩

/-- The constructed point and a perpendicular unit tangent span exactly the normal kernel. -/
theorem lorentzAxis_span_ker (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (hpn : lorentzBilinear p.val n = 0) (e : Fin 3 → ℝ)
    (hep : lorentzBilinear e p.val = 0)
    (hen : lorentzBilinear e n = 0) (hee : lorentzBilinear e e = 1) :
  Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)) =
    (lorentzFunctional n).ker := by
  have hdim : Module.finrank ℝ (lorentzFunctional n).ker = 2 := by
    have h : Module.finrank ℝ (lorentzFunctional n).ker + 1 = 3 := by
      simpa using Module.Dual.finrank_ker_add_one_of_ne_zero
        (lorentzAxisProjection_spec n hn).2.1
    omega
  have hle : Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)) ≤
      (lorentzFunctional n).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    change lorentzFunctional n x = 0
    rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact hpn
    · have he : x = e := by simpa using hx
      subst x
      exact hen
  exact Submodule.eq_of_le_of_finrank_eq hle
    ((hyperboloidGeodesic_plane p e hep hee).2.1.trans hdim.symm)

/-- The graph coordinates of the positive Lorentz sheet over the real plane.
Textbook G06 S01.connected (lines 80–84): the explicit square-root graph. -/
def hyperboloidGraphCoords (xy : ℝ × ℝ) : Fin 3 → ℝ :=
  ![xy.1, xy.2, Real.sqrt (1 + xy.1^2 + xy.2^2)]

/-- The square-root graph satisfies the hyperboloid equation and has positive time.
Textbook G06 S01.connected: positivity of the radicand and its square-root square. -/
theorem hyperboloidGraphCoords_mem (xy : ℝ × ℝ) :
  (hyperboloidGraphCoords xy 0)^2 + (hyperboloidGraphCoords xy 1)^2 -
    (hyperboloidGraphCoords xy 2)^2 = -1 ∧
  0 < hyperboloidGraphCoords xy 2 := by
  have hpos : 0 < 1 + xy.1^2 + xy.2^2 := by positivity
  change xy.1^2 + xy.2^2 - (Real.sqrt (1 + xy.1^2 + xy.2^2))^2 = -1 ∧
    0 < Real.sqrt (1 + xy.1^2 + xy.2^2)
  constructor
  · rw [Real.sq_sqrt hpos.le]
    ring
  · exact Real.sqrt_pos.mpr hpos

/-- The explicit graph parametrization into the actual positive-sheet subtype.
Textbook G06 S01.connected: the continuous graph map from the real plane. -/
def hyperboloidGraph (xy : ℝ × ℝ) : Hyperboloid :=
  ⟨hyperboloidGraphCoords xy, hyperboloidGraphCoords_mem xy⟩

/-- The inverse graph coordinates are the first two ambient coordinates.
Textbook G06 S01.connected: the ordinary coordinate-projection inverse. -/
def hyperboloidGraphProjection (p : Hyperboloid) : ℝ × ℝ :=
  (p.val 0, p.val 1)

/-- Every positive-sheet point is recovered from its first two coordinates.
Textbook G06 S01.connected: the sheet equation and positive time determine the square root. -/
theorem hyperboloidGraph_right_inv (p : Hyperboloid) :
  hyperboloidGraph (hyperboloidGraphProjection p) = p := by
  apply Subtype.ext
  funext i
  fin_cases i
  · rfl
  · rfl
  · change Real.sqrt (1 + (p.val 0)^2 + (p.val 1)^2) = p.val 2
    have heq : 1 + (p.val 0)^2 + (p.val 1)^2 = (p.val 2)^2 := by
      nlinarith [p.property.1]
    rw [heq, Real.sqrt_sq p.property.2.le]

/-- The square-root graph is continuous for the ordinary product and subtype topologies.
Textbook G06 S01.connected: coordinatewise continuity followed by subtype continuity. -/
theorem continuous_hyperboloidGraph : Continuous hyperboloidGraph := by
  have hc : Continuous hyperboloidGraphCoords := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
    · exact ((continuous_const.add (continuous_fst.pow 2)).add
        (continuous_snd.pow 2)).sqrt
  exact hc.subtype_mk hyperboloidGraphCoords_mem

/-- The explicit graph and coordinate projections identify the plane with the positive sheet.
Textbook G06 S01.connected: both inverse maps are continuous in ordinary topology. -/
def hyperboloidGraphHomeomorph : (ℝ × ℝ) ≃ₜ Hyperboloid where
  toFun := hyperboloidGraph
  invFun := hyperboloidGraphProjection
  left_inv := fun xy => by cases xy; rfl
  right_inv := hyperboloidGraph_right_inv
  continuous_toFun := continuous_hyperboloidGraph
  continuous_invFun :=
    ((continuous_apply 0).comp continuous_subtype_val).prodMk
      ((continuous_apply 1).comp continuous_subtype_val)

/-- The positive sheet is connected as the continuous graph image of the real plane.
Textbook G06 S01.connected: real straight-segment paths, product paths, and connected image.
This theorem does not install a global connectedness instance. -/
theorem connectedSpace_hyperboloidGraph : ConnectedSpace Hyperboloid := by
  letI : PathConnectedSpace ℝ := Real.instPathConnectedSpace
  letI : PathConnectedSpace (ℝ × ℝ) := Prod.instPathConnectedSpace
  letI : ConnectedSpace (ℝ × ℝ) := PathConnectedSpace.connectedSpace
  exact hyperboloidGraphHomeomorph.surjective.connectedSpace
    continuous_hyperboloidGraph

/-- A unit tangent admits a unit perpendicular normal by the same independent-vector orthogonalization.
Textbook G06 N02.1, lines 59–61: retain the witness and literal normalization formula. -/
theorem exists_lorentzNormal_of_unitTangent
    (p : Hyperboloid) (e : Fin 3 → ℝ)
    (hep : lorentzBilinear e p.val = 0)
    (hee : lorentzBilinear e e = 1) :
    ∃ z : Fin 3 → ℝ,
      z ∈ (lorentzFunctional p.val).ker ∧
      z ∉ Submodule.span ℝ ({e} : Set (Fin 3 → ℝ)) ∧
      ∃ n : Fin 3 → ℝ,
        n = (Real.sqrt (lorentzBilinear
          (z - lorentzBilinear z e • e)
          (z - lorentzBilinear z e • e)))⁻¹ •
            (z - lorentzBilinear z e • e) ∧
        lorentzBilinear n n = 1 ∧
        lorentzBilinear n p.val = 0 ∧ lorentzBilinear n e = 0 := by
  obtain ⟨z, hzp, hze, hnp, hne, hnn⟩ :=
    Hyperbolic.exists_lorentzAxisDirection e hee p
      ((Hyperbolic.lorentzBilinear_symm p.val e).trans hep)
  exact ⟨z, hzp, hze, lorentzAxisDirectionCoords e z, rfl, hnn, hnp, hne⟩

/-- A timelike plane spanned by a point and tangent equals its unit normal's kernel.
Textbook G06 N02.2, lines 61–63: span inclusion and equality of dimensions. -/
theorem lorentzPlane_eq_normalKer
    (W : Submodule ℝ (Fin 3 → ℝ))
    (hW : IsLorentzTimelikePlane W)
    (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hspan : W = Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)))
    (hnn : lorentzBilinear n n = 1)
    (hnp : lorentzBilinear n p.val = 0)
    (hne : lorentzBilinear n e = 0) :
    W = (lorentzFunctional n).ker := by
  have hsurj : Function.Surjective (lorentzFunctional n).toLinearMap := by
    intro a
    refine ⟨a • n, ?_⟩
    change lorentzFunctional n (a • n) = a
    rw [← lorentzBilinear_eq_functional]
    simp [hnn]
  have hdim : Module.finrank ℝ (lorentzFunctional n).ker = 2 := by
    have h := (lorentzFunctional n).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    have h' : 1 + Module.finrank ℝ (lorentzFunctional n).ker = 3 := by
      simpa using h
    omega
  have hle : W ≤ (lorentzFunctional n).ker := by
    rw [hspan]
    apply Submodule.span_le.mpr
    intro x hx
    change lorentzFunctional n x = 0
    rw [← lorentzBilinear_eq_functional]
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact hnp
    · have he : x = e := by simpa using hx
      subst x
      exact hne
  exact Submodule.eq_of_le_of_finrank_eq hle (hW.1.trans hdim.symm)

/-- A timelike plane's unit normals are exactly the two signs of any one unit normal.
Textbook G06 N02.3, lines 63–65: the restricted tangent functional has one-dimensional kernel. -/
theorem lorentzPlane_unitNormals_iff
    (W : Submodule ℝ (Fin 3 → ℝ))
    (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hep : lorentzBilinear e p.val = 0)
    (hee : lorentzBilinear e e = 1)
    (hspan : W = Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)))
    (hnn : lorentzBilinear n n = 1)
    (hWn : W = (lorentzFunctional n).ker)
    (m : Fin 3 → ℝ) :
    (lorentzBilinear m m = 1 ∧ W = (lorentzFunctional m).ker) ↔
      m = n ∨ m = -n := by
  have hpW : p.val ∈ W := by
    rw [hspan]
    exact Submodule.subset_span (by simp)
  have heW : e ∈ W := by
    rw [hspan]
    exact Submodule.subset_span (by simp)
  have horth (v : Fin 3 → ℝ) (hWv : W = (lorentzFunctional v).ker) :
      lorentzBilinear v p.val = 0 ∧ lorentzBilinear v e = 0 := by
    have hp := hpW
    have he := heW
    rw [hWv] at hp he
    change lorentzFunctional v p.val = 0 at hp
    change lorentzFunctional v e = 0 at he
    rw [← lorentzBilinear_eq_functional] at hp he
    exact ⟨hp, he⟩
  constructor
  · rintro ⟨hmm, hWm⟩
    obtain ⟨hnp, hne⟩ := horth n hWn
    obtain ⟨hmp, hme⟩ := horth m hWm
    let tangentKer := (lorentzFunctional p.val).ker
    have heK : e ∈ tangentKer := by
      change lorentzFunctional p.val e = 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hep
    have hnK : n ∈ tangentKer := by
      change lorentzFunctional p.val n = 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hnp
    have hmK : m ∈ tangentKer := by
      change lorentzFunctional p.val m = 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hmp
    let eK : tangentKer := ⟨e, heK⟩
    let nK : tangentKer := ⟨n, hnK⟩
    let mK : tangentKer := ⟨m, hmK⟩
    let f : tangentKer →ₗ[ℝ] ℝ :=
      (lorentzFunctional e).toLinearMap.comp tangentKer.subtype
    have hsurj : Function.Surjective f := by
      intro a
      refine ⟨a • eK, ?_⟩
      change lorentzFunctional e (a • e) = a
      rw [← lorentzBilinear_eq_functional]
      simp [hee]
    have hdim : Module.finrank ℝ f.ker = 1 := by
      have h := f.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hsurj] at h
      have h' : 1 + Module.finrank ℝ f.ker = 2 := by
        simpa [tangentKer, finrank_lorentzKer] using h
      omega
    have hnker : nK ∈ f.ker := by
      change lorentzFunctional e n = 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hne
    have hmker : mK ∈ f.ker := by
      change lorentzFunctional e m = 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hme
    have hnne : nK ≠ 0 := by
      intro hz
      have hnzero : n = 0 := congrArg (fun v : tangentKer => (v : Fin 3 → ℝ)) hz
      rw [hnzero] at hnn
      simpa using hnn
    have hle : Submodule.span ℝ ({nK} : Set tangentKer) ≤ f.ker := by
      apply Submodule.span_le.mpr
      intro v hv
      have hvn : v = nK := by simpa using hv
      subst v
      exact hnker
    have hspanKer : Submodule.span ℝ ({nK} : Set tangentKer) = f.ker :=
      Submodule.eq_of_le_of_finrank_eq hle ((finrank_span_singleton hnne).trans hdim.symm)
    have hmspan : mK ∈ Submodule.span ℝ ({nK} : Set tangentKer) := by
      rw [hspanKer]
      exact hmker
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmspan
    have ham : a • n = m := congrArg (fun v : tangentKer => (v : Fin 3 → ℝ)) ha
    have haa : a * a = 1 := by
      rw [← ham] at hmm
      simpa only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hnn, mul_one] using hmm
    have hfactor : (a - 1) * (a + 1) = 0 := by nlinarith [haa]
    rcases mul_eq_zero.mp hfactor with hpos | hneg
    · have haone : a = 1 := by linarith
      left
      simpa [haone] using ham.symm
    · have haneg : a = -1 := by linarith
      right
      simpa [haneg] using ham.symm
  · rintro (rfl | rfl)
    · exact ⟨hnn, hWn⟩
    · constructor
      · simpa only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] using hnn
      · rw [hWn]
        ext v
        change lorentzFunctional n v = 0 ↔ lorentzFunctional (-n) v = 0
        rw [← lorentzBilinear_eq_functional, ← lorentzBilinear_eq_functional]
        simp only [map_neg, ContinuousLinearMap.neg_apply, neg_eq_zero]

/-- Changing a unit normal's sign leaves the actual ambient reflection unchanged.
Textbook G06 N02.4, line 66: both signs have the same reflection formula. -/
theorem lorentzReflection_neg_normal
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1)
    (hneg : lorentzBilinear (-n) (-n) = 1) :
    lorentzReflection (-n) hneg = lorentzReflection n hn := by
  ext v
  rw [lorentzReflection_apply, lorentzReflection_apply]
  simp only [map_neg, mul_neg, smul_neg, neg_smul, neg_neg]

/-- Every timelike plane admits a unit normal, unique up to sign, defining the same reflection.
Textbook G06 N02.5, lines 53–66: the arbitrary-plane construction and full geodesic receipt. -/
theorem IsLorentzTimelikePlane.exists_unitNormal
    (W : Submodule ℝ (Fin 3 → ℝ)) (hW : IsLorentzTimelikePlane W) :
    ∃ p : Hyperboloid, ∃ e n : Fin 3 → ℝ,
      ∃ hep : lorentzBilinear e p.val = 0,
      ∃ hee : lorentzBilinear e e = 1,
      ∃ hnn : lorentzBilinear n n = 1,
        p.val ∈ W ∧ e ∈ W ∧
        W = Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)) ∧
        lorentzBilinear n p.val = 0 ∧ lorentzBilinear n e = 0 ∧
        W = (lorentzFunctional n).ker ∧
        Set.range (hyperboloidGeodesic p e hep hee) =
          {q : Hyperboloid | q.val ∈ W} ∧
        (∀ m : Fin 3 → ℝ,
          (lorentzBilinear m m = 1 ∧ W = (lorentzFunctional m).ker) ↔
            m = n ∨ m = -n) ∧
        (∀ (m : Fin 3 → ℝ) (hm : lorentzBilinear m m = 1),
          W = (lorentzFunctional m).ker →
          lorentzReflection m hm = lorentzReflection n hnn) := by
  obtain ⟨p,e,hep,hee,hpW,heW,hspan,hrange⟩ :=
    Hyperbolic.IsLorentzTimelikePlane.exists_hyperboloidGeodesic hW
  obtain ⟨z,hzp,hze,n,hnformula,hnn,hnp,hne⟩ :=
    exists_lorentzNormal_of_unitTangent p e hep hee
  have hWn := lorentzPlane_eq_normalKer
    W hW p e n hspan hnn hnp hne
  have hclass := lorentzPlane_unitNormals_iff
    W p e n hep hee hspan hnn hWn
  refine ⟨p,e,n,hep,hee,hnn,hpW,heW,hspan,hnp,hne,hWn,hrange,hclass,?_⟩
  intro m hm hWm
  rcases (hclass m).mp ⟨hm,hWm⟩ with hpos | hneg
  · subst m
    rfl
  · subst m
    exact lorentzReflection_neg_normal n hnn hm

/-- The time coordinate of a Lorentz reflection is continuous on the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 84–85. -/
theorem continuous_lorentzReflection_time (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  Continuous (fun p : Hyperboloid => lorentzReflection n hn p.val 2) :=
  (continuous_apply 2).comp
    ((lorentzReflection n hn).toContinuousLinearEquiv.continuous.comp
      continuous_subtype_val)

/-- Lorentz reflection preserves the square minus one of every upper-sheet point.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 85–86. -/
theorem lorentzReflection_hyperboloid_square (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
  lorentzBilinear (lorentzReflection n hn p.val)
    (lorentzReflection n hn p.val) = -1 := by
  have hp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  exact (lorentzReflection_preserves n hn p.val p.val).trans hp

/-- The reflected time coordinate never vanishes on the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 86–87. -/
theorem lorentzReflection_time_ne_zero (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
  lorentzReflection n hn p.val 2 ≠ 0 :=
  lorentzUnit_time_ne_zero _ (lorentzReflection_hyperboloid_square n hn p)

/-- The constructed upper-sheet axis point is fixed by its Lorentz reflection.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 90–91. -/
theorem lorentzReflection_axisPoint (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  lorentzReflection n hn (lorentzAxisPoint n hn).val =
    (lorentzAxisPoint n hn).val :=
  (lorentzReflection_fixed_iff n hn _).mpr
    (lorentzAxisPointCoords_spec n hn).2

/-- Lorentz reflection has positive time on the entire upper sheet. Connectedness and
the fixed positive-time axis point determine the sign of its nonvanishing time coordinate.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 87–92. -/
theorem lorentzReflection_time_pos (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
  0 < lorentzReflection n hn p.val 2 := by
  let : ConnectedSpace Hyperboloid := connectedSpace_hyperboloidGraph
  by_contra hpos
  have hbad : lorentzReflection n hn p.val 2 ≤ 0 := le_of_not_gt hpos
  have haxis : 0 < lorentzReflection n hn (lorentzAxisPoint n hn).val 2 := by
    rw [lorentzReflection_axisPoint]
    exact (lorentzAxisPoint n hn).property.2
  obtain ⟨q, hq⟩ := intermediate_value_univ p (lorentzAxisPoint n hn)
    (continuous_lorentzReflection_time n hn) ⟨hbad, haxis.le⟩
  exact lorentzReflection_time_ne_zero n hn q hq

/-- The ambient reflection satisfies the defining equations of the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 92–93. -/
theorem lorentzReflection_hyperboloid_mem (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
  (lorentzReflection n hn p.val 0)^2 +
    (lorentzReflection n hn p.val 1)^2 -
    (lorentzReflection n hn p.val 2)^2 = -1 ∧
  0 < lorentzReflection n hn p.val 2 := by
  refine ⟨?_, lorentzReflection_time_pos n hn p⟩
  simpa only [lorentzBilinear_apply, pow_two] using
    lorentzReflection_hyperboloid_square n hn p

/-- The restriction of the ambient Lorentz reflection to the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 92–93. -/
def hyperboloidReflection (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) : Hyperboloid :=
  ⟨lorentzReflection n hn p.val, lorentzReflection_hyperboloid_mem n hn p⟩

/-- The restricted reflection has exactly the original ambient value.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 92–93. -/
theorem hyperboloidReflection_val (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
  (hyperboloidReflection n hn p).val = lorentzReflection n hn p.val := rfl

/-- The upper-sheet reflection is an involution.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 92–93. -/
theorem hyperboloidReflection_involutive (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  Function.Involutive (hyperboloidReflection n hn) := fun p =>
  Subtype.ext (lorentzReflection_involutive n hn p.val)

/-- The upper-sheet reflection as an equivalence, with the same map as inverse.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 93. -/
def hyperboloidReflectionEquiv (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) : Hyperboloid ≃ Hyperboloid where
  toFun := hyperboloidReflection n hn
  invFun := hyperboloidReflection n hn
  left_inv := hyperboloidReflection_involutive n hn
  right_inv := hyperboloidReflection_involutive n hn

/-- The restricted Lorentz reflection is smooth in the existing real hyperboloid atlas.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 93–94. -/
theorem contMDiff_hyperboloidReflection (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) :
  ContMDiff I I ∞ (hyperboloidReflection n hn) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  have hA : ContMDiff I J ∞
      (fun p : Hyperboloid => lorentzReflection n hn p.val) :=
    (lorentzReflection n hn).toContinuousLinearEquiv.contDiff.comp_contMDiff
      contMDiff_hyperboloid_val
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.contMDiffOn.comp_contMDiff hA
    (fun p => hyperboloid_denominator_pos (hyperboloidReflection n hn p))

/-- The upper-sheet reflection as a diffeomorphism, with the same smooth inverse.

Textbook source: reviewed Lorentz reflection proof, S01.reflection, lines 94. -/
def hyperboloidReflectionDiffeomorph (n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) : Hyperboloid ≃ₘ⟮I, I⟯ Hyperboloid :=
  { hyperboloidReflectionEquiv n hn with
    contMDiff_toFun := contMDiff_hyperboloidReflection n hn
    contMDiff_invFun := contMDiff_hyperboloidReflection n hn }

/-- The fixed points of the restricted reflection are exactly the zero-normal-coordinate points.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_fixed_iff (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
    hyperboloidReflection n hn p = p ↔ lorentzBilinear p.val n = 0 := by
  rw [Subtype.ext_iff]
  exact lorentzReflection_fixed_iff n hn p.val

/-- The restricted reflection negates the normal coordinate.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_normal (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid) :
    lorentzBilinear (hyperboloidReflection n hn p).val n = -lorentzBilinear p.val n := by
  rw [hyperboloidReflection_val]
  exact lorentzReflection_normal n hn p.val

/-- The full fixed set is the all-real geodesic through the explicit axis point, with its
unit tangent, independent frame, dimension, Gram identity and normal-kernel span.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_fixed_geodesic (n : V) (hn : lorentzBilinear n n = 1) :
    ∃ (p : Hyperboloid) (e : V)
      (hep : lorentzBilinear e p.val = 0) (hee : lorentzBilinear e e = 1),
      p = lorentzAxisPoint n hn ∧ lorentzBilinear p.val n = 0 ∧
      lorentzBilinear e n = 0 ∧
      LinearIndependent ℝ ![p.val,e] ∧
      Module.finrank ℝ (lorentzFunctional n).ker = 2 ∧
      (∀ a b : ℝ, lorentzBilinear (a • p.val+b • e) (a • p.val+b • e)
        = -a^2+b^2) ∧
      Submodule.span ℝ ({p.val,e} : Set V) = (lorentzFunctional n).ker ∧
      Set.range (hyperboloidGeodesic p e hep hee) =
        {q : Hyperboloid | lorentzBilinear q.val n = 0} ∧
      {q : Hyperboloid | hyperboloidReflection n hn q = q} =
        Set.range (hyperboloidGeodesic p e hep hee) := by
  let p := lorentzAxisPoint n hn
  have hpn : lorentzBilinear p.val n = 0 := (lorentzAxisPointCoords_spec n hn).2
  obtain ⟨z,hz,hznot,hep,hen,hee⟩ := exists_lorentzAxisDirection n hn p hpn
  let e := lorentzAxisDirectionCoords n z
  have hspan := lorentzAxis_span_ker n hn p hpn e hep hen hee
  obtain ⟨hli,hdim,hgram,hrange⟩ := hyperboloidGeodesic_plane p e hep hee
  have hk : Module.finrank ℝ (lorentzFunctional n).ker = 2 := by
    rw [← hspan]
    exact hdim
  have hr : Set.range (hyperboloidGeodesic p e hep hee) =
      {q : Hyperboloid | lorentzBilinear q.val n = 0} := by
    rw [hrange, hspan]
    ext q
    change lorentzFunctional n q.val = 0 ↔ lorentzBilinear q.val n = 0
    rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm n q.val]
  refine ⟨p,e,hep,hee,rfl,hpn,hen,hli,hk,hgram,hspan,hr,?_⟩
  rw [hr]
  ext q
  exact hyperboloidReflection_fixed_iff n hn q

/-- The all-real normal radial geodesic has normal coordinate equal to the hyperbolic sine.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidGeodesic_normal_coordinate (n : V) (hn : lorentzBilinear n n = 1)
    (p : Hyperboloid) (hpn : lorentzBilinear p.val n = 0) (s : ℝ) :
    lorentzBilinear
      (hyperboloidGeodesic p n ((lorentzBilinear_symm n p.val).trans hpn) hn s).val n =
      Real.sinh s := by
  change lorentzBilinear (Real.cosh s • p.val + Real.sinh s • n) n = Real.sinh s
  simp only [map_add, ContinuousLinearMap.add_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hpn, hn, mul_zero, mul_one, zero_add]

/-- Both strict normal-coordinate sides are open and nonempty.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_sides_open_nonempty (n : V) (hn : lorentzBilinear n n = 1) :
    IsOpen {p : Hyperboloid | 0 < lorentzBilinear p.val n} ∧ IsOpen {p : Hyperboloid | lorentzBilinear p.val n < 0} ∧
    ({p : Hyperboloid | 0 < lorentzBilinear p.val n}).Nonempty ∧ ({p : Hyperboloid | lorentzBilinear p.val n < 0}).Nonempty := by
  have hc : Continuous (fun p : Hyperboloid => lorentzBilinear p.val n) := by
    have h : Continuous (fun p : Hyperboloid => lorentzFunctional n p.val) :=
      (lorentzFunctional n).continuous.comp continuous_subtype_val
    simpa only [← lorentzBilinear_eq_functional, lorentzBilinear_symm] using h
  refine ⟨isOpen_lt continuous_const hc, isOpen_lt hc continuous_const, ?_⟩
  let p := lorentzAxisPoint n hn
  have hpn : lorentzBilinear p.val n = 0 := (lorentzAxisPointCoords_spec n hn).2
  let γ := hyperboloidGeodesic p n ((lorentzBilinear_symm n p.val).trans hpn) hn
  constructor
  · refine ⟨γ 1, ?_⟩
    change 0 < lorentzBilinear (γ 1).val n
    rw [hyperboloidGeodesic_normal_coordinate n hn p hpn 1]
    exact Real.sinh_pos_iff.mpr (by norm_num)
  · refine ⟨γ (-1), ?_⟩
    change lorentzBilinear (γ (-1)).val n < 0
    rw [hyperboloidGeodesic_normal_coordinate n hn p hpn (-1)]
    exact Real.sinh_neg_iff.mpr (by norm_num)

/-- The reflection exchanges both strict normal-coordinate sides by exact image equalities.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_open_side_images (n : V) (hn : lorentzBilinear n n = 1) :
    (hyperboloidReflection n hn) '' {p : Hyperboloid | 0 < lorentzBilinear p.val n} = {p : Hyperboloid | lorentzBilinear p.val n < 0} ∧
    (hyperboloidReflection n hn) '' {p : Hyperboloid | lorentzBilinear p.val n < 0} = {p : Hyperboloid | 0 < lorentzBilinear p.val n} := by
  constructor
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change 0 < lorentzBilinear p.val n at hp
      change lorentzBilinear (hyperboloidReflection n hn p).val n < 0
      rw [hyperboloidReflection_normal]
      linarith
    · intro hq
      change lorentzBilinear q.val n < 0 at hq
      refine ⟨hyperboloidReflection n hn q, ?_, hyperboloidReflection_involutive n hn q⟩
      change 0 < lorentzBilinear (hyperboloidReflection n hn q).val n
      rw [hyperboloidReflection_normal]
      linarith
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change lorentzBilinear p.val n < 0 at hp
      change 0 < lorentzBilinear (hyperboloidReflection n hn p).val n
      rw [hyperboloidReflection_normal]
      linarith
    · intro hq
      change 0 < lorentzBilinear q.val n at hq
      refine ⟨hyperboloidReflection n hn q, ?_, hyperboloidReflection_involutive n hn q⟩
      change lorentzBilinear (hyperboloidReflection n hn q).val n < 0
      rw [hyperboloidReflection_normal]
      linarith

/-- The reflection is a bijection from either strict normal-coordinate side onto the other.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_open_side_bijOn (n : V) (hn : lorentzBilinear n n = 1) :
    Set.BijOn (hyperboloidReflection n hn) {p : Hyperboloid | 0 < lorentzBilinear p.val n} {p : Hyperboloid | lorentzBilinear p.val n < 0} ∧
    Set.BijOn (hyperboloidReflection n hn) {p : Hyperboloid | lorentzBilinear p.val n < 0} {p : Hyperboloid | 0 < lorentzBilinear p.val n} := by
  have h := hyperboloidReflection_open_side_images n hn
  exact ⟨(hyperboloidReflectionEquiv n hn).image_eq_iff_bijOn.mp h.1,
    (hyperboloidReflectionEquiv n hn).image_eq_iff_bijOn.mp h.2⟩

/-- The reflection exchanges both weak normal-coordinate half-spaces by exact image equalities.

Textbook source: reviewed Lorentz reflection proof, S02, lines 96–102. -/
theorem hyperboloidReflection_closed_side_images (n : V) (hn : lorentzBilinear n n = 1) :
    (hyperboloidReflection n hn) '' {p : Hyperboloid | 0 ≤ lorentzBilinear p.val n} = {p : Hyperboloid | lorentzBilinear p.val n ≤ 0} ∧
    (hyperboloidReflection n hn) '' {p : Hyperboloid | lorentzBilinear p.val n ≤ 0} = {p : Hyperboloid | 0 ≤ lorentzBilinear p.val n} := by
  constructor
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change 0 ≤ lorentzBilinear p.val n at hp
      change lorentzBilinear (hyperboloidReflection n hn p).val n ≤ 0
      rw [hyperboloidReflection_normal]
      linarith
    · intro hq
      change lorentzBilinear q.val n ≤ 0 at hq
      refine ⟨hyperboloidReflection n hn q, ?_, hyperboloidReflection_involutive n hn q⟩
      change 0 ≤ lorentzBilinear (hyperboloidReflection n hn q).val n
      rw [hyperboloidReflection_normal]
      linarith
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change lorentzBilinear p.val n ≤ 0 at hp
      change 0 ≤ lorentzBilinear (hyperboloidReflection n hn p).val n
      rw [hyperboloidReflection_normal]
      linarith
    · intro hq
      change 0 ≤ lorentzBilinear q.val n at hq
      refine ⟨hyperboloidReflection n hn q, ?_, hyperboloidReflection_involutive n hn q⟩
      change lorentzBilinear (hyperboloidReflection n hn q).val n ≤ 0
      rw [hyperboloidReflection_normal]
      linarith

/-- Lorentz reflection carries each tangent kernel into the kernel at the reflected point.

Textbook source: reviewed Lorentz reflection proof, M01, lines 118–120. -/
theorem lorentzReflection_mem_tangentKer
    (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (v : V) (hv : v ∈ (lorentzFunctional p.val).ker) :
    lorentzReflection n hn v ∈
      (lorentzFunctional (hyperboloidReflection n hn p).val).ker := by
  change lorentzFunctional (hyperboloidReflection n hn p).val
    (lorentzReflection n hn v) = 0
  rw [← lorentzBilinear_eq_functional, hyperboloidReflection_val,
    lorentzReflection_preserves]
  exact hv

/-- The intrinsic differential of the restricted reflection is its ambient linear map
under the actual hyperboloid inclusion.

Textbook source: reviewed Lorentz reflection proof, M01, line 118. -/
theorem mfderiv_hyperboloidReflection_val
    (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (v : TangentSpace I p) :
    mfderiv I J (fun q : Hyperboloid => q.val) (hyperboloidReflection n hn p)
      (mfderiv I I (hyperboloidReflection n hn) p v) =
    lorentzReflection n hn (mfderiv I J (fun q : Hyperboloid => q.val) p v) := by
  let A : V ≃L[ℝ] V := (lorentzReflection n hn).toContinuousLinearEquiv
  have hf := (contMDiff_hyperboloidReflection n hn).mdifferentiable (by simp)
  have hi := contMDiff_hyperboloid_val.mdifferentiable (by simp)
  have hA : MDifferentiable J J (A : V → V) :=
    (A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hleft := mfderiv_comp_apply p (hi (hyperboloidReflection n hn p)) (hf p) v
  have hright := mfderiv_comp_apply p (hA p.val) (hi p) v
  have hfun : (fun q : Hyperboloid => q.val) ∘ hyperboloidReflection n hn =
      (A : V → V) ∘ (fun q : Hyperboloid => q.val) := rfl
  have hcongr :
      mfderiv I J ((fun q : Hyperboloid => q.val) ∘ hyperboloidReflection n hn) p =
      mfderiv I J ((A : V → V) ∘ (fun q : Hyperboloid => q.val)) p :=
    mfderiv_congr hfun
  have hderiv : mfderiv J J (A : V → V) p.val = A.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact A.toContinuousLinearMap.fderiv
  have heq := hleft.symm.trans ((congrArg (fun L => L v) hcongr).trans hright)
  rw [hderiv] at heq
  exact heq

/-- Under the established tangent-kernel identification, the differential is Lorentz reflection.

Textbook source: reviewed Lorentz reflection proof, M01, lines 118–120. -/
theorem hyperboloidReflection_tangentEquivKer
    (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (v : TangentSpace I p) :
    (hyperboloidTangentEquivKer (hyperboloidReflection n hn p)
      (mfderiv I I (hyperboloidReflection n hn) p v)).val =
    lorentzReflection n hn (hyperboloidTangentEquivKer p v).val := by
  simp only [hyperboloidTangentEquivKer_apply]
  exact mfderiv_hyperboloidReflection_val n hn p v

/-- The restricted reflection preserves the existing hyperboloid tangent tensor.

Textbook source: reviewed Lorentz reflection proof, M01, lines 120–122. -/
theorem hyperboloidReflection_preserves_tangentTensor
    (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (v w : TangentSpace I p) :
    hyperboloidTangentTensor (hyperboloidReflection n hn p)
      (mfderiv I I (hyperboloidReflection n hn) p v)
      (mfderiv I I (hyperboloidReflection n hn) p w) =
    hyperboloidTangentTensor p v w := by
  simp only [hyperboloidTangentTensor_apply, mfderiv_hyperboloidReflection_val]
  exact lorentzReflection_preserves n hn _ _

/-- The restricted reflection preserves the existing intrinsic hyperboloid metric pairing.

Textbook source: reviewed Lorentz reflection proof, M01, line 122. -/
theorem hyperboloidReflection_preserves_metric
    (n : V) (hn : lorentzBilinear n n = 1) (p : Hyperboloid)
    (v w : TangentSpace I p) :
    hyperboloidMetric.inner (hyperboloidReflection n hn p)
      (mfderiv I I (hyperboloidReflection n hn) p v)
      (mfderiv I I (hyperboloidReflection n hn) p w) =
    hyperboloidMetric.inner p v w := by
  simp only [hyperboloidMetric_inner]
  exact hyperboloidReflection_preserves_tangentTensor n hn p v w

/-- The restricted reflection preserves both real and extended speeds in the existing tangent metric.

Textbook source: reviewed Lorentz reflection proof, M02, lines 124–126. -/
theorem hyperboloidReflection_speed
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1)
    (γ : ℝ → Hyperboloid) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidReflection n hn ∘ γ) t (1 : ℝ)‖ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
    ‖mfderiv 𝓘(ℝ, ℝ) I (hyperboloidReflection n hn ∘ γ) t (1 : ℝ)‖ₑ =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  exact Manifold.speed_comp_of_tensorPreserving hyperboloidMetric hyperboloidMetric
    (hyperboloidReflection n hn) (contMDiff_hyperboloidReflection n hn)
    (hyperboloidReflection_preserves_metric n hn) γ t hγ

/-- The same reflection preserves within speeds on the same parameter set, including one-sided velocities.

Textbook source: reviewed Lorentz reflection proof, M02, lines 124–126. -/
theorem hyperboloidReflection_speedWithin
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1)
    (γ : ℝ → Hyperboloid) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (hyperboloidReflection n hn ∘ γ) s t (1 : ℝ)‖ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
    ‖mfderivWithin 𝓘(ℝ, ℝ) I (hyperboloidReflection n hn ∘ γ) s t (1 : ℝ)‖ₑ =
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  exact Manifold.speedWithin_comp_of_tensorPreserving hyperboloidMetric hyperboloidMetric
    (hyperboloidReflection n hn) (contMDiff_hyperboloidReflection n hn)
    (hyperboloidReflection_preserves_metric n hn) γ s t hγ hs

/-- The restricted reflection preserves the entire finite-piece length receipt: subdivisions, endpoints,
piece integrals, real and extended lengths, bridges and finiteness, including repeated pieces.

Textbook source: reviewed Lorentz reflection proof, M02, lines 126–127. -/
theorem hyperboloidReflection_length
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1)
    {γ : ℝ → Hyperboloid} {a b : ℝ} {k : ℕ} {cut : Fin (k+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b k cut) :
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    let P : Fin k → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let q : Fin k → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)‖
    let q' : Fin k → ℝ → ℝ := fun i t =>
      ‖mfderivWithin 𝓘(ℝ, ℝ) I (hyperboloidReflection n hn ∘ γ) (P i) t (1 : ℝ)‖
    IsPiecewiseC1On I (hyperboloidReflection n hn ∘ γ) a b k cut ∧
    (hyperboloidReflection n hn ∘ γ) a = hyperboloidReflection n hn (γ a) ∧
    (hyperboloidReflection n hn ∘ γ) b = hyperboloidReflection n hn (γ b) ∧
    (∀ i : Fin k, (∫ t in cut i.castSucc..cut i.succ, q' i t) =
      ∫ t in cut i.castSucc..cut i.succ, q i t) ∧
    piecewiseC1Length hyperboloidMetric (hyperboloidReflection n hn ∘ γ) cut =
      piecewiseC1Length hyperboloidMetric γ cut ∧
    0 ≤ piecewiseC1Length hyperboloidMetric γ cut ∧
    0 ≤ piecewiseC1Length hyperboloidMetric (hyperboloidReflection n hn ∘ γ) cut ∧
    pathELength I (hyperboloidReflection n hn ∘ γ) a b = pathELength I γ a b ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) ∧
    pathELength I (hyperboloidReflection n hn ∘ γ) a b < (⊤ : ℝ≥0∞) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length hyperboloidMetric γ cut) ∧
    pathELength I (hyperboloidReflection n hn ∘ γ) a b =
      ENNReal.ofReal (piecewiseC1Length hyperboloidMetric (hyperboloidReflection n hn ∘ γ) cut) ∧
    (∀ i : Fin k, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) =
      ∫⁻ t in P i, ENNReal.ofReal (q i t)) ∧
    (∀ i : Fin k, (∫⁻ t in P i, ENNReal.ofReal (q i t)) < (⊤ : ℝ≥0∞)) ∧
    (∀ i : Fin k, (∫⁻ t in P i, ENNReal.ofReal (q' i t)) < (⊤ : ℝ≥0∞)) := by
  exact hγ.length_comp_of_tensorPreserving hyperboloidMetric hyperboloidMetric
    (hyperboloidReflection n hn) (contMDiff_hyperboloidReflection n hn)
    (hyperboloidReflection_preserves_metric n hn)

/-- Transporting every competitor gives the first inequality for the original five-index length infimum.

Textbook source: reviewed Lorentz reflection proof, M02, lines 127–129. -/
theorem hyperboloidReflection_piecewiseC1EDist_le
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1) (p q : Hyperboloid) :
    piecewiseC1EDist hyperboloidMetric (hyperboloidReflection n hn p)
      (hyperboloidReflection n hn q) ≤ piecewiseC1EDist hyperboloidMetric p q := by
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  unfold piecewiseC1EDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun k => le_iInf fun cut =>
    le_iInf fun γ => ?_
  rcases hyperboloidReflection_length n hn γ.property.1 with
    ⟨hc, ha, hb, hp, hr, hn0, hn1, he, hf0, hf1, hbr0, hbr1, hpe, hpf0, hpf1⟩
  let η : PiecewiseC1CurveOn I a b k cut
      (hyperboloidReflection n hn p) (hyperboloidReflection n hn q) :=
    ⟨hyperboloidReflection n hn ∘ γ.val, hc,
      congrArg (hyperboloidReflection n hn) γ.property.2.1,
      congrArg (hyperboloidReflection n hn) γ.property.2.2⟩
  exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le k
    (iInf_le_of_le cut (iInf_le_of_le η (le_of_eq (congrArg ENNReal.ofReal hr))))))

/-- The actual involution gives the reverse inequality for the same extended length distance.

Textbook source: reviewed Lorentz reflection proof, M02, lines 129–130. -/
theorem hyperboloidReflection_piecewiseC1EDist
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1) (p q : Hyperboloid) :
    piecewiseC1EDist hyperboloidMetric (hyperboloidReflection n hn p)
      (hyperboloidReflection n hn q) = piecewiseC1EDist hyperboloidMetric p q := by
  have hforward := hyperboloidReflection_piecewiseC1EDist_le n hn p q
  have hbackward := hyperboloidReflection_piecewiseC1EDist_le n hn
    (hyperboloidReflection n hn p) (hyperboloidReflection n hn q)
  rw [Hyperbolic.hyperboloidReflection_involutive n hn p,
    Hyperbolic.hyperboloidReflection_involutive n hn q] at hbackward
  exact le_antisymm hforward hbackward

/-- The restricted reflection preserves the original named hyperbolic length distance.
The established radial joining family supplies finite competitors for every pair of endpoints.

Textbook source: reviewed Lorentz reflection proof, M02, lines 130–133. -/
theorem hyperboloidReflection_lengthDist
    (n : Fin 3 → ℝ) (hn : lorentzBilinear n n = 1) (p q : Hyperboloid) :
    hyperboloidLengthDist (hyperboloidReflection n hn p) (hyperboloidReflection n hn q) =
      hyperboloidLengthDist p q := by
  exact congrArg ENNReal.toReal
    (hyperboloidReflection_piecewiseC1EDist n hn p q)

/-- The timelike coefficient of a vector in an adapted Lorentz frame.

Textbook source: reviewed Lorentz reflection proof, S03, lines 105–107. -/
def hyperboloidAdaptedTime (p : Hyperboloid) (u : Fin 3 → ℝ) : ℝ :=
  -lorentzFunctional p.val u

/-- The two spacelike coefficient projections on the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S03, lines 105,114. -/
def hyperboloidAdaptedProjection (e n : Fin 3 → ℝ) (q : Hyperboloid) : ℝ × ℝ :=
  (lorentzFunctional e q.val, lorentzFunctional n q.val)

/-- Every vector decomposes in the prescribed adapted Lorentz frame, with its actual pairing coefficients.

Textbook source: reviewed Lorentz reflection proof, S03, lines 104–105. -/
theorem lorentzAdapted_decomposition (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (u : Fin 3 → ℝ) :
  u = hyperboloidAdaptedTime p u • p.val +
    lorentzFunctional e u • e + lorentzFunctional n u • n := by
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hpe : lorentzBilinear p.val e = 0 := (lorentzBilinear_symm _ _).trans hep
  have hu : u - lorentzFunctional n u • n ∈ (lorentzFunctional n).ker := by
    change lorentzFunctional n (u - lorentzFunctional n u • n) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [← lorentzBilinear_eq_functional, hn]
    ring
  have hspan : u - lorentzFunctional n u • n ∈
      Submodule.span ℝ ({p.val, e} : Set (Fin 3 → ℝ)) := by
    rw [lorentzAxis_span_ker n hn p hpn e hep hen hee]
    exact hu
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
  have ha : a = hyperboloidAdaptedTime p u := by
    have h := congrArg (fun v => lorentzFunctional p.val v) hab
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at h
    rw [← lorentzBilinear_eq_functional, hpp, hpe, hpn] at h
    dsimp [hyperboloidAdaptedTime]
    rw [← lorentzBilinear_eq_functional]
    linarith
  have hb : b = lorentzFunctional e u := by
    have h := congrArg (fun v => lorentzFunctional e v) hab
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at h
    rw [← lorentzBilinear_eq_functional, hep, hee, hen] at h
    rw [← lorentzBilinear_eq_functional]
    linarith
  rw [ha, hb] at hab
  exact (eq_sub_iff_add_eq.mp hab).symm

/-- The hyperboloid equation in adapted Lorentz coordinates.

Textbook source: reviewed Lorentz reflection proof, S03, lines 105–106. -/
theorem hyperboloidAdaptedTime_square (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (q : Hyperboloid) :
  -(hyperboloidAdaptedTime p q.val)^2 + (lorentzFunctional e q.val)^2 +
    (lorentzFunctional n q.val)^2 = -1 := by
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hqq : lorentzBilinear q.val q.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using q.property.1
  have hpe : lorentzBilinear p.val e = 0 := (lorentzBilinear_symm _ _).trans hep
  have hnp : lorentzBilinear n p.val = 0 := (lorentzBilinear_symm _ _).trans hpn
  have hne : lorentzBilinear n e = 0 := (lorentzBilinear_symm _ _).trans hen
  have h := congrArg (fun u => lorentzBilinear u u)
    (lorentzAdapted_decomposition p e n hn hpn hep hen hee q.val)
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  rw [hpp, hqq, hpe, hnp, hne, hep, hpn, hen, hee, hn] at h
  nlinarith [h]

/-- The timelike coefficient never vanishes on the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S03, lines 106. -/
theorem hyperboloidAdaptedTime_ne_zero (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (q : Hyperboloid) :
  hyperboloidAdaptedTime p q.val ≠ 0 := by
  intro hz
  have h := hyperboloidAdaptedTime_square p e n hn hpn hep hen hee q
  rw [hz] at h
  nlinarith [sq_nonneg (lorentzFunctional e q.val), sq_nonneg (lorentzFunctional n q.val)]

/-- The timelike coefficient of the frame base point is one.

Textbook source: reviewed Lorentz reflection proof, S03, lines 106–107. -/
theorem hyperboloidAdaptedTime_self (p : Hyperboloid) :
  hyperboloidAdaptedTime p p.val = 1 := by
  have h : lorentzFunctional p.val p.val = -1 := by
    simpa only [lorentzFunctional_apply, pow_two] using p.property.1
  simp only [hyperboloidAdaptedTime, h, neg_neg]

/-- Connectedness and the value at the base point make the adapted timelike coefficient positive.

Textbook source: reviewed Lorentz reflection proof, S03, lines 106–107. -/
theorem hyperboloidAdaptedTime_pos (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (q : Hyperboloid) :
  0 < hyperboloidAdaptedTime p q.val := by
  let : ConnectedSpace Hyperboloid := connectedSpace_hyperboloidGraph
  by_contra hpos
  have hbad : hyperboloidAdaptedTime p q.val ≤ 0 := le_of_not_gt hpos
  have hc : Continuous (fun r : Hyperboloid => hyperboloidAdaptedTime p r.val) :=
    ((lorentzFunctional p.val).continuous.comp continuous_subtype_val).neg
  have hp : 0 ≤ hyperboloidAdaptedTime p p.val := by
    rw [hyperboloidAdaptedTime_self]
    norm_num
  obtain ⟨r, hr⟩ := intermediate_value_univ q p hc ⟨hbad, hp⟩
  exact hyperboloidAdaptedTime_ne_zero p e n hn hpn hep hen hee r hr

/-- The positive timelike coefficient is the square root determined by the hyperboloid equation.

Textbook source: reviewed Lorentz reflection proof, S03, lines 107. -/
theorem hyperboloidAdaptedTime_sqrt (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (q : Hyperboloid) :
  hyperboloidAdaptedTime p q.val =
    Real.sqrt (1 + (lorentzFunctional e q.val)^2 + (lorentzFunctional n q.val)^2) := by
  have hs := hyperboloidAdaptedTime_square p e n hn hpn hep hen hee q
  have hp := hyperboloidAdaptedTime_pos p e n hn hpn hep hen hee q
  have heq : 1 + (lorentzFunctional e q.val)^2 + (lorentzFunctional n q.val)^2 =
      (hyperboloidAdaptedTime p q.val)^2 := by linarith
  rw [heq, Real.sqrt_sq hp.le]

/-- The explicit adapted graph in the ambient Lorentz space.

Textbook source: reviewed Lorentz reflection proof, S03, lines 108. -/
def hyperboloidAdaptedGraphCoords (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (ba : ℝ × ℝ) : Fin 3 → ℝ :=
  Real.sqrt (1 + ba.1^2 + ba.2^2) • p.val + ba.1 • e + ba.2 • n

/-- The adapted graph has Lorentz square minus one and the prescribed spacelike coefficients.

Textbook source: reviewed Lorentz reflection proof, S03, lines 108–110. -/
theorem hyperboloidAdaptedGraphCoords_spec (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (ba : ℝ × ℝ) :
  lorentzBilinear (hyperboloidAdaptedGraphCoords p e n ba)
    (hyperboloidAdaptedGraphCoords p e n ba) = -1 ∧
  lorentzFunctional e (hyperboloidAdaptedGraphCoords p e n ba) = ba.1 ∧
  lorentzFunctional n (hyperboloidAdaptedGraphCoords p e n ba) = ba.2 := by
  have hpp : lorentzBilinear p.val p.val = -1 := by
    simpa only [lorentzBilinear_apply, pow_two] using p.property.1
  have hpe : lorentzBilinear p.val e = 0 := (lorentzBilinear_symm _ _).trans hep
  have hnp : lorentzBilinear n p.val = 0 := (lorentzBilinear_symm _ _).trans hpn
  have hne : lorentzBilinear n e = 0 := (lorentzBilinear_symm _ _).trans hen
  have hs : (Real.sqrt (1 + ba.1^2 + ba.2^2))^2 = 1 + ba.1^2 + ba.2^2 :=
    Real.sq_sqrt (by positivity)
  constructor
  · simp only [hyperboloidAdaptedGraphCoords, map_add, map_smul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hpp, hpe, hnp, hne, hep, hpn, hen, hee, hn]
    nlinarith [hs]
  · constructor
    · rw [← lorentzBilinear_eq_functional]
      simp only [hyperboloidAdaptedGraphCoords, map_add, map_smul, smul_eq_mul,
        hep, hee, hen]
      ring
    · rw [← lorentzBilinear_eq_functional]
      simp only [hyperboloidAdaptedGraphCoords, map_add, map_smul, smul_eq_mul,
        hnp, hne, hn]
      ring

/-- The adapted graph takes the parameter origin to the frame base point.

Textbook source: reviewed Lorentz reflection proof, S03, lines 110–111. -/
theorem hyperboloidAdaptedGraphCoords_zero (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  hyperboloidAdaptedGraphCoords p e n (0, 0) = p.val := by
  simp [hyperboloidAdaptedGraphCoords]

/-- The adapted graph has positive time, by connectedness of the parameter plane and its value at the origin.

Textbook source: reviewed Lorentz reflection proof, S03, lines 109–111. -/
theorem hyperboloidAdaptedGraphCoords_time_pos (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (ba : ℝ × ℝ) :
  0 < hyperboloidAdaptedGraphCoords p e n ba 2 := by
  let : PathConnectedSpace ℝ := Real.instPathConnectedSpace
  let : PathConnectedSpace (ℝ × ℝ) := Prod.instPathConnectedSpace
  by_contra hpos
  have hbad : hyperboloidAdaptedGraphCoords p e n ba 2 ≤ 0 := le_of_not_gt hpos
  have hc : Continuous (hyperboloidAdaptedGraphCoords p e n) :=
    ((((continuous_const.add (continuous_fst.pow 2)).add
        (continuous_snd.pow 2)).sqrt.smul continuous_const).add
        (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const)
  have hzero : 0 ≤ hyperboloidAdaptedGraphCoords p e n (0, 0) 2 := by
    rw [hyperboloidAdaptedGraphCoords_zero p e n hn hpn hep hen hee]
    exact p.property.2.le
  obtain ⟨xy, hxy⟩ := intermediate_value_univ ba (0, 0)
    ((continuous_apply 2).comp hc) ⟨hbad, hzero⟩
  exact lorentzUnit_time_ne_zero _
    (hyperboloidAdaptedGraphCoords_spec p e n hn hpn hep hen hee xy).1 hxy

/-- The displayed adapted graph satisfies the actual upper-sheet subtype predicate.

Textbook source: reviewed Lorentz reflection proof, S03, lines 109–111. -/
theorem hyperboloidAdaptedGraphCoords_mem (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (ba : ℝ × ℝ) :
  (hyperboloidAdaptedGraphCoords p e n ba 0)^2 +
    (hyperboloidAdaptedGraphCoords p e n ba 1)^2 -
    (hyperboloidAdaptedGraphCoords p e n ba 2)^2 = -1 ∧
  0 < hyperboloidAdaptedGraphCoords p e n ba 2 := by
  refine ⟨?_, hyperboloidAdaptedGraphCoords_time_pos p e n hn hpn hep hen hee ba⟩
  simpa only [lorentzBilinear_apply, pow_two] using
    (hyperboloidAdaptedGraphCoords_spec p e n hn hpn hep hen hee ba).1

/-- The adapted graph as a map into the upper hyperboloid.

Textbook source: reviewed Lorentz reflection proof, S03, lines 108–111. -/
def hyperboloidAdaptedGraph (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (ba : ℝ × ℝ) : Hyperboloid :=
  ⟨hyperboloidAdaptedGraphCoords p e n ba,
    hyperboloidAdaptedGraphCoords_mem p e n hn hpn hep hen hee ba⟩

/-- The adapted graph and its coefficient projection are inverse in both directions.

Textbook source: reviewed Lorentz reflection proof, S03, lines 111–112. -/
theorem hyperboloidAdaptedGraph_inverse (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  (∀ ba : ℝ × ℝ,
    hyperboloidAdaptedProjection e n (hyperboloidAdaptedGraph p e n hn hpn hep hen hee ba) = ba) ∧
  (∀ q : Hyperboloid,
    hyperboloidAdaptedGraph p e n hn hpn hep hen hee (hyperboloidAdaptedProjection e n q) = q) := by
  constructor
  · intro ba
    exact Prod.ext
      (hyperboloidAdaptedGraphCoords_spec p e n hn hpn hep hen hee ba).2.1
      (hyperboloidAdaptedGraphCoords_spec p e n hn hpn hep hen hee ba).2.2
  · intro q
    apply Subtype.ext
    change Real.sqrt (1 + (lorentzFunctional e q.val)^2 +
      (lorentzFunctional n q.val)^2) • p.val +
      lorentzFunctional e q.val • e + lorentzFunctional n q.val • n = q.val
    rw [← hyperboloidAdaptedTime_sqrt p e n hn hpn hep hen hee q]
    exact (lorentzAdapted_decomposition p e n hn hpn hep hen hee q.val).symm

/-- The adapted graph into the upper hyperboloid is continuous.

Textbook source: reviewed Lorentz reflection proof, S03, lines 111–112. -/
theorem continuous_hyperboloidAdaptedGraph (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  Continuous (hyperboloidAdaptedGraph p e n hn hpn hep hen hee) := by
  have hc : Continuous (hyperboloidAdaptedGraphCoords p e n) :=
    ((((continuous_const.add (continuous_fst.pow 2)).add
        (continuous_snd.pow 2)).sqrt.smul continuous_const).add
        (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const)
  exact hc.subtype_mk (hyperboloidAdaptedGraphCoords_mem p e n hn hpn hep hen hee)

/-- The explicit adapted graph homeomorphism, with inverse given by its two coefficient functionals.

Textbook source: reviewed Lorentz reflection proof, S03, lines 111–112. -/
def hyperboloidAdaptedHomeomorph (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) : (ℝ × ℝ) ≃ₜ Hyperboloid where
  toFun := hyperboloidAdaptedGraph p e n hn hpn hep hen hee
  invFun := hyperboloidAdaptedProjection e n
  left_inv := (hyperboloidAdaptedGraph_inverse p e n hn hpn hep hen hee).1
  right_inv := (hyperboloidAdaptedGraph_inverse p e n hn hpn hep hen hee).2
  continuous_toFun := continuous_hyperboloidAdaptedGraph p e n hn hpn hep hen hee
  continuous_invFun :=
    ((lorentzFunctional e).continuous.comp continuous_subtype_val).prodMk
      ((lorentzFunctional n).continuous.comp continuous_subtype_val)

/-- The normal pairing on the adapted graph is exactly the second parameter.

Textbook source: reviewed Lorentz reflection proof, S03, lines 112. -/
theorem hyperboloidAdaptedGraph_normal (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) (ba : ℝ × ℝ) :
  lorentzBilinear (hyperboloidAdaptedGraph p e n hn hpn hep hen hee ba).val n = ba.2 := by
  rw [lorentzBilinear_symm, lorentzBilinear_eq_functional]
  exact (hyperboloidAdaptedGraphCoords_spec p e n hn hpn hep hen hee ba).2.2

/-- The two open half-planes map exactly onto the positive and negative normal sides.

Textbook source: reviewed Lorentz reflection proof, S03, lines 112–113. -/
theorem hyperboloidAdaptedGraph_sides (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  hyperboloidAdaptedGraph p e n hn hpn hep hen hee '' ((Set.univ : Set ℝ) ×ˢ Set.Ioi 0) =
    {q : Hyperboloid | 0 < lorentzBilinear q.val n} ∧
  hyperboloidAdaptedGraph p e n hn hpn hep hen hee '' ((Set.univ : Set ℝ) ×ˢ Set.Iio 0) =
    {q : Hyperboloid | lorentzBilinear q.val n < 0} := by
  constructor
  · ext q
    constructor
    · rintro ⟨ba, hba, rfl⟩
      change 0 < lorentzBilinear (hyperboloidAdaptedGraph p e n hn hpn hep hen hee ba).val n
      rw [hyperboloidAdaptedGraph_normal]
      exact hba.2
    · intro hq
      refine ⟨hyperboloidAdaptedProjection e n q, ?_,
        (hyperboloidAdaptedGraph_inverse p e n hn hpn hep hen hee).2 q⟩
      refine ⟨Set.mem_univ _, ?_⟩
      change 0 < lorentzFunctional n q.val
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hq
  · ext q
    constructor
    · rintro ⟨ba, hba, rfl⟩
      change lorentzBilinear (hyperboloidAdaptedGraph p e n hn hpn hep hen hee ba).val n < 0
      rw [hyperboloidAdaptedGraph_normal]
      exact hba.2
    · intro hq
      refine ⟨hyperboloidAdaptedProjection e n q, ?_,
        (hyperboloidAdaptedGraph_inverse p e n hn hpn hep hen hee).2 q⟩
      refine ⟨Set.mem_univ _, ?_⟩
      change lorentzFunctional n q.val < 0
      rw [← lorentzBilinear_eq_functional, lorentzBilinear_symm]
      exact hq

/-- Both normal sides are nonempty and path connected, as images of open half-planes.

Textbook source: reviewed Lorentz reflection proof, S03, lines 113–114. -/
theorem hyperboloid_normal_sides_pathConnected (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  IsPathConnected {q : Hyperboloid | 0 < lorentzBilinear q.val n} ∧ IsPathConnected {q : Hyperboloid | lorentzBilinear q.val n < 0} := by
  have hp : IsPathConnected ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).prod
      (convex_Ioi (0 : ℝ))).isPathConnected ⟨(0, 1), by simp⟩
  have hm : IsPathConnected ((Set.univ : Set ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).prod
      (convex_Iio (0 : ℝ))).isPathConnected ⟨(0, -1), by simp⟩
  exact ⟨(hyperboloidAdaptedGraph_sides p e n hn hpn hep hen hee).1 ▸
      hp.image (continuous_hyperboloidAdaptedGraph p e n hn hpn hep hen hee),
    (hyperboloidAdaptedGraph_sides p e n hn hpn hep hen hee).2 ▸
      hm.image (continuous_hyperboloidAdaptedGraph p e n hn hpn hep hen hee)⟩

/-- A preconnected subset avoiding the zero axis has a constant normal sign, including the empty subset.

Textbook source: reviewed Lorentz reflection proof, S03, lines 114–115. -/
theorem hyperboloid_normal_sign_on_preconnected (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1)
    (s : Set Hyperboloid) (hs : IsPreconnected s)
    (haxis : s ⊆ {q : Hyperboloid | lorentzBilinear q.val n ≠ 0}) :
  s ⊆ {q : Hyperboloid | 0 < lorentzBilinear q.val n} ∨ s ⊆ {q : Hyperboloid | lorentzBilinear q.val n < 0} := by
  by_cases hpos : s ⊆ {q : Hyperboloid | 0 < lorentzBilinear q.val n}
  · exact Or.inl hpos
  · right
    obtain ⟨q, hq, hqnot⟩ := Set.not_subset.mp hpos
    intro r hr
    change lorentzBilinear r.val n < 0
    by_contra hrnot
    have hc : Continuous (fun z : Hyperboloid => lorentzBilinear z.val n) := by
      have he : (fun z : Hyperboloid => lorentzBilinear z.val n) =
          (fun z : Hyperboloid => lorentzFunctional n z.val) := by
        funext z
        rw [lorentzBilinear_symm, lorentzBilinear_eq_functional]
      rw [he]
      exact (lorentzFunctional n).continuous.comp continuous_subtype_val
    obtain ⟨z, hz, hzero⟩ := hs.intermediate_value hq hr hc.continuousOn
      ⟨le_of_not_gt hqnot, le_of_not_gt hrnot⟩
    exact haxis hz hzero

/-- The zero-axis complement has exactly the two normal sides as its distinct, disjoint connected components.

Textbook source: reviewed Lorentz reflection proof, S03, lines 115–116. -/
theorem hyperboloid_normal_components (p : Hyperboloid) (e n : Fin 3 → ℝ)
    (hn : lorentzBilinear n n = 1) (hpn : lorentzBilinear p.val n = 0)
    (hep : lorentzBilinear e p.val = 0) (hen : lorentzBilinear e n = 0)
    (hee : lorentzBilinear e e = 1) :
  (∀ q : Hyperboloid, 0 < lorentzBilinear q.val n →
    connectedComponentIn {q : Hyperboloid | lorentzBilinear q.val n ≠ 0} q = {q : Hyperboloid | 0 < lorentzBilinear q.val n}) ∧
  (∀ q : Hyperboloid, lorentzBilinear q.val n < 0 →
    connectedComponentIn {q : Hyperboloid | lorentzBilinear q.val n ≠ 0} q = {q : Hyperboloid | lorentzBilinear q.val n < 0}) ∧
  {C : Set Hyperboloid | ∃ q : Hyperboloid, lorentzBilinear q.val n ≠ 0 ∧
    C = connectedComponentIn {q : Hyperboloid | lorentzBilinear q.val n ≠ 0} q} =
    {{q : Hyperboloid | 0 < lorentzBilinear q.val n}, {q : Hyperboloid | lorentzBilinear q.val n < 0}} ∧
  Disjoint {q : Hyperboloid | 0 < lorentzBilinear q.val n} {q : Hyperboloid | lorentzBilinear q.val n < 0} ∧
  {q : Hyperboloid | 0 < lorentzBilinear q.val n} ≠ {q : Hyperboloid | lorentzBilinear q.val n < 0} := by
  have hpaths := hyperboloid_normal_sides_pathConnected p e n hn hpn hep hen hee
  have hpEq : ∀ q : Hyperboloid, 0 < lorentzBilinear q.val n →
      connectedComponentIn {q : Hyperboloid | lorentzBilinear q.val n ≠ 0} q =
        {q : Hyperboloid | 0 < lorentzBilinear q.val n} := by
    intro q hq
    apply Set.Subset.antisymm
    · rcases hyperboloid_normal_sign_on_preconnected p e n hn hpn hep hen hee _
        isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) with hp | hm
      · exact hp
      · exact False.elim ((not_lt_of_gt hq) (hm (mem_connectedComponentIn (ne_of_gt hq))))
    · exact hpaths.1.isConnected.isPreconnected.subset_connectedComponentIn hq
        (fun _ hz => ne_of_gt hz)
  have hmEq : ∀ q : Hyperboloid, lorentzBilinear q.val n < 0 →
      connectedComponentIn {q : Hyperboloid | lorentzBilinear q.val n ≠ 0} q =
        {q : Hyperboloid | lorentzBilinear q.val n < 0} := by
    intro q hq
    apply Set.Subset.antisymm
    · rcases hyperboloid_normal_sign_on_preconnected p e n hn hpn hep hen hee _
        isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) with hp | hm
      · exact False.elim ((not_lt_of_gt hq) (hp (mem_connectedComponentIn (ne_of_lt hq))))
      · exact hm
    · exact hpaths.2.isConnected.isPreconnected.subset_connectedComponentIn hq
        (fun _ hz => ne_of_lt hz)
  refine ⟨hpEq, hmEq, ?_, ?_, ?_⟩
  · ext C
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases lt_or_gt_of_ne hq with hm | hp
      · exact Or.inr (hmEq q hm)
      · exact Or.inl (hpEq q hp)
    · intro hC
      rcases hC with hC | hC
      · subst C
        obtain ⟨q, hq⟩ := hpaths.1.nonempty
        exact ⟨q, ne_of_gt hq, (hpEq q hq).symm⟩
      · subst C
        obtain ⟨q, hq⟩ := hpaths.2.nonempty
        exact ⟨q, ne_of_lt hq, (hmEq q hq).symm⟩
  · exact Set.disjoint_left.mpr (fun q hp hm =>
      (not_lt_of_gt (show 0 < lorentzBilinear q.val n from hp)) hm)
  · intro hsets
    obtain ⟨q, hq⟩ := hpaths.1.nonempty
    have hm : q ∈ {q : Hyperboloid | lorentzBilinear q.val n < 0} := hsets ▸ hq
    exact (not_lt_of_gt (show 0 < lorentzBilinear q.val n from hq)) hm

end Hyperbolic
