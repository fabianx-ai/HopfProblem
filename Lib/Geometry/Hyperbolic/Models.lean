module

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


end Hyperbolic
